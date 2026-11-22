"""A universal seven-symbol 2-tag system with literal unary Collatz returns."""

from collections import deque
import re

from parity_program import bouncing_machine, clock, guarded

PAIR = "bc"
TILE = "ababeb"
RULES = {"I": "ezII", "D": "DDez", "z": "e", "e": "",
         "a": PAIR, "b": "a", "c": TILE}

# Programmed lanes at each register, one bit per sweep.
TEST = "0000101000100010"
BEFORE = {2: "1010101001010101", -2: "1010100101100101"}
AFTER = {2: "0110101010010100", -2: "0110100110100100"}
HALVE = "00"
DOUBLE = "10"
IDLE = HALVE + DOUBLE


def guard_masks(test, changes):
    """Sixty-four sweeps for 'if register test is zero, add changes'."""
    if not 0 <= test < len(changes) or changes[test] != 0:
        raise ValueError("the tested register must exist and have delta zero")
    if any(delta not in (-1, 0, 1) for delta in changes):
        raise ValueError("register deltas must be -1, 0 or 1")
    masks = []
    for j, delta in enumerate(changes):
        if j == test:
            masks.append(HALVE * 8 + TEST * 2 + DOUBLE * 8)
        else:
            programs = BEFORE if j < test else AFTER
            first, second = {1: (2, 2), 0: (2, -2), -1: (-2, -2)}[delta]
            masks.append(IDLE * 4 + programs[first] + programs[second] + IDLE * 4)
    return masks


def compile_guards(guards, values):
    """Return a physical starting queue and its power-of-two sweep period."""
    if not guards or not values or any(v < 0 for v in values):
        raise ValueError("expected guards and nonnegative initial registers")
    masks = [""] * len(values)
    for test, changes in guards:
        if len(changes) != len(values):
            raise ValueError("one delta per register is required")
        masks = [old + new for old, new in zip(masks, guard_masks(test, changes))]
    length = len(masks[0])
    period = 1 << (length - 1).bit_length()
    masks = [m + IDLE * ((period - length) // 4) for m in masks]
    previous = "0" * period
    parts = []
    for mask, value in zip(masks, values):
        parts.append(clock([int(a != b) for a, b in zip(previous, mask)]))
        parts.append(PAIR * (1 << (8 + 4 * value)))
        previous = mask
    parts.append(clock(list(map(int, previous))))
    return "".join(parts), period


def bounce_guards(states, start, halt, data, edges):
    """Translate the existing bouncing-machine compiler at guard boundaries."""
    rows, values = bouncing_machine(states, start, halt, data, edges)
    guards = []
    for offset in range(0, len(rows), 12):
        block = rows[offset:offset + 12]
        # Return probe identifies the tested register. The two probe signs
        # encode (+,+), (+,-), or (-,-) for each passive register.
        test = block[5][1].index(1)
        changes = [1 - first - second for first, second in zip(block[4][0], block[6][0])]
        changes[test] = 0
        if block != guarded(test, changes):
            raise ValueError("unrecognized six-symbol guard encoding")
        guards.append((test, changes))
    return guards, values


def literal_sweep(queue):
    for _ in range((len(queue) + 1) // 2):
        head = queue.popleft()
        queue.popleft()
        queue.extend(RULES[head])


def check_probe():
    """Derive both cut histories and verify the dyadic paths symbolically."""
    def next_block(kind, count, lane):
        if kind == PAIR:
            return (TILE if lane else "a"), count
        if kind == "a":
            return PAIR, (count + 1 - lane) // 2
        return ("a", 3 * count) if lane else (PAIR, 2 * count)

    kind, count, cut = PAIR, 1, 0
    before, after = [], []
    for bit in TEST:
        before.append(cut)
        parity = (len(kind) * count) % 2
        kind, count = next_block(kind, count, int(bit) ^ cut)
        cut ^= parity
        after.append(cut)
    assert (kind, count, cut) == (PAIR, 1, 0)

    def dyadic_path(bits, cuts):
        kind, exponent, minimum = PAIR, 0, 0
        for bit, cut in zip(bits, cuts):
            lane = int(bit) ^ cut
            if kind == PAIR:
                kind = TILE if lane else "a"
            elif kind == "a":
                kind, exponent = PAIR, exponent - 1
            else:
                assert lane == 0
                kind, exponent = PAIR, exponent + 1
            minimum = min(minimum, exponent)
        assert kind == PAIR
        return exponent, minimum

    zeros = [0] * len(TEST)
    assert dyadic_path(TEST, zeros) == (0, -2)
    for programs, cuts in [(BEFORE, before), (AFTER, after)]:
        for change, bits in programs.items():
            for history, expected in [(zeros, 0), (cuts, change)]:
                net, minimum = dyadic_path(bits, history)
                assert net == expected and minimum >= -8


def check():
    check_probe()
    for n in range(2, 1001):
        q = deque("a" * n)
        for _ in range(2 + n % 2):
            literal_sweep(q)
        assert "".join(q) == "a" * (n // 2 if n % 2 == 0 else (3 * n + 1) // 2)
    cases = [
        ([(1, [1, 0, -1])], [0, 0, 1], 1),
        ([(1, [-1, 0, 1])], [1, 0, 0], 1),
        ([(1, [0, 0, 0])], [0, 0, 0], 2),
        ([(1, [-1, 0, 1])], [0, 1, 0], 2),
        ([(0, [0, 1]), (1, [-1, 0]), (0, [0, -1])], [0, 1], 2),
    ]
    for guards, initial, periods in cases:
        word, period = compile_guards(guards, initial)
        values = initial.copy()
        q = deque(word)
        for _ in range(periods):
            for test, changes in guards:
                if values[test] == 0:
                    values = [v + d for v, d in zip(values, changes)]
                    assert min(values) >= 0
            for _ in range(period):
                literal_sweep(q)
            runs = re.findall(r"(?:bc)+", "".join(q))
            assert [len(run) // 2 for run in runs] == [1 << (8 + 4*v) for v in values]
    guards, registers = bounce_guards(["s", "h"], "s", "h", [0], [("s", "+", 0, "h")])
    checkpoints = []
    for _ in range(5):
        for test, changes in guards:
            if registers[test] == 0:
                registers = [v + d for v, d in zip(registers, changes)]
                assert min(registers) >= 0
        checkpoints.append(registers.copy())
    assert [registers[0] for registers in checkpoints] == [1, 1, 0, 0, 1]
    assert checkpoints[0] == checkpoints[4]
    print("Verified unary returns 2..1000, symbolic probe paths, and literal guarded programs.")


if __name__ == "__main__":
    check()
