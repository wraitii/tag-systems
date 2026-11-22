"""A six-symbol 2-tag interpreter for periodic guarded counter updates.

Run python3 parity_program.py to compare literal tag steps with counter semantics.
The interpreter has persistent program cells. Its observable is reachability.
"""
from collections import deque
import re

INTEGRATOR = "ezII"
DIFFERENTIATOR = "DDez"
COUNTER = "aaaeaeae"
RULES = dict(I=INTEGRATOR, D=DIFFERENTIATOR, z="e", e="", a="b", b=COUNTER)


def integrator_program(mask):
    """Encode the integrator states that emit mask on zero input."""
    length = len(mask)
    if not length or length & (length - 1):
        raise ValueError("clock length must be a power of two")
    # Output t is the XOR of the initial states at all bitwise supersets
    # of t. The superset transform is its own inverse over the binary field.
    seed = list(mask)
    stride = 1
    while stride < length:
        for i in range(length):
            if not i & stride:
                seed[i] ^= seed[i | stride]
        stride *= 2
    return "".join(("e" if bit else "") + INTEGRATOR for bit in seed)


def clock(mask):
    """Encode a periodic mask that composes by XOR with any input."""
    return DIFFERENTIATOR * len(mask) + integrator_program(mask)


def guarded(test, changes):
    """If counter test is zero, add changes[j] in {-1,0,+1} to counter j."""
    if changes[test] or any(abs(v) > 1 for v in changes):
        raise ValueError("invalid conditional update")
    rows = []

    def emit(test_sign, other_signs, return_probe=False):
        signs = list(other_signs)
        signs[test] = test_sign
        parity_mask = [0] * len(changes)
        parity_mask[test] = int(return_probe)
        rows.append(([int(s < 0) for s in signs], parity_mask))

    for s in [1, -1] * 2:
        emit(-1, [s] * len(changes))
    for default in [1, -1]:
        signs = [v or default for v in changes]
        emit(-1, signs)
        emit(1, [-s for s in signs], return_probe=True)
    for s in [1, -1] * 2:
        emit(1, [s] * len(changes))
    return rows


def reversible_machine(states, initial_state, data, edges):
    """Compile Morita-style edges (source, op, data index, destination).

    The caller supplies a deterministic, backward-deterministic machine.
    Z/P test zero/positive, +/- change a register, and N does nothing.
    A decrement requires a positive operand. Stop decoding on entry
    to a source halt state. The physical queue continues to run.
    """
    pc = {state: len(data) + i for i, state in enumerate(states)}
    latch = len(data) + len(states)
    constant = latch + len(edges)
    values = list(data) + [int(state != initial_state) for state in states]
    values += [1] * len(edges) + [0]
    rows = []

    def add(control, updates):
        delta = [0] * len(values)
        for index, amount in updates:
            delta[index] += amount
        if any(delta):
            rows.extend(guarded(control, delta))

    def select(state, op, x, index, amount):
        # Temporarily add one mismatch bit to the inactive-state flag.
        if op == "Z":
            add(constant, [(state, 1)])
            add(x, [(state, -1)])
        elif op == "P":
            add(x, [(state, 1)])
        add(state, [(index, amount)])
        if op == "Z":
            add(x, [(state, 1)])
            add(constant, [(state, -1)])
        elif op == "P":
            add(x, [(state, -1)])

    for i, (src, op, x, dst) in enumerate(edges):
        if op not in ("Z", "P", "+", "-", "N"):
            raise ValueError("unknown transition")
        select(pc[src], "P" if op == "-" else op, x, latch + i, -1)
    for i, (src, op, x, dst) in enumerate(edges):
        updates = [(pc[src], 1), (pc[dst], -1)]
        if op in ("+", "-"):
            updates.append((x, 1 if op == "+" else -1))
        add(latch + i, updates)
    for i, (src, op, x, dst) in enumerate(edges):
        select(pc[dst], "P" if op == "+" else op, x, latch + i, 1)
    return rows, values


def bouncing_machine(states, start, halt, data, edges):
    """Compile halt to eventual periodicity. Reachable live states must have
    one successor, the start has no incoming edge, and halt has no outgoing
    edge. Use a distinct entry and halting state.
    """
    if start == halt or any(dst == start or src == halt for src, _, _, dst in edges):
        raise ValueError("bounce requires a fresh entry and terminal halt")
    labels = [(direction, q) for direction in (1, -1) for q in states]
    forward = [((1, src), op, x, (1, dst)) for src, op, x, dst in edges]
    inverse = {"+": "-", "-": "+", "Z": "Z", "P": "P", "N": "N"}
    backward = [((-1, dst), inverse[op], x, (-1, src))
                for src, op, x, dst in edges]
    turns = [((1, halt), "N", 0, (-1, halt)),
             ((-1, start), "N", 0, (1, start))]
    return reversible_machine(labels, (1, start), data, forward + backward + turns)


def monitored_machine(states, initial_state, halt_state, data, edges):
    """Return the periodic program, initial registers, and H-monitor index."""
    rows, values = reversible_machine(states, initial_state, data, edges)
    halt_flag = len(data) + states.index(halt_state)
    probe = guarded(halt_flag, [0] * len(values))
    # Probe at the start of each period, including before the first transition.
    first_return = next(i for i, (_, mask) in enumerate(probe) if any(mask))
    return probe + rows, values, first_return


def compile_program(rows, values, halt_probe=None, *, encode_clock=clock):
    count = len(values)
    commands = list(rows)
    if not commands or len(commands) % 2:
        raise ValueError("expected a nonempty even number of commands")
    period = 1 << (2 * len(commands) - 1).bit_length()
    while 2 * len(commands) < period:
        for bit in (0, 1):
            commands.append(([bit] * count, [0] * count))
    masks = [[] for _ in range(count + 1)]
    for pair in commands:
        for desired in pair:
            previous = 0
            for mask, bit in zip(masks, desired):
                mask.append(previous ^ bit)
                previous = bit
            masks[-1].append(previous)
    parts = []
    if halt_probe is not None:
        if not 0 <= halt_probe < len(rows) or not any(rows[halt_probe][1]):
            raise ValueError("halt_probe must index a return probe")
        monitor_mask = []
        for index, (_, parity_mask) in enumerate(commands):
            monitor_mask.extend([0, int(any(parity_mask) and index != halt_probe)])
        parts.extend([encode_clock(monitor_mask), "MN"])
        masks[0] = [a ^ b for a, b in zip(masks[0], monitor_mask)]
    for mask, value in zip(masks, values):
        parts.extend([encode_clock(mask), COUNTER * (1 << (4 + 4 * value))])
    parts.append(encode_clock(masks[-1]))
    return "".join(parts), commands


FIVE_RULES = {symbol: appendant for symbol, appendant in RULES.items() if symbol != "D"}


def compile_five_program(rows, values, horizon):
    """Use integrators alone. Agreement is guaranteed for horizon sweeps."""
    if horizon < 1:
        raise ValueError("horizon must be positive")

    def finite_clock(mask):
        length = 1 << (max(len(mask), horizon) - 1).bit_length()
        repeated = mask * (length // len(mask))
        return integrator_program(repeated)

    return compile_program(rows, values, encode_clock=finite_clock)


def verify(rows, values, expected, periods):
    initial, commands = compile_program(rows, values)
    queue = deque(initial)
    phase = 0
    exponents = [4 + 4 * v for v in values]
    steps = 0
    for iteration in range(periods):
        for signs, _ in commands:
            # Independent counter calculation, including reflection at zero.
            attempted = [v + (-1 if bit ^ phase else 1)
                         for v, bit in zip(exponents, signs)]
            hits = [i for i, v in enumerate(attempted) if v < 0]
            assert len(hits) <= 1
            phase ^= len(hits)
            exponents = [max(0, v) for v in attempted]
            # Physical queue already lacks the first letter on an odd entry.
            for _ in range(2):
                size = len(queue)
                assert size >= 2
                steps += (size + 1) // 2
                for _ in range((size + 1) // 2):
                    assert len(queue) >= 2
                    first = queue.popleft()
                    queue.popleft()
                    queue.extend(RULES[first])
                offset = size % 2
            assert offset == phase
            # The phase-crossing deletion is in the leading clock.
            word = "".join(queue)
            blocks = re.findall(f"(?:{COUNTER})+", word)
            assert [len(b) // len(COUNTER) for b in blocks] == [1 << v for v in exponents]
        assert phase == 0
        want = expected(iteration + 1)
        assert exponents == [4 + 4 * v for v in want]
    return steps


MONITORED_RULES = dict(RULES, M="MN", N="MH", H="H")


def first_halt_read(rows, values, halt_probe, periods):
    """Report (sweep, steps) on reading H, or (None, steps) at the limit."""
    word, commands = compile_program(rows, values, halt_probe)
    queue = deque(word)
    steps = 0
    for sweep in range(2 * len(commands) * periods):
        for _ in range((len(queue) + 1) // 2):
            first = queue.popleft()
            if first == "H":
                return sweep, steps
            queue.popleft()
            queue.extend(MONITORED_RULES[first])
            steps += 1
    return None, steps


def check_five_symbol_horizons():
    """Check physical counter blocks and the first divergent command."""
    rows = guarded(0, [0, 1])
    for horizon in (1, 32, 57, 128):
        for x in (0, 1):
            five, commands = compile_five_program(rows, [x, 0], horizon)
            six, _ = compile_program(rows, [x, 0])
            assert set(five) <= FIVE_RULES.keys()
            five_table = str.maketrans(FIVE_RULES)
            six_table = str.maketrans(RULES)
            length = 1 << (max(2 * len(commands), horizon) - 1).bit_length()
            for sweep in range(1, length + 3):
                five = five[::2].translate(five_table)[len(five) % 2:]
                six = six[::2].translate(six_table)[len(six) % 2:]
                pattern = r"b+" if sweep % 2 else f"(?:{COUNTER})+"
                old = re.findall(pattern, six)
                new = re.findall(pattern, five)
                if sweep <= length:
                    assert old == new
                if length == 32 and sweep == 34:
                    sizes = [[len(run) // len(COUNTER) for run in runs]
                             for runs in (old, new)]
                    assert sizes == ([[8, 512], [8, 128]] if x == 0
                                     else [[128, 32], [128, 8]])
    print("Checked the five-symbol horizon and its first divergent command.")


if __name__ == "__main__":
    check_five_symbol_horizons()
    total = 0
    for x in range(2):
        total += verify(guarded(0, [0, 1]), [x, 0],
                        lambda n: [x, n if x == 0 else 0], 2)
        total += verify(guarded(1, [-1, 0]), [2, x],
                        lambda n: [2 - n if x == 0 else 2, x], 2)
    # Alternate tested registers and use the newly written value immediately.
    total += verify(guarded(0, [0, 1]) + guarded(1, [1, 0]),
                    [0, 0], lambda n: [0, n], 2)
    for x in (0, 1):
        rows, values = reversible_machine(
            ["start", "joined", "halt"], "start", [x],
            [("start", "Z", 0, "joined"), ("start", "P", 0, "joined"),
             ("joined", "+", 0, "halt")])
        def snapshot(period):
            return [x + int(period == 2), 1, int(period != 1),
                    int(period != 2), 1, 1, 1, 0]
        total += verify(rows, values, snapshot, 2)
    rows = guarded(0, [0, 0]) + guarded(1, [0, 0])
    for x in (0, 1):
        for y in (0, 1):
            # Arm only on register 1, on the first of its two return probes.
            sweep, steps = first_halt_read(rows, [x, y], 17, 3)
            assert sweep == (35 if y == 0 else None)
            total += steps
    examples = [
        ("start", [("start", "N", 0, "halt")], 1),
        ("halt", [("start", "N", 0, "halt")], 0),
        ("start", [("start", "N", 0, "start")], None),
    ]
    for state, edges, halt_period in examples:
        rows, values, probe = monitored_machine(
            ["start", "halt"], state, "halt", [0], edges)
        period = 1 << (2 * len(rows) - 1).bit_length()
        sweep, steps = first_halt_read(rows, values, probe, 3)
        assert sweep == (None if halt_period is None
                         else period * halt_period + 2 * probe + 1)
        total += steps
    # Compare whole physical queues at period boundaries, including all clocks.
    rows, values = bouncing_machine(["s", "h"], "s", "h", [0],
                                    [("s", "+", 0, "h")])
    word, commands = compile_program(rows, values)
    translations = str.maketrans(RULES)
    seen = {}
    for checkpoint in range(10):
        if word in seen:
            assert checkpoint - seen[word] == 4
            print(f"Identical physical queue at checkpoints {seen[word]} and {checkpoint}.")
            break
        seen[word] = checkpoint
        for _ in range(2 * len(commands)):
            size = len(word)
            total += (size + 1) // 2
            word = word[::2].translate(translations)[size % 2:]
    else:
        raise AssertionError("expected a physical cycle")
    print(f"Verified {total:,} individual 2-tag steps.")
