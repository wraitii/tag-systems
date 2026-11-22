"""Autonomous shuttle and binary dispatch in a fixed four-symbol 2-tag system."""

from collections import deque

from five_symbol_transfer import drop_first, equal_words, physical_sweep

UNIT = "aaaeaeae"
CELL = "IIe"
RULES = {"I": CELL, "e": "", "a": "b", "b": UNIT}


def boundary(phase, counts):
    """Each run precedes one clock cell. Zero copies is an empty run."""
    word = []
    for count in counts:
        if count:
            word.append((UNIT, count))
        word.append((CELL, 1))
    return drop_first(word) if phase else word


def advance(phase, counts):
    """One two-sweep round, including simultaneous odd runs and empty slots."""
    odd_seen = 0
    result = []
    for j, count in enumerate(counts):
        first_lane = phase ^ (j % 2)
        if first_lane == 0:
            result.append(2 * count)
        else:
            # Sparse lane on sweep two reads the first b iff this bit is 1.
            round_up = (len(counts) % 2) ^ odd_seen
            result.append((count + round_up) // 2)
            odd_seen ^= count % 2
    return phase ^ odd_seen, tuple(result)


def verified_round(phase, counts, literal=False):
    word = boundary(phase, counts)
    successor = advance(phase, counts)
    expected = boundary(*successor)
    mid = physical_sweep(word, RULES)
    assert equal_words(physical_sweep(mid, RULES), expected)
    if literal:
        queue = deque("".join(tile * count for tile, count in word))
        for _ in range(2):
            for _ in range((len(queue) + 1) // 2):
                head = queue.popleft()
                queue.popleft()
                queue.extend(RULES[head])
        assert "".join(queue) == "".join(tile * count for tile, count in expected)
    return successor


def digit(b, tape, literal=False):
    """First return to phase 1 with one A unit, including the empty-tape shuttle."""
    state = (1, (1, 1 << b, tape))
    odd = tape % 2
    rounds = 1 if odd else 2 * b + 5
    for step in range(1, rounds + 1):
        state = verified_round(*state, literal=literal)
        if state[0] == 1 and state[1][0] == 1:
            assert step == rounds
    assert state == (1, (1, 1 << (b + 2 - odd), tape // 2))
    return b + 2 - odd, tape // 2, rounds


def check():
    for phase in (0, 1):
        for a in range(5):
            for b in range(5):
                for tape in range(5):
                    verified_round(phase, (a, b, tape), literal=True)
    for b in (0, 1, 2, 5, 20):
        for tape in (0, 1, 2, 3, 10, 17, 1024, 65535):
            digit(b, tape, literal=(b <= 2 and tape < 20))
    for initial in (1, 2, 11, 32, 173, 4095):
        b, tape = 0, initial
        while tape:
            b, tape, _ = digit(b, tape)
        assert b == 2 * initial.bit_length() - initial.bit_count()
        for _ in range(3):
            b, tape, _ = digit(b, tape)
    for h in range(10):
        start = 2
        b, tape, elapsed = start, 1 << h, 0
        for _ in range(h):
            b, tape, rounds = digit(b, tape)
            elapsed += rounds
        assert (b, tape, elapsed) == (start + 2*h, 1, h * (2*start + 2*h + 3))
    # Two cells select floor rounding at a solitary odd run.
    for initial in range(1, 65):
        phase, counts = 1, (initial, 0)
        while phase:
            phase, counts = verified_round(phase, counts, literal=True)
        if initial & (initial - 1) == 0:
            assert counts == (0, 0)
            assert verified_round(0, counts, literal=True) == (0, counts)
        else:
            assert counts[0] > 0
            assert verified_round(0, counts, literal=True) == (0, (2 * counts[0], 0))
    print("Verified the four-symbol dispatcher, nested countdown, shuttle, and exact-cycle predicate.")


if __name__ == "__main__":
    check()
