"""Certificates for a five-symbol arithmetic return and an exact mixed-guard cycle."""

from collections import deque
from math import lcm

UNIT = "aaazazae"
RULES = {"I": "ezII", "z": "e", "e": "", "a": "b", "b": UNIT}


def sweep_clock(n, clock):
    lane = clock >> (n - 1)
    successor = lanes = 0
    for j in range(n):
        lanes |= lane << j
        lane ^= (clock >> j) & 1
        successor |= lane << j
    return successor, lanes


def advance(n, positions, state):
    clock, *values = state
    middle, commands = sweep_clock(n, clock)
    successor, reads = sweep_clock(n, middle)
    flip = 0
    events = []
    for i, j in enumerate(positions):
        if values[i] is None:
            continue
        if not (commands >> j & 1):
            values[i] += 1
        elif values[i]:
            values[i] -= 1
        else:
            # The single bee block regenerates UNIT on lane 0.
            if ((reads >> j & 1) ^ flip) == 0:
                events.append(i)
            else:
                values[i] = None
            flip ^= 1
            successor ^= (1 << n) - (1 << j)
    return (successor, *values), events


def normal_segment(clock, length):
    delta = [0, 0]
    minimum = [0, 0]
    for _ in range(length):
        middle, commands = sweep_clock(6, clock)
        clock, _ = sweep_clock(6, middle)
        for i in range(2):
            delta[i] += -1 if commands >> i & 1 else 1
            minimum[i] = min(minimum[i], delta[i])
    return clock, tuple(delta), tuple(minimum)


# Physical words are concatenations of (literal tile, repetition count).
def drop_first(word):
    tile, count = word[0]
    first = [(tile[1:], 1)] if len(tile) > 1 else []
    rest = [(tile, count - 1)] if count > 1 else []
    return first + rest + word[1:]


def boundary(n, positions, state):
    clock, *values = state
    counters = dict(zip(positions, values))
    word = []
    for j in range(n):
        if counters.get(j) is not None:
            word.append((UNIT, 1 << counters[j]))
        word.append(("e" * ((clock >> j) & 1) + "ezII", 1))
    return drop_first(word) if clock >> (n - 1) else word


def physical_sweep(word, rules=RULES):
    lane = 0
    output = []
    for tile, count in word:
        # A pair of tiles always has even width, including odd-width tiles.
        pairs, tail = divmod(count, 2)
        for block, copies in ((tile * 2, pairs), (tile, tail)):
            if copies:
                emitted = "".join(rules[letter] for letter in block[lane::2])
                if emitted:
                    output.append((emitted, copies))
        lane ^= len(tile) * count & 1
    return drop_first(output) if lane else output


def equal_words(left, right):
    # Compare literal letters over one common tile period per overlap.
    li = ri = lo = ro = 0
    while li < len(left) and ri < len(right):
        a, ac = left[li]
        b, bc = right[ri]
        alen, blen = len(a) * ac, len(b) * bc
        size = min(alen - lo, blen - ro)
        for j in range(min(size, lcm(len(a), len(b)))):
            if a[(lo + j) % len(a)] != b[(ro + j) % len(b)]:
                return False
        lo += size
        ro += size
        if lo == alen:
            li += 1
            lo = 0
        if ro == blen:
            ri += 1
            ro = 0
    return li == len(left) and ri == len(right)


def verify_path(n, positions, start, length, literal=False):
    state = start
    events = []
    for _ in range(length):
        word = boundary(n, positions, state)
        successor, fired = advance(n, positions, state)
        events.extend((state[0], i) for i in fired)
        expected = boundary(n, positions, successor)
        assert equal_words(physical_sweep(physical_sweep(word)), expected)
        if literal:
            queue = deque("".join(tile * count for tile, count in word))
            for _ in range(2):
                for _ in range((len(queue) + 1) // 2):
                    head = queue.popleft()
                    queue.popleft()
                    queue.extend(RULES[head])
            assert "".join(queue) == "".join(tile * count for tile, count in expected)
        state = successor
    return state, events


def check():
    for clock, length, result, delta, minimum in [
        (15, 21, 15, (5, -3), (0, -6)),
        (15, 12, 1, (6, -4), (0, -4)),
        (20, 16, 34, (-2, 0), (-2, 0)),
        (30, 21, 30, (-3, 5), (-5, 0)),
        (30, 6, 49, (-2, 2), (-2, 0)),
    ]:
        assert normal_segment(clock, length) == (result, delta, minimum)
    for k in (1, 2, 3, 4, 8, 9):
        end, events = verify_path(6, (0, 1), (49, 0, 9*k), 168*k - 5)
        assert end == (49, 0, 25*k - 3)
        assert events == [(49, 0), (1, 1), (34, 1)]
    verify_path(6, (0, 1), (49, 0, 9), 15, literal=True)
    end, events = verify_path(5, (0, 2), (5, 0, 0), 3, literal=True)
    assert end == (5, 0, 0) and events == [(5, 1), (19, 0)]
    for start, rounds, expected in [
        ((49, 0, 9), 545, (36, None, None)),
        ((36, None, None), 21, (36, None, None)),
        ((49, 0, 18), 659, (63, 81, None)),
        ((63, 81, None), 21, (63, 86, None)),
    ]:
        end, _ = verify_path(6, (0, 1), start, rounds)
        assert end == expected
    clock, delta, minimum = normal_segment(63, 21)
    assert (clock, delta[0], minimum[0]) == (63, 5, -1)
    print("Verified six arithmetic returns, the mixed-guard cycle, the clock-only cycle, and the growth certificate.")


if __name__ == "__main__":
    check()
