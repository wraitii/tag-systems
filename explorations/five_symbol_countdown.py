"""A counted addition loop followed by a live second loop in the aaazazae table."""

from collections import deque

from five_symbol_transfer import RULES, UNIT, drop_first, equal_words, physical_sweep


def boundary(clock, counts):
    positions = dict(zip((0, 1, 2, 4), counts))
    word = []
    for j in range(5):
        if j in positions:
            word.append((UNIT, positions[j]))
        word.append(("e" * (clock >> j & 1) + "ezII", 1))
    return drop_first(word) if clock >> 4 else word


def check_path(rows, literal=False):
    queue = None
    for (clock, *counts), (target, *values) in zip(rows, rows[1:]):
        word = boundary(clock, counts)
        expected = boundary(target, values)
        assert equal_words(physical_sweep(physical_sweep(word)), expected)
        if literal:
            if queue is None:
                queue = deque("".join(tile * n for tile, n in word))
            for _ in range(2):
                for _ in range((len(queue) + 1) // 2):
                    head = queue.popleft()
                    queue.popleft()
                    queue.extend(RULES[head])
            assert "".join(queue) == "".join(tile * n for tile, n in expected)


def lap(x, y):
    # x is a multiple of 4, y is any positive integer.
    return [(21, x, y, 1, 1), (20, x//2, 2*y, 2, 1),
            (14, x//4, y, 1, 2), (21, x//2, 2*y, 1, 1)]


def leave(y):
    return [(21, 22, y, 1, 1), (20, 11, 2*y, 2, 1), (17, 5, y, 1, 2),
            (16, 2, 2*y, 2, 4), (5, 1, y, 1, 2)]


def onward(y, z):
    # y must be even. z is any positive integer.
    return [(5, 1, y, 1, z), (29, 2, y//2, 1, 2*z),
            (19, 1, y, 2, 4*z), (5, 1, 2*y, 1, 2*z)]


def check():
    for h in (0, 1, 2, 5, 14, 42):
        for d in (1, 2, 7):
            x, y = 22 << h, 1 << d
            simple = h < 3 and d < 3
            for _ in range(h):
                rows = lap(x, y)
                check_path(rows, simple)
                _, x, y, _, _ = rows[-1]
            assert (x, y) == (22, 1 << (d+h))
            check_path(leave(y), simple)
            z = 2
            for _ in range(3):
                check_path(onward(y, z), simple)
                y, z = 2*y, 2*z
    print("Verified the old-table countdown, its four-round exit and the second recurrent loop.")


if __name__ == "__main__":
    check()
