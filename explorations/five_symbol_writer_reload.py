"""Certificates for two autonomous instruction reloads in the five-symbol writer."""
from collections import deque

from four_symbol_loop import digit

from five_symbol_writer_return import CELL, WRITER, UNIT, RULES, expand, sweep, word


def boundary(bank, data, control):
    return 1, word((CELL, 1), (WRITER, 1), *bank, (CELL, 1), (WRITER, 1),
                   (UNIT, 1), ("b", 3), (UNIT, data), ("b", control))


def sweeps(state, count, literal=False):
    if literal:
        queue = deque(expand(state, 0, 0))
    for _ in range(count):
        state = sweep(state)
        if literal:
            for _ in range((len(queue) + 1) // 2):
                head = queue.popleft()
                queue.popleft()
                queue.extend(RULES[head])
            assert "".join(queue) == expand(state, 0, 0)
    return state


def pairs(*counts):
    return [(tile, n) for a, b in counts for tile, n in ((UNIT, a), ("b", b))]


RECORD = pairs((2, 4))
FIRST_BANK = pairs((10, 72), (36, 512), (16, 2048), (448, 90112))
THREE_RECORDS = pairs((2, 4), (8, 16), (32, 64))
SECOND_BANK = pairs((2, 12), (8, 57880), (4, 16384), (4, 131072),
                    (32, 524288), (128, 2097152)) + [(UNIT, 512)]


def check():
    # x and y are independent nonnegative integers in the inherited affine model.
    assert sweeps(boundary([], (0, 1, 0), (1, 0, 4)), 8) == boundary(
        RECORD, (1, 4, 0), (1, 0, 1))
    # Invisible inserted pair: every intermediate b slope is even.
    bank = pairs(((0, 1, 0), (0, 0, 2)))
    assert sweeps(boundary(bank, 1, 1), 8) == boundary(
        RECORD + pairs(((0, 4, 0), (0, 0, 8))), 5, 1)

    initial = boundary([], (13, 32, 0), 1393)
    after_write = boundary(THREE_RECORDS[:4], (213, 512, 0), 88)
    assert sweeps(initial, 16) == after_write
    assert sweeps(after_write, 55) == boundary(FIRST_BANK, 68, (1, 1, 0))
    assert sweeps(boundary([], 13, 1393), 71, literal=True) == boundary(FIRST_BANK, 68, 1)

    # Follow the original terminal run up to the sweep that deletes it.
    state = initial
    tile, count = "b", 1393
    for tick in range(1, 64):
        phase, runs = state
        assert runs[-1] == (tile, (count, 0, 0))
        lane = phase
        for preceding, (c, u, v) in runs[:-1]:
            assert (len(preceding)*u) % 2 == (len(preceding)*v) % 2 == 0
            lane ^= (len(preceding)*c) % 2
        if tile == "b":
            tile, count = UNIT, (count + 1 - lane) // 2
        else:
            tile, count = "b", count * (1 if lane else 4)
        assert (count == 0) == (tick == 63)
        state = sweep(state)

    assert sweeps(boundary(THREE_RECORDS, (21, 32, 0), 126), 81) == boundary(
        SECOND_BANK, 13, (17, 2, 0))
    bank = THREE_RECORDS + pairs(((0, 64, 0), (0, 0, 64)))
    extra = [("b", (0, 4194304, 0)), (UNIT, (0, 0, 512))]
    assert sweeps(boundary(bank, 21, 126), 81) == boundary(SECOND_BANK + extra, 13, 17)

    # Compare the composed trajectory to the closed form without resetting the queue.
    for h in (3, 4, 8, 31):
        state = sweeps(boundary([], 13 + 32*125*4**h, 1393), 71 + 8*h + 81)
        data = 68*4**h + (4**h - 1)//3
        tape = (data + 251)//16
        remainder = pairs(*[(2*4**j, 4*4**j) for j in range(3, h)])
        remainder += [(tile, n*4**h) for tile, n in FIRST_BANK]
        bank = SECOND_BANK + [("b", n*65536) if tile == UNIT else (UNIT, n*8)
                              for tile, n in remainder]
        assert state == boundary(bank, 13, tape)
        assert tape % 4 == 1
        assert sweeps(state, 8) == boundary(
            RECORD + [(tile, 4*n) for tile, n in bank], 53, (tape+3)//4)
        control = tape
        laps = 0
        while control % 4 == 1:
            control = (control + 3) // 4
            laps += 1
        assert laps == (2 if h == 3 else 1)

    # Independent reader entry: run the generated value through physical dispatcher rounds.
    for h in (5, 6, 8, 12):
        k = h - 2
        for initial in (0, 2, 5):
            exponent, unread, elapsed = initial, (205*4**k + 47)//3, 0
            for _ in range(2*k):
                exponent, unread, duration = digit(exponent, unread)
                elapsed += duration
            assert (exponent, unread) == (initial + 3*k, 68)
            assert elapsed == k*(2*initial + 8) + 3*k*(k-1) - 2
    print("Verified both reloads, follow-on lap counts and the separate binary-reader entry.")


if __name__ == "__main__":
    check()
