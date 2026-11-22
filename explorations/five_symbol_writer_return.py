"""Symbolic whole-queue returns for the five-symbol writer. Run with python3 -B."""
from collections import deque

from five_symbol_writer import CELL, UNIT, WRITER, RULES


# Each multiplicity is c + u*x + v*y, for independent x,y >= 0.
def affine(value):
    return (value, 0, 0) if isinstance(value, int) else value


def word(*runs):
    return [(tile, affine(n)) for tile, n in runs if any(affine(n))]


def dispatch(data, tape):
    return 0, word((CELL, 1), (CELL, 1), (WRITER, 1), (UNIT, 7),
                   ("b", 2), (UNIT, data), (CELL, 1), (UNIT, tape))


def sweep(state):
    lane, runs = state
    output = []

    def emit(tile, count):
        count = affine(count)
        if not any(count):
            return
        if tile in (UNIT, "b") and output and output[-1][0] == tile:
            count = tuple(a + b for a, b in zip(output.pop()[1], count))
        output.append((tile, count))

    for tile, count in runs:
        c, u, v = count
        assert min(count) >= 0
        if tile in (CELL, WRITER):
            assert count == (1, 0, 0)
            emit(tile, 1)
            if tile == CELL:
                lane ^= 1
            else:
                emit(UNIT, lane)
        elif tile == UNIT:
            factor = 1 if lane else 4
            emit("b", tuple(factor * a for a in count))
        else:
            assert tile == "b" and u % 2 == v % 2 == 0
            emit(UNIT, ((c + 1 - lane) // 2, u // 2, v // 2))
            lane ^= c % 2
    return lane, output


def expand(state, x, y):
    lane, runs = state
    return "".join(tile * (c + u*x + v*y) for tile, (c, u, v) in runs)[lane:]


def verify(start, rounds, end, literal_at=None):
    state = start
    if literal_at is not None:
        queue = deque(expand(start, *literal_at))
    for _ in range(2 * rounds):
        state = sweep(state)
        if literal_at is not None:
            for _ in range((len(queue) + 1) // 2):
                head = queue.popleft()
                queue.popleft()
                queue.extend(RULES[head])
            assert "".join(queue) == expand(state, *literal_at)
    assert state == end, (state, end)


def check():
    # The symbolic lane rules are direct slices of the actual appendants.
    for tile, lanes in ((CELL, (CELL, CELL)), (WRITER, (WRITER, WRITER + UNIT)),
                        (UNIT, ("bbbb", "b")), ("b", (UNIT, ""))):
        assert tuple("".join(RULES[ch] for ch in tile[p::2]) for p in (0, 1)) == lanes

    data = (0, 4, 0)
    verify(dispatch(data, (0, 0, 2)), 7,
           dispatch((16, 8, 0), (0, 0, 1)), (1, 0))
    verify(dispatch(data, (1, 0, 8)), 11,
           dispatch((28, 32, 0), (0, 0, 1)), (1, 1))

    # Execute the identical 15-bit field on two classes of written data.
    field = (731, 0, 32768)
    verify(dispatch((96, 128, 0), field), 47,
           dispatch((524, 256, 0), (364, 0, 16384)), (0, 0))
    verify(dispatch((12, 16, 0), field), 65,
           dispatch((224, 524288, 0), (0, 0, 1)), (0, 0))

    # The longer arm executes the rest of the field and rejoins the same tail.
    verify(dispatch((524, 256, 0), (364, 0, 16384)), 168,
           dispatch((9574736, 4194304, 0), (0, 0, 1)))

    # Width four, source 2, blank output and an arbitrary continuation.
    initial = 0, word((CELL, 1), (UNIT, 14), (CELL, 1), (WRITER, 1),
                      (CELL, 1), (UNIT, (2, 0, 32)))
    verify(initial, 10, dispatch(12, (0, 0, 2)), (0, 1))
    verify(dispatch(12, (0, 0, 2)), 7, dispatch(40, (0, 0, 1)), (0, 1))
    print("Verified blank-output entry, both write instructions and both data-dependent returns.")


if __name__ == "__main__":
    check()
