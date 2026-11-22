"""Two selectable recurrent zero-event routes in one fixed five-symbol 2-tag table.

Cell 0 is the low clock bit. X precedes cell 0 and Y precedes cell 8.
At clock 808, X=0 selects 605 and Y=0 selects 674. The X route returns
to 808 every 37 rounds, adding one to Y. The Y route returns to 674
every 37 rounds, adding five to X. One round is two sweeps.
"""

from collections import deque

UNIT = "azaaazae"
RULES = {"I": "ezII", "z": "e", "e": "", "a": "b", "b": UNIT}
CELLS = 10
COUNTERS = {0: 0, 8: 1}


def boundary(clock, x, y, payload=()):
    chunks = []
    for j in range(CELLS):
        if j in COUNTERS:
            chunks.append(UNIT * (1 << (x, y)[COUNTERS[j]]))
        for position, exponent in payload:
            if j == position:
                chunks.append(UNIT * (1 << exponent))
        chunks.append("e" * ((clock >> j) & 1) + "ezII")
    return "".join(chunks)[clock >> 9:]


def cell(lane, clock, j):
    return lane ^ ((clock >> j) & 1)


def advance(state):
    clock, x, y = state
    exponents = [x, y]
    commands = []
    lane = clock >> 9
    middle = 0
    for j in range(CELLS):
        if j in COUNTERS:
            commands.append(lane)
        lane = cell(lane, clock, j)
        middle |= lane << j

    result = 0
    events = []
    for j in range(CELLS):
        if j in COUNTERS:
            i = COUNTERS[j]
            if commands[i] == 0:
                exponents[i] += 1
            elif exponents[i] > 0:
                exponents[i] -= 1
            else:
                # The odd first-sweep word ebe keeps its b only on lane 1.
                if lane != 1:
                    raise ValueError("Counter block erased")
                events.append(i)
                lane ^= 1
        lane = cell(lane, middle, j)
        result |= lane << j
    return (result, *exponents), events


def verify(start, rounds, guard, expected, event_clocks, drift):
    state = start
    observed = []
    # The two registers before cell 9 store an arbitrary difference.
    # The register before cell 1 lets us also compare the two locations.
    payload = [(1, 5), (9, 1), (9, 3)]
    queue = deque(boundary(*start, payload))
    for _ in range(rounds):
        following, events = advance(state)
        for counter in events:
            assert counter == guard
            observed.append(state[0])
        updated = []
        for position, exponent in payload:
            lane = state[0] >> 9
            for j in range(position):
                lane = cell(lane, state[0], j)
            exponent += 1 if lane == 0 else -1
            assert exponent >= 0  # no attempted decrement at zero
            updated.append((position, exponent))
        payload = updated
        for _ in range(2):
            for _ in range((len(queue) + 1) // 2):
                head = queue.popleft()
                queue.popleft()
                queue.extend(RULES[head])
        assert "".join(queue) == boundary(*following, payload)
        state = following
    assert payload == [(1, 5 + drift[0]), (9, 1 + drift[1]), (9, 3 + drift[1])]
    assert observed == event_clocks and state == expected


def check():
    # At these lowest certified payloads the passive counter never
    # underflows. Increasing it by d translates every passive exponent
    # by d, leaving every lane, event and active exponent unchanged.
    for h in range(3, 7):
        verify((808, 0, h), 1, 0, (605, 0, h - 1), [808], (-1, 1))
        verify((808, 0, h), 37, 0, (808, 0, h + 1), [808, 605, 792], (5, 7))
    for h in range(5, 9):
        verify((808, h, 0), 1, 1, (674, h - 1, 0), [808], (-1, 1))
        verify((674, h - 1, 0), 37, 1, (674, h + 4, 0), [74, 94, 441], (5, 5))
    print("Matched 304 whole-queue round boundaries across both branches.")


if __name__ == "__main__":
    check()
