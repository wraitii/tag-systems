"""Verify a guard-selected instruction sequence in the six-cell clock-49 layout."""

from five_symbol_dispatch import trace


# Each header is (number of low bits, low-bit value), least significant first.
BRANCH = (18, 180568)
BYTE = (8, 255)
BODY = (15, 22655)
RESET = (19, 279519)
RAISE = (9, 269)
SENSE = (16, 65267)
SKIP = (23, 4240311)
OPTIONAL = (15, 16563)


def prepend(header, tail):
    bits, digit = header
    return (tail << bits) + digit


def dispatch(header, guard, data, tail, rounds, output, next_guard, change, *, data_events=0):
    bits, digit = header
    result = trace(1 << bits, digit, {2: guard, 5: data}, rounds, physical_tail=tail)
    assert result is not None
    elapsed, tape, regs, _, fired = result
    assert elapsed == rounds and tape == output
    assert regs == {0: 0, 2: next_guard, 5: data + change}
    assert sum(j == 5 for _, j in fired) == data_events
    return (tape[0] * tail + tape[1]) // 4 - 1, next_guard, data + change


def run_branch(guard, data, tail):
    if guard == 7:
        stream, guard, data = dispatch(BRANCH, guard, data, tail, 184, (4, 4), 2, 12)
    else:
        assert guard == 25
        stream, guard, data = dispatch(BRANCH, guard, data, tail, 129,
                                       (33554432, 23199744), 2, -1)
        body = prepend(BODY, tail)
        assert stream == prepend(BYTE, body)
        stream, guard, data = dispatch(BYTE, guard, data, body, 58, (4, 4), 5, 6)
        assert stream == body
        stream, guard, data = dispatch(BODY, guard, data, tail, 81, (4, 4), 2, -1)
    assert stream == tail
    return stream, guard, data


def run_zero_test(value, continuation):
    """Zero skips OPTIONAL; every positive value executes it. Same initial Z=7."""
    data = 2 + 4 * value
    after_raises = prepend(SKIP, continuation)
    after_sense = prepend(RAISE, prepend(RAISE, after_raises))
    if value == 0:
        stream, z, data = dispatch(SENSE, 7, data, after_sense, 84, (4, 4), 7, 2, data_events=2)
    else:
        stream, z, data = dispatch(SENSE, 7, data, after_sense, 166, (4, 4), 10, 6)
    for _ in range(2):
        tail, digit = divmod(stream, 1 << RAISE[0])
        assert digit == RAISE[1]
        stream, z, data = dispatch(RAISE, z, data, tail, 55, (4, 4), z + 3, 5)
    assert stream == after_raises
    if z == 13:
        return dispatch(SKIP, z, data, continuation, 145, (4, 4), 16, 15)
    assert z == 16
    stream, z, data = dispatch(SKIP, z, data, continuation, 160, (131072, 66256), 10, 8)
    assert stream == prepend(OPTIONAL, continuation)
    return dispatch(OPTIONAL, z, data, continuation, 73, (4, 4), 11, 11)


def check():
    for original in (7, 25):
        for tail in (0, 1, 69):
            # All shallow checks start at the least certified data exponent.
            pending = prepend(RESET, tail)
            stream, guard, data = run_branch(original, 3, pending)
            assert stream == pending and guard == 2
            stream, guard, data = dispatch(RESET, guard, data, tail, 109, (4, 4), 7, -1)
            assert (stream, data) == (tail, 3 + (11 if original == 7 else 3))

    # Compose both choices without editing a queue between instructions.
    # A direct branch is followed by a reset, six raises and an indirect branch.
    tail = 0
    indirect = prepend(BRANCH, tail)
    pending = indirect
    for _ in range(6):
        pending = prepend(RAISE, pending)
    after_reset = pending
    pending = prepend(RESET, pending)
    stream, z, d = run_branch(7, 3, pending)
    assert stream == prepend(RESET, after_reset)
    stream, z, d = dispatch(RESET, z, d, after_reset, 109, (4, 4), 7, -1)
    for _ in range(6):
        remainder, digit = divmod(stream, 1 << RAISE[0])
        assert digit == RAISE[1]
        stream, z, d = dispatch(RAISE, z, d, remainder, 55, (4, 4), z + 3, 5)
    assert stream == indirect and z == 25
    assert run_branch(z, d, tail) == (tail, 2, 48)
    for value in (0, 1, 2, 9):
        for tail in (0, 69):
            following = prepend(RAISE, tail)
            stream, z, data = run_zero_test(value, following)
            expected = (16, 29) if value == 0 else (11, 37 + 4 * value)
            assert (stream, z, data) == (following, *expected)
            assert dispatch(RAISE, z, data, tail, 55, (4, 4), z + 3, 5)[0] == tail
    print("Verified the generated instruction sequence, the live zero-test skip, and dispatch after both joins.")


if __name__ == "__main__":
    check()
