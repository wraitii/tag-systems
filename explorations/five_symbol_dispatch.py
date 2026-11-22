"""Residue dispatch using the original clock-49 layout and arbitrary UNIT counts.

Run with python3 -B five_symbol_dispatch.py. The symbolic checks run on an
entire residue class at once. The physical checks use literal production tiles.
"""

from five_symbol_transfer import advance, normal_segment, UNIT, drop_first, equal_words, physical_sweep, sweep_clock


def boundary(clock, counts):
    blocks = []
    for j in range(6):
        if j in counts:
            assert counts[j] > 0
            blocks.append((UNIT, counts[j]))
        blocks.append(("e" * (clock >> j & 1) + "ezII", 1))
    return drop_first(blocks) if clock >> 5 else blocks


def trace(radix, digit, guards, limit, *, physical_tail=None):
    """Start with tape size 4*(radix*k + digit + 1), k arbitrary and nonnegative.

    The X exponent starts at zero. Each other guard starts at the supplied
    exponent. Track the tape count as a*k+b. Return on the first live re-entry.
    """
    a, b = 4 * radix, 4 * (digit + 1)
    exponents = {0: 0, **guards}
    clock = 49
    fired = []
    minima = exponents.copy()

    def word():
        counts = {j: 1 << h for j, h in exponents.items()}
        counts[1] = a * physical_tail + b
        return boundary(clock, counts)

    for t in range(1, limit + 1):
        if physical_tail is not None:
            before = word()
        middle, commands = sweep_clock(6, clock)
        successor, reads = sweep_clock(6, middle)
        flip = 0
        for j in range(6):
            decrement = (commands >> j) & 1
            lane = ((reads >> j) & 1) ^ flip
            if j == 1:
                if not decrement:
                    a, b = 2 * a, 2 * b
                    continue
                if a % 2:
                    return None  # Different tails take different paths.
                odd = b % 2
                a, b = a // 2, (b + odd * (1 - 2 * lane)) // 2
                if b == 0:
                    return None  # The zero tail would lose this block.
            elif j in exponents:
                h = exponents[j]
                odd = decrement and h == 0
                if odd:
                    if lane:
                        return None
                    fired.append((t, j))
                else:
                    exponents[j] += -1 if decrement else 1
                    minima[j] = min(minima[j], exponents[j])
            else:
                continue
            if odd:
                flip ^= 1
                successor ^= 64 - (1 << j)
        clock = successor
        if physical_tail is not None:
            assert equal_words(physical_sweep(physical_sweep(before)), word())
        if clock == 49 and exponents[0] == 0:
            return t, (a, b), exponents, minima, fired
    return None


def check_power_exits():
    # For h=9+r+9u track each exponent as base + slope*u. Insert 3u laps
    # at 15 and, if reached after the Y event at 34, another 5u laps at 30.
    for r in range(1, 9):
        state = (49, 0, 9 + r)
        slopes = [0, 9]
        anchor = 15
        for _ in range(300):
            clock, x, y = state
            if clock == anchor:
                copies = 3 if clock == 15 else 5
                end, drift, minimum = normal_segment(clock, 21)
                assert end == clock
                for j, base in enumerate((x, y)):
                    new = slopes[j] + copies * drift[j]
                    assert new >= 0
                    # At u>=1 the first or last lap minimizes the exponent.
                    floor = base + (slopes[j] if drift[j] >= 0 else new - drift[j])
                    assert floor + minimum[j] >= 0
                    if j == 0:
                        for length in range(1, 22):
                            q, delta, _ = normal_segment(clock, length)
                            assert q != 49 or floor + delta[0] > 0
                    slopes[j] = new
                anchor = None
            _, commands = sweep_clock(6, clock)
            for j, base in enumerate((x, y)):
                if base == 0 and commands >> j & 1:
                    assert slopes[j] == 0
            state, fired = advance(6, (0, 1), state)
            if clock == 34 and 1 in fired:
                anchor = 30
            if None in state:
                assert state[1 if r in (3, 6) else 2] is None
                break
            assert state[:2] != (49, 0)
        else:
            raise AssertionError("Missing counter loss")
    for h in range(9):
        state = (49, 0, h)
        for t in range(1, 120):
            state, _ = advance(6, (0, 1), state)
            if None in state or state[:2] == (49, 0):
                break
        if h == 1:
            assert (t, state) == (23, (49, 0, 2))
        else:
            assert None in state


def check():
    check_power_exits()
    # Each successful header produces precisely 4*(k+1) copies for the tail.
    recovered = {}
    for digit in range(128):
        result = trace(128, digit, {}, 49)
        if result and result[1] == (4, 4):
            recovered[digit] = result[0]
    assert recovered == {62: 49, 69: 41}

    for tail in (0, 1, 62, 69):
        for digit, rounds, delta in ((62, 49, 11), (69, 41, 7)):
            result = trace(128, digit, {3: 1, 5: 7}, rounds, physical_tail=tail)
            t, tape, regs, _, fired = result
            assert (t, tape, regs) == (rounds, (4, 4), {0: 0, 3: 2, 5: 7 + delta})
            assert all(j == 0 for _, j in fired)

    for tail in (0, 1, 69):
        for z, rounds, output, guard_events in ((7, 73, 1, 1), (10, 59, 1, 0), (13, 59, 4, 0)):
            result = trace(1 << 17, 28942, {2: z}, rounds, physical_tail=tail)
            t, tape, regs, _, fired = result
            assert (t, tape, regs) == (rounds, (4, 4), {0: 0, 2: output})
            assert sum(j == 2 for _, j in fired) == guard_events

    # Same live datum and header, two different arithmetic updates of the tape.
    for z, rounds, tape, z_out in [(1, 55, (4, 4), 1), (100, 117, (262144, 131072), 81)]:
        result = trace(128, 23, {2: z}, rounds, physical_tail=2)
        assert result[:3] == (rounds, tape, {0: 0, 2: z_out})

    headers = [(131072, 28942), (16384, 16375), (2048, 445), (2048, 445)]
    for initial_guard, gain in ((7, 39), (10, 45)):
        suffix = 69
        tails = []
        for radix, digit in reversed(headers):
            tails.append(suffix)
            suffix = radix * suffix + digit
        guard, data = initial_guard, 1
        for (radix, digit), tail in zip(headers, reversed(tails)):
            assert suffix == radix * tail + digit
            result = trace(radix, digit, {2: guard, 5: data}, 100, physical_tail=tail)
            _, tape, regs, _, fired = result
            assert tape == (4, 4) and all(j != 5 for _, j in fired)
            guard, data, suffix = regs[2], regs[5], tail
        assert (guard, data, suffix) == (7, 1 + gain, 69)
    result = trace(512, 269, {2: 7, 5: 1}, 55, physical_tail=0)
    assert result[:3] == (55, (4, 4), {0: 0, 2: 10, 5: 6})
    assert all(j != 5 for _, j in result[4])
    print("Verified composable digits, arithmetic dispatch, and both complete test-and-reset routes.")


if __name__ == "__main__":
    check()
