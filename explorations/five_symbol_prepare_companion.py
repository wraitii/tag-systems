"""Prepare both input runs for the companion reader. Times count single sweeps."""
from five_symbol_companion_reader import divided, growth_region, loader
from five_symbol_transfer import drop_first, equal_words, physical_sweep
from five_symbol_writer_reload import (
    CELL, RECORD, RULES, SECOND_BANK, THREE_RECORDS, UNIT, boundary, sweep, sweeps, word,
)


def initial(height, data=68, extra_seed=0):
    """Timing positions depend on height. All W-run counts are bounded."""
    if height < 5:
        raise ValueError("height must be at least five")
    scale = 4**height
    total = 131197*scale + 1
    first = (height+1)//2
    previous = 0
    seeds = []
    for i in range(first, height):
        position = 131071*scale + 4**i
        count = 2050
        if i == first:
            count = 2128 if height % 2 else 1952
        seeds.extend([("b", position-previous), (UNIT, count)])
        previous = position
    if extra_seed:
        position = 131072*scale
        seeds.extend([("b", position-previous), (UNIT, extra_seed)])
        previous = position
    seeds.append(("b", total-previous))
    phase, prefix = boundary([], data, 0)
    return phase, prefix + word(*seeds)


def records(count):
    return [(tile, n*4**j) for j in range(count) for tile, n in RECORD]


def check_cut():
    # A zero-residue cut quadruples any marker. A one-residue cut quarters
    # a multiple of four. Check the cut positions and the independent data.
    for residue, unit, output_unit in ((0, 1, 4), (1, 4, 1)):
        right = 1-residue
        start = divided([], 68, (8+residue, 4, 0), unit, (8+right, 0, 4))
        end = divided(RECORD, 273, (2+residue, 1, 0), output_unit, (2+right, 0, 1))
        assert sweeps(start, 8) == end
        start = divided([], (68, 1, 0), 8+residue, (unit, 0, unit), 8+right)
        end = divided(RECORD, (273, 4, 0), 2+residue,
                      (output_unit, 0, output_unit), 2+right)
        assert sweeps(start, 8) == end


def physical_word(state):
    phase, runs = state
    assert all(not u and not v for _, (_, u, v) in runs)
    tiles = [(tile, n) for tile, (n, _, _) in runs]
    return drop_first(tiles) if phase else tiles


def check():
    check_cut()
    # Independent whole-word comparisons use the five literal productions.
    state = initial(5)
    for _ in range(16*5+65):
        actual = physical_sweep(physical_word(state), RULES)
        state = sweep(state)
        assert equal_words(actual, physical_word(state))

    for height in (5, 6, 7, 8, 15, 16, 31, 64):
        k = height-2
        data = (205*4**height - 1)//3
        state = initial(height, (68, 4, 0))
        bank = records(height)
        state = sweeps(state, 8*height)
        assert state == loader(bank, (data, 4**(height+1), 0), 2*data-234)
        tail = bank[len(THREE_RECORDS):]
        loaded = SECOND_BANK + [("b", n*65536) if t == UNIT else (UNIT, n*8)
                                for t, n in tail]
        state = sweeps(state, 81+8*k)
        expected_bank = records(k) + [(t, n*4**k) for t, n in loaded]
        assert state == divided(expected_bank, (40*4**k-1)//3, (69, 4, 0), 16, 137)
    check_post_read()
    check_payload_reload()
    print("Verified preparation, readback, the doubling region and the payload-controlled reload.")


def check_post_read():
    # All old bank pairs beyond the first three have these divisibilities.
    prefix = records(3)
    base = divided(prefix, (853, 2560, 0), (69, 0, 32768), 16, 137)
    end = sweeps(base, 76)
    assert growth_region(end)
    assert end[1][-2:] == word((UNIT, (72, 160, 0)), ("b", (0, 0, 128)))
    inserted = [(UNIT, (0, 128, 0)), ("b", (0, 0, 256))]
    extended = sweeps(divided(prefix + inserted, 853, 69, 16, 137), 76)
    assert growth_region(extended)
    cut = next(i for i, (tile, _) in enumerate(extended[1][1:], 1)
               if tile == CELL)
    assert extended[1][cut-2:cut] == word((UNIT, (0, 131072, 0)), ("b", (0, 0, 4096)))


def check_payload_reload():
    # The total control is 1 mod 4 on a lap. Its right component fixes
    # the left residue, hence the entire path, for all unread quotients.
    for right, spacer, next_spacer in ((140, 16, 4), (35, 4, 4), (9, 4, 16),
                                      (3, 16, 16), (1, 16, 64)):
        residue = (1-right) % 4
        start = divided([], (1, 0, 1), (residue, 4, 0), spacer, right)
        end = divided(RECORD, (5, 0, 4), (int(residue > 0), 1, 0),
                      next_spacer, (right+3)//4)
        assert sweeps(start, 8) == end
    assert sweeps(divided([], 13, (0, 4, 0), (16, 0, 16), 1), 8) == divided(
        RECORD, 53, (0, 1, 0), (64, 0, 64), 1)
    assert sweeps(divided(THREE_RECORDS, (21, 32, 0), 125, (0, 0, 256), 1),
                  81) == boundary(SECOND_BANK, 13, (17, 2, 4))

    for h, laps in ((5, 6), (6, 7), (11, 14), (16, 31)):
        k = h-2
        payload = 125*4**(laps-1)-52
        start = initial(h, 68+4*payload, extra_seed=3)
        n = (205*4**h-1)//3
        bank = records(h)
        state = sweeps(start, 8*h)
        assert state == loader(bank, n+4**(h+1)*payload, 2*n-234+3*4**h)
        tail = bank[len(THREE_RECORDS):]
        bank = SECOND_BANK + [("b", count*65536) if tile == UNIT else (UNIT, count*8)
                              for tile, count in tail]
        state = sweeps(state, 81+8*k)
        bank = records(k) + [(tile, count*4**k) for tile, count in bank]
        assert state == divided(bank, (40*4**k-1)//3, 69+4*payload, 16, 140)
        state = sweeps(state, 8*laps)
        n = (40*4**(k+laps)-1)//3
        spacer = 4**(laps-2)
        bank = records(laps) + [(tile, count*4**laps) for tile, count in bank]
        assert state == divided(bank, n, 125, spacer, 1)
        tail = bank[len(THREE_RECORDS):]
        bank = SECOND_BANK + [("b", count*65536) if tile == UNIT else (UNIT, count*8)
                              for tile, count in tail]
        state = sweeps(state, 81)
        assert state == boundary(bank, 13, (n+251)//16 + spacer//64)
        if laps >= 14:
            assert growth_region(sweeps(state, 334))
        if (h, laps) == (5, 6):
            literal = start
            for _ in range(16*h+146+8*laps):
                physical = physical_sweep(physical_word(literal), RULES)
                literal = sweep(literal)
                assert equal_words(physical, physical_word(literal))
            assert literal == state


if __name__ == "__main__":
    check()
