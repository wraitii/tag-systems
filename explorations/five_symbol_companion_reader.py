"""Whole-queue checks for the companion count and the unmodified reload family."""
from five_symbol_writer_reload import (
    CELL, FIRST_BANK, RECORD, SECOND_BANK, THREE_RECORDS, UNIT, WRITER, boundary, sweeps, word,
)


def divided(bank, data, left, spacer, right):
    phase, prefix = boundary(bank, data, 0)
    return phase, prefix + word(("b", left), (UNIT, spacer), ("b", right))


def check_lap():
    # left and right are at least eight. Their residues sum to one modulo four.
    for d, e, spacer, result in ((1, 0, 64, 16), (3, 2, 16, 16), (2, 3, 16, 16)):
        start = divided([], 13, (8+d, 4, 0), spacer, (8+e, 0, 4))
        end = divided(RECORD, 53, (2+int(d>0), 1, 0), result,
                      (2+int(e>0), 0, 1))
        assert sweeps(start, 8) == end
        # Vary data and spacer independently on the same parity path.
        start = divided([], (13, 1, 0), 8+d, (spacer, 0, spacer), 8+e)
        end = divided(RECORD, (53, 4, 0), 2+int(d>0),
                      (result, 0, result), 2+int(e>0))
        assert sweeps(start, 8) == end
        assert sweeps(divided([], 13, 8+d, spacer, 8+e), 8, literal=True) == divided(
            RECORD, 53, 2+int(d>0), result, 2+int(e>0))


def loader(bank, data, second_data):
    phase, runs = boundary(bank, data, 126)
    return phase, runs[:-1] + word(("b", 1 << 17), (UNIT, second_data)) + runs[-1:]


def check_reader():
    assert sweeps(loader(THREE_RECORDS, (21, 32, 0), (0, 0, 32)), 81) == divided(
        SECOND_BANK, 13, (17, 2, 0), 64, (0, 0, 2))
    for k in (3, 4, 8, 31):
        tape = (205*4**k+47)//3
        data = 16*tape - 251
        h = k + 2
        tail = [(t, n*4**j) for j in range(3, h) for t, n in RECORD]
        tail.extend((t, n*4**h) for t, n in FIRST_BANK)
        state = loader(THREE_RECORDS + tail, data, 2*data-234)
        bank = [(t, n*4**j) for j in range(k) for t, n in RECORD]
        loaded = SECOND_BANK + [("b", n*65536) if t == UNIT else (UNIT, n*8)
                                for t, n in tail]
        bank.extend((t, n*4**k) for t, n in loaded)
        expected = divided(bank, (40*4**k-1)//3, 69, 16, 137)
        assert sweeps(state, 81+8*k) == expected


def growth_region(state):
    phase, runs = state
    if phase or sum(t == CELL for t, _ in runs) != 2:
        return False
    middle = next(i for i in range(1, len(runs)) if runs[i][0] == CELL)
    for part in (runs[:middle], runs[middle:]):
        if part[:3] != word((CELL, 1), (WRITER, 1), (UNIT, 1)) or len(part) < 4:
            return False
        tile, (c, u, v) = part[3]
        if tile != "b" or c % 2 != 1 or u % 2 or v % 2:
            return False
        for tile, count in part[4:]:
            if tile not in (UNIT, "b") or (tile == "b" and any(n % 2 for n in count)):
                return False
    return True


def check_unmodified():
    # Use the shared prefix for h >= 11, allowing any number of later bank pairs.
    base = list(SECOND_BANK)
    for j in range(3, 11):
        base.extend([("b", 2*4**j*65536), (UNIT, 4*4**j*8)])
    tape = (205*4**9+47)//3
    state = sweeps(boundary(base, 13, (tape, 4**9, 0)), 334)
    assert growth_region(state)
    assert state[1][-1] == ("b", (544, 8, 0))

    # A zero-constant pair between the shared prefix and second C contributes
    # even width at every sweep. It can be inserted any number of times.
    pair = [("b", (0, 2*4**11*65536, 0)), (UNIT, (0, 0, 32*4**11))]
    extended = sweeps(boundary(base+pair, 13, tape), 334)
    assert growth_region(extended)
    index = next(i for i in range(1, len(extended[1])) if extended[1][i][0] == CELL)
    assert extended[1][index-2:index] == [
        ("b", (0, 70368744177664, 0)), (UNIT, (0, 0, 1099511627776))]
    assert all(n % 2 == 0 for tile, n in FIRST_BANK if tile == UNIT)
    assert all(n % 4 == 0 for tile, n in FIRST_BANK if tile == "b")


if __name__ == "__main__":
    check_lap()
    check_reader()
    check_unmodified()
    print("Verified the two-writer reader and the growth region for the original reload.")
