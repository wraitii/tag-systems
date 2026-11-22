"""An unbounded FizzBuzz stream under the fixed productions in parity_program."""

from parity_program import COUNTER, RULES, clock

TRANSLATION = str.maketrans(RULES)


def initial_queue():
    """Return three clock blocks, one W tile, and a final clock block."""
    fizz, buzz, lane = [], [], []
    for slot in range(1, 17):
        # Four sweeps per slot. Slot 16 undoes its first doubling.
        fizz.extend([int(slot % 3 == 0), 0, 0, 0])
        buzz.extend([int(slot % 5 == 0), 0, 0, 0])
        lane.extend([0, 0, int(slot == 16), 0])
    masks = [fizz, [a ^ b for a, b in zip(fizz, buzz)],
             [a ^ b for a, b in zip(buzz, lane)], lane]
    return [clock(mask) for mask in masks], 1


def sweep(clocks, tile, copies):
    """Read alternate physical letters. Keep the homogeneous data run compressed."""
    phase = 0
    boundaries = []
    updated = []
    for index, block in enumerate(clocks):
        if index == 3:
            # The data run lies between the third and fourth clocks.
            data_output = tile[phase::2].translate(TRANSLATION)
            if tile == COUNTER:
                copies *= len(data_output)
                tile = "b"
            else:
                # An even run of b's selects exactly half on either lane.
                assert copies % 2 == 0
                copies //= 2
                tile = COUNTER
        updated.append(block[phase::2].translate(TRANSLATION))
        phase ^= len(block) % 2
        boundaries.append(phase)
    assert phase == 0
    return updated, tile, copies, boundaries


def fizzbuzz():
    clocks, copies = initial_queue()
    tile = COUNTER
    while True:
        for slot in range(1, 17):
            for tick in range(4):
                clocks, tile, copies, boundaries = sweep(clocks, tile, copies)
                if tick == 0:
                    fizz, buzz = boundaries[:2]
            if slot <= 15:
                # After n emitted slots the physical queue contains 4**n W tiles.
                exponent = copies.bit_length() - 1
                assert tile == COUNTER and copies == 1 << exponent and exponent % 2 == 0
                yield ("Fizz" * fizz + "Buzz" * buzz) or str(exponent // 2)


def initial_word():
    clocks, copies = initial_queue()
    return "".join(clocks[:3]) + COUNTER * copies + clocks[3]


def main():
    import argparse
    from itertools import islice

    parser = argparse.ArgumentParser(description=__doc__)
    raw = parser.add_mutually_exclusive_group()
    raw.add_argument("--initial", action="store_true", help="print the literal starting queue")
    raw.add_argument("--steps", type=int, metavar="N",
                     help="print the starting queue and the next N literal queues, one per line")
    args = parser.parse_args()
    if args.steps is not None and args.steps < 0:
        parser.error("--steps must be nonnegative")
    if args.initial or args.steps is not None:
        word = initial_word()
        print(word)
        for _ in range(args.steps or 0):
            word = word[2:] + RULES[word[0]]
            print(word)
    else:
        print(" ".join(islice(fizzbuzz(), 100)))


if __name__ == "__main__":
    main()
