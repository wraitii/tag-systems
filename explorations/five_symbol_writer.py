"""Five fixed productions that write a reversed/complemented word, then read it."""

from collections import deque

from five_symbol_transfer import drop_first, equal_words, physical_sweep
from four_symbol_loop import CELL, RULES as SHUTTLE_RULES, UNIT

WRITER = "JJeb"
RULES = {**SHUTTLE_RULES, "J": WRITER}


def boundary(phase, left, output, right, prefix=0, leading_units=0):
    """C W^left C V W^leading_units b^prefix W^output C W^right, with the leading phase cut."""
    word = [(tile, count) for tile, count in
            ((CELL, 1), (UNIT, left), (CELL, 1), (WRITER, 1),
             (UNIT, leading_units), ("b", prefix), (UNIT, output), (CELL, 1), (UNIT, right)) if count]
    return drop_first(word) if phase else word


def round_check(start, end, literal=False):
    before = boundary(*start)
    after = boundary(*end)
    assert equal_words(physical_sweep(physical_sweep(before, RULES), RULES), after)
    if literal:
        queue = deque("".join(tile * n for tile, n in before))
        for _ in range(2):
            for _ in range((len(queue) + 1) // 2):
                head = queue.popleft()
                queue.popleft()
                queue.extend(RULES[head])
        assert "".join(queue) == "".join(tile * n for tile, n in after)


def write_and_read(width, source, initial_output=0, literal=False):
    assert 0 <= source < 1 << width
    left, output, right = (1 << width) - source, initial_output, source
    for _ in range(width):
        assert (left ^ right) % 2 == 0
        successor = ((left + 1) // 2, 2 * output + 1 - right % 2, right // 2)
        round_check((0, left, output, right), (0, *successor), literal)
        left, output, right = successor
    reversed_source = int(format(source, "0%db" % width)[::-1], 2) if width else 0
    answer = (initial_output << width) + (1 << width) - 1 - reversed_source
    assert (left, output, right) == (1, answer, 0)

    # A solitary odd left block closes the write loop and appends a zero.
    round_check((0, 1, answer, 0), (1, 1, 2 * answer, 0), literal)
    round_check((1, 1, 2 * answer, 0), (1, 2, answer, 0, 4), literal)
    # The next whole-queue boundary has a phase selected by the written value.
    phase = 1 ^ (answer % 2)
    round_check((1, 2, answer, 0, 4), (phase, 4, (answer + 1) // 2, 0, 12), literal)
    # Continue reading to the first one, or verify further zero-only laps.
    left, value, prefix = 2, answer, 4
    trailing = (answer & -answer).bit_length() - 1 if answer else 2
    for _ in range(trailing):
        assert value % 2 == 0
        successor = (1, 2 * left, value // 2, 0, 4 + 2 * prefix)
        round_check((1, left, value, 0, prefix), successor, literal)
        _, left, value, _, prefix = successor
    if answer:
        assert value % 2 == 1
        written = (value + 1) // 2
        new_prefix = 4 + 2 * prefix
        round_check((1, left, value, 0, prefix), (0, 2 * left, written, 0, new_prefix), literal)
        # The selected write phase executes; JJeb emits a new UNIT on sweep two.
        round_check((0, 2 * left, written, 0, new_prefix),
                    (0, left, 2 * written, 0, new_prefix // 2, 1), literal)
    return answer, phase


def check():
    for width in range(9):
        for source in range(1 << width):
            write_and_read(width, source, literal=(width <= 3))
    for width, source in ((32, 0x12345678), (64, (1 << 64)-1), (1000, (1 << 999)+1)):
        write_and_read(width, source, initial_output=5)
    assert write_and_read(3, 0b010) == (0b101, 0)
    assert write_and_read(3, 0b110) == (0b100, 1)
    print("Verified 511 exhaustive width/input cases, three larger inputs, both readback phases and re-entry to writing.")


if __name__ == "__main__":
    check()
