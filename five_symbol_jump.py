"""A repeatable conditional jump in a five-symbol 2-tag system."""
from collections import deque

UNIT = "zaaazaea"
RULES = {"I": "ezII", "z": "e", "e": "", "a": "b", "b": UNIT}


def boundary(clock, first, second):
    """Seven integrators, with counters before cells 0 and 2 (low bit first)."""
    cells = [("e" if clock & (1 << j) else "") + "ezII" for j in range(7)]
    word = UNIT * (1 << first) + "".join(cells[:2])
    word += UNIT * (1 << second) + "".join(cells[2:])
    return word[(clock >> 6) & 1:]


def check():
    # At the start of the loop the second exponent may be any h >= 1.
    # It changes by -1,+1,+1,+1,+1; only the first counter underflows.
    loop = [(93, 0, 0), (108, 1, -1), (54, 2, 0),
            (14, 1, 1), (41, 0, 2), (93, 0, 3)]
    cases = 0
    for h in range(1, 10):
        queue = deque(boundary(93, 0, h))
        for clock, first, delta in loop[1:]:
            for _ in range(2):
                for _ in range((len(queue) + 1) // 2):
                    head = queue.popleft()
                    queue.popleft()
                    queue.extend(RULES[head])
            assert "".join(queue) == boundary(clock, first, h + delta)
            cases += 1
    print(f"Matched {cases} full physical queue boundaries.")


if __name__ == "__main__":
    check()
