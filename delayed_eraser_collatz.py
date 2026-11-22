"""Delayed-eraser experiment at deletion two. Run directly to check the results."""

from collections import deque
from functools import lru_cache
from itertools import product

R = "bbeaeaeaez"
RULES = {"I": "ezII", "D": "DDez", "z": "e", "e": "", "a": R, "b": "a"}
TRANSLATION = str.maketrans(RULES)


def lane(word, bit):
    return word[bit::2].translate(TRANSLATION)


T = lane(R, 1)


def check_unary(limit):
    for n in range(2, limit + 1):
        queue = deque("a" * n)
        non_a = 0
        sweeps = 2 + n % 2
        for sweep in range(sweeps):
            steps = (len(queue) + 1) // 2
            for step in range(steps):
                head, partner = queue.popleft(), queue.popleft()
                tail = RULES[head]
                queue.extend(tail)
                non_a += len(tail) - tail.count("a") - (head != "a") - (partner != "a")
                assert (non_a == 0) == (sweep == sweeps - 1 and step == steps - 1)
        expected = n // 2 if n % 2 == 0 else (3*n + 1) // 2
        assert "".join(queue) == "a" * expected


def primitive(word):
    length = (word + word).index(word, 1)
    return word[:length], len(word) // length


@lru_cache(maxsize=2048)
def periodic_lane(tile, bit):
    # Two odd-width copies expose both alignments and restore the incoming lane.
    span = 1 + len(tile) % 2
    emitted = lane(tile * span, bit)
    if not emitted:
        return "", 0, span
    root, factor = primitive(emitted)
    return root, factor, span


def scalings(tile, horizon):
    """Exact 1/2 and 2 returns for any lane string through the given horizon."""
    root, factor = primitive(tile)
    initial = factor * (1 << horizon)
    states = {(root, initial)}
    found = set()
    for _ in range(horizon):
        successors = set()
        for word, count in states:
            for bit in (0, 1):
                new_word, factor, span = periodic_lane(word, bit)
                assert count % span == 0
                if factor:
                    successors.add((new_word, (count // span) * factor))
        if (root, initial // 2) in successors:
            found.add("halve")
        if (root, 2 * initial) in successors:
            found.add("double")
        states = successors
    return found


def check():
    assert lane(R, 0) == "a" and T == "a" + 3*R + "e"
    assert lane(T, 0) == R + 3*T and lane(T, 1) == "aaa"
    check_unary(1000)
    # First check the known halving path on R, then search mixed encodings.
    assert scalings(R, 2) == {"halve"}
    tested = 0
    hits = []
    for width in range(2, 5):
        for tokens in product(("a", R, T), repeat=width):
            if len(set(tokens)) == 1:
                continue
            tile = "".join(tokens)
            tested += 1
            if scalings(tile, 8) == {"halve", "double"}:
                hits.append(tokens)
    print(f"Verified 999 literal first returns. Tested {tested} mixed encodings "
          f"through eight sweeps; {len(hits)} admit both scalings.")
    for hit in hits:
        print(hit)


if __name__ == "__main__":
    check()
