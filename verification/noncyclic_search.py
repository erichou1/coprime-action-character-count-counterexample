"""Balance condition over ALL odd-order operator groups, for dim V <= 5.

Let A be a finite group of odd order acting faithfully on V = F_2^n with
C_V(A) = 0.  By Maschke, V is a direct sum of nontrivial simple
F_2[A]-modules V_i, and the image of A in GL(V_i) is an odd-order group
acting faithfully and irreducibly.  The manuscript's reduction lemma
shows that for dim V_i <= 5 such an image lies in Gamma L(m, 2^e) with
me = dim V_i and e > 1.  So A embeds block-diagonally into a product of
such groups, and for n <= 5 there are only finitely many products to
consider.

This module enumerates the odd-order subgroups of each of those products
and tests the balance condition.  Two prunings make the search small and
are justified in the manuscript:

  * if A <= A' then every A'-stable set is A-stable, so a balanced A'
    has only balanced subgroups; an unbalanced group can therefore be
    pruned along with all of its overgroups;
  * balance is inherited downward and C_V(A) = 0 is inherited upward, so
    it suffices to examine subgroups minimal with respect to C_V(A) = 0.

The result is that no pair (A, V) with dim V <= 5 is balanced.
"""

from __future__ import annotations

from itertools import product as iproduct

POLY = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011}


def _fmul(a: int, b: int, e: int) -> int:
    mod, r = POLY[e], 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> e & 1:
            a ^= mod
    return r & ((1 << e) - 1)


def identity(n: int) -> tuple[int, ...]:
    return tuple(1 << i for i in range(n))


def mat_mul(a, b, n):
    out = []
    for i in range(n):
        row, r = 0, a[i]
        for j in range(n):
            if r >> j & 1:
                row ^= b[j]
        out.append(row)
    return tuple(out)


def apply(m, v, n):
    out = 0
    for i in range(n):
        if v >> i & 1:
            out ^= m[i]
    return out


def group_closure(gens, n, limit=500000):
    ident = identity(n)
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mat_mul(x, g, n)
                if y not in seen:
                    seen.add(y)
                    if len(seen) > limit:
                        raise MemoryError("ambient group too large")
                    nxt.append(y)
        frontier = nxt
    return seen


def _mult_matrix(alpha, e):
    return tuple(_fmul(alpha, 1 << i, e) for i in range(e))


def _block_diag(mats, dims):
    n, rows, off = sum(dims), [], 0
    for m, d in zip(mats, dims):
        for i in range(d):
            rows.append(m[i] << off)
        off += d
    assert len(rows) == n
    return tuple(rows)


def gamma_l_gens(m: int, e: int):
    """Generators of Gamma L(m, 2^e), as F_2-matrices of size m*e."""
    n = m * e
    gens = []
    if e > 1:
        gens.append(_block_diag([_mult_matrix(2, e)] + [identity(e)] * (m - 1),
                                [e] * m))
        sq = tuple(_fmul(1 << i, 1 << i, e) for i in range(e))
        gens.append(_block_diag([sq] * m, [e] * m))
    if m > 1:
        rows = [1 << i for i in range(n)]
        for i in range(e):
            rows[e + i] ^= 1 << i
        gens.append(tuple(rows))
        rows = [0] * n
        for k in range(m):
            for i in range(e):
                rows[k * e + i] = 1 << (((k + 1) % m) * e + i)
        gens.append(tuple(rows))
    return [g for g in gens if g != identity(n)]


def orbit_sizes(elements, n):
    unseen, sizes = set(range(1 << n)), []
    while unseen:
        v = next(iter(unseen))
        orb = {apply(g, v, n) for g in elements}
        sizes.append(len(orb))
        unseen -= orb
    return sorted(sizes)


def is_balanced(sizes, target):
    reach = 1
    for s in sizes:
        reach |= reach << s
        reach &= (1 << (target + 1)) - 1
    return bool(reach >> target & 1)


def _fixed_is_zero(elements, n):
    return all(
        any(apply(g, v, n) != v for g in elements)
        for v in range(1, 1 << n)
    )


def search_ambient(gens, n):
    """Return (subgroups explored, balanced groups with C_V(A) = 0)."""
    ident = identity(n)
    big = group_closure(gens, n)
    order = len(big)
    odd_part = order
    while odd_part % 2 == 0:
        odd_part //= 2

    odd_elems = []
    for g in big:
        x, p, e = ident, g, odd_part
        while e:
            if e & 1:
                x = mat_mul(x, p, n)
            p = mat_mul(p, p, n)
            e >>= 1
        if x == ident:
            odd_elems.append(g)

    target = 1 << (n - 1)
    seen = {frozenset([ident])}
    frontier, hits = [frozenset([ident])], []
    while frontier:
        nxt = []
        for H in frontier:
            for g in odd_elems:
                if g in H:
                    continue
                K = frozenset(group_closure(list(H) + [g], n))
                if K in seen or len(K) % 2 == 0:
                    continue
                seen.add(K)
                sizes = orbit_sizes(K, n)
                if not is_balanced(sizes, target):
                    continue          # no overgroup of K can be balanced
                if _fixed_is_zero(K, n):
                    hits.append((len(K), sizes))
                    continue          # only minimal C_V = 0 groups needed
                nxt.append(K)
        frontier = nxt
    return len(seen), hits


def partitions(n, minpart=2):
    if n == 0:
        yield ()
        return
    for p in range(minpart, n + 1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def shapes(d):
    return [(d // e, e) for e in range(2, d + 1) if d % e == 0]


def _embed(mat, offset, sub_dim, n):
    rows = [1 << i for i in range(n)]
    for i in range(sub_dim):
        rows[offset + i] = mat[i] << offset
    return tuple(rows)


def all_cases(n):
    """Yield (label, generators) for every module shape in dimension n."""
    for parts in partitions(n):
        for choice in iproduct(*[shapes(d) for d in parts]):
            gens, off = [], 0
            for d, (m, e) in zip(parts, choice):
                for g in gamma_l_gens(m, e):
                    gens.append(_embed(g, off, d, n))
                off += d
            if gens:
                label = " + ".join(f"{d}[m={m},e={e}]"
                                   for d, (m, e) in zip(parts, choice))
                yield label, gens


def run(nmax=5):
    """Search every dimension up to nmax.  Returns the list of balanced
    pairs found (empty, for nmax <= 5)."""
    found = []
    for n in range(2, nmax + 1):
        for label, gens in all_cases(n):
            explored, hits = search_ambient(gens, n)
            print(f"n={n}  {label:<28} {explored:>4} subgroups, "
                  f"{len(hits)} balanced with C_V(A)=0")
            found.extend((n, label) + h for h in hits)
    return found


if __name__ == "__main__":
    hits = run(5)
    print()
    print(f"balanced pairs with dim V <= 5: {len(hits)}")
