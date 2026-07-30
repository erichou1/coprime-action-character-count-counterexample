# Coprime actions and characters nonvanishing on the fixed-point subgroup

This repository contains the manuscript and exact verification programs for
**Coprime actions and characters nonvanishing on the fixed-point subgroup**
by Eric Hou. The paper answers Problem 21.100 of the 21st issue of the
Kourovka Notebook negatively.

Problem 21.100 is the coprime-action analogue of Burnside's theorem that the
nonvanishing irreducible characters of a group are exactly the linear ones. It
asks whether, for a coprime action of \(A\) on \(G\) with \(C=C_G(A)\), the
number of \(A\)-invariant \(\chi\in\mathrm{Irr}(G)\) with \(\chi_C\) nowhere
zero is always \(|C/C'|\).

For the constructed action of \(A\cong C_{21}\) on
\(G=B\rtimes V\cong C_2^{128}\rtimes C_2^7\), with
\(V=\mathbf F_4^2\oplus\mathbf F_8\) and \(B\) the Boolean functions on \(V\),
the paper proves

\[
|N_A(G)|=1728<4096=|C_G(A)/C_G(A)'|.
\]

Since \(C\cong C_2^{12}\) is abelian, every Glauberman–Isaacs correspondent is
linear, so the example also refutes the stronger criterion proposed with the
problem: 2368 invariant characters have linear correspondent yet vanish
somewhere on \(C\). That criterion is **Problem 6.3** of G. Navarro,
*Problems on characters: solvable groups*, Publ. Mat. **67** (2023), 173–198,
which therefore has a negative answer — and the counterexample lies in the
nilpotent case Navarro singles out there as "territory for counterexamples".
It also shows that the hypothesis that the operator group be a \(p\)-group,
in the one direction of Problem 6.3 known to hold, cannot be dropped.
By a theorem of Isaacs, *Carter subgroups, characters and composition series*,
Trans. Amer. Math. Soc. Ser. B **9** (2022), 470–498, the invariant characters
with linear correspondent are exactly his *A-head characters*, so the example
also shows that the \(A\)-head characters are not the invariant characters
nonvanishing on \(C\).

Passing to \(\Gamma = G\rtimes A\), whose Carter subgroup is
\(K = C\times A\), settles the Carter analogue too: exactly **36288**
irreducible characters of \(\Gamma\) are nonvanishing on \(K\), while
\(|K/K'| = 86016\). This refutes **Problem 6.7** — a conjecture of Navarro
that Isaacs reports is supported by "abundant computational evidence" — and
shows the head characters of a solvable group need not be its
Carter-nonvanishing characters. Since \(|\Gamma| = 2^{135}\cdot 21\), no
computer search would have reached it.

Neither counterexample depends on the particular \(V\), nor on \(A\) being
cyclic. Call \((A,V)\) *balanced* if \(V\) has an \(A\)-stable subset of half
its size; every balanced pair with \(A\) of odd order gives a counterexample
to both problems (the Carter statement additionally needs \(A\) abelian),
and balanced pairs are closed under adding a fixed-point-free summand, so
there are infinitely many. The minima are now exact, over *all* operator
groups of odd order: no prime-power \(A\) is balanced in any dimension, no
\(A\) whatsoever is balanced with \(\dim V\le 6\), the least dimension is 7,
the least operator order is \(|A|=15\) (attained at \(\dim V=8\)), and the
least group order in the family is \(2^{135}\). The proof is a scalar-divisor
argument on simple summands plus a short support-sum analysis
(`verification/scalar_obstruction.py`, with an independent subgroup
enumeration in `verification/noncyclic_search.py`). The fixed subgroup
need not be abelian either: multiplying by any nonabelian 2-group on which
\(A\) acts trivially preserves the failure.

Section 9 of the paper records precisely which neighbouring problems
(6.1, 6.5, 6.6, and those of Section 5) are *not* affected, with proofs.
Taking direct powers makes the ratios \((27/64)^n\) arbitrarily small.

## How the example was found

The paper reduces everything to a subset-sum condition (the *balance
condition*): the construction yields a counterexample exactly when some
sub-multiset of the \(A\)-orbit sizes on \(V\) sums to \(|V|/2\). No operator
group of prime power order admits such a \(V\), and the smallest admissible design
is \(|A|=21\) with \(\dim V=7\), where the orbit sizes are forced to be

```text
1, 3, 3, 3, 3, 3, 7, 21, 21, 21, 21, 21     and     1 + 21 + 21 + 21 = 64.
```

That identity is the whole example. `verification/design_search.py` reproduces
this enumeration.

## Repository contents

- `main.tex`: LaTeX source for the paper.
- `paper.pdf`: compiled manuscript.
- `verification/design_search.py`: the design-space enumeration — every
  candidate with \(\dim V\le7\), and the wider search over \(|A|\le105\),
  \(\dim V\le14\).
- `verification/scalar_obstruction.py`: the support-sum criterion proving no
  odd-order operator group is balanced below dimension 7.
- `verification/noncyclic_search.py`: independent subgroup enumeration over
  all odd-order operator groups for \(\dim V\le5\).
- `verification/carter_subgroup.py`: the character count on the Carter
  subgroup \(K=C\times A\) of \(\Gamma=G\rtimes A\).
- `verification/linear_criterion.py`: enumeration from the complete affine
  zero criterion.
- `verification/direct_field.py`: direct computation in
  \(\mathbf F_4^2\oplus\mathbf F_8\).
- `verification/walsh_transform.py`: full 128-point integer Walsh-transform
  calculation.
- `verification/verify.g`: an independent check in **GAP**, using GAP's own
  character theory rather than any formula from the paper (see below).
- `tests/test_verification.py`: consistency tests for the three counts, the
  correlation identity, the twenty zero patterns, the orbit decomposition,
  the explicit zero witness, the design table, the Carter-subgroup count,
  the support-sum criterion, and the subgroup enumeration.

The three counting implementations all return

```text
zero-free: 1728
has a zero: 2368
```

They are independent checks; the proof in `main.tex` does not rely on them.
Note that \(|G|=2^{135}\), so \(G\) cannot be built in a computer algebra
system — and nothing here needs it. Every computation runs either on the
7-dimensional space \(V\) (128 points, 12 orbits) or on the 12-dimensional
space \(B^A\) (4096 elements).

## Independent check in GAP

Since \(|G| = 2^{135}\) cannot be built in any computer algebra system, the
GAP script checks the two ingredients the counterexample is assembled from:
the dimension-7 arithmetic (orbit sizes, \(C_V(A)=0\), \(1+21+21+21=64\),
twenty \(A\)-stable halves), and the structural machinery in the same family
\(G = C_2 \wr V\) at \(\dim V = 2, 3\) — where GAP confirms
\(C_G(A)=B^A\), \(|\mathrm{Irr}_A(G)| = |C/C'|\), and the lemma
\(\chi_{\delta_0}(c) = |V| - 2|\mathrm{supp}\,c|\) that produces the zero.
It closes with a balanced non-fixed-point-free case (\(|G| = 2048\)) where
GAP exhibits vanishing invariant characters directly.

```bash
gap -q -b --nointeract verification/verify.g
```

## Reproduce the verification

Python 3.9 or later; 3.12 is the tested version.

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
make verify
```

To run an implementation separately:

```bash
python -m verification.design_search
```

```bash
python -m verification.linear_criterion
```

```bash
python -m verification.direct_field
```

```bash
python -m verification.walsh_transform
```

```bash
python -m verification.carter_subgroup
```

```bash
python -m verification.scalar_obstruction
```

```bash
python -m verification.noncyclic_search
```

## Build the paper

A TeX distribution containing `amsmath`, `amsthm`, `mathtools`, `microtype`,
`enumitem`, `booktabs`, and `hyperref` is required.

```bash
make paper
```

The build runs `pdflatex` twice and writes `main.pdf`. The tracked
`paper.pdf` is the publication copy produced from the same `main.tex` source.

## Reference

E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory:
The Kourovka Notebook*, No. 21, Sobolev Institute of Mathematics,
Novosibirsk, 2026, Problem 21.100, p. 178,
[arXiv:1401.0300v45](https://arxiv.org/abs/1401.0300v45).

## License

See `LICENSE`.
