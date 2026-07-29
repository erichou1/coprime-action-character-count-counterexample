# Zero-Free Invariant Characters under Coprime Action: A Counterexample

This repository contains the manuscript and exact verification programs for
**Zero-Free Invariant Characters under Coprime Action: A Counterexample** by Eric Hou.
The paper gives a negative answer to Problem 21.100 in the 21st issue of the
Kourovka Notebook.

For the constructed coprime action of \(A\cong C_{21}\) on
\(G\cong C_2^{128}\rtimes C_2^7\), the paper proves

\[
|N_A(G)|=1728<4096=|C_G(A)/C_G(A)'|.
\]

## Repository contents

- `main.tex`: LaTeX source for the paper.
- `paper.pdf`: compiled manuscript.
- `verification/linear_criterion.py`: enumeration from the complete affine
  zero criterion.
- `verification/direct_field.py`: direct computation in
  \(\mathbf F_4^2\oplus\mathbf F_8\).
- `verification/walsh_transform.py`: full 128-point integer Walsh-transform
  calculation.
- `tests/test_verification.py`: exhaustive consistency tests for the three
  counts, the correlation identity, the twenty zero patterns, the orbit
  decomposition, and the explicit zero witness.

The three implementations all return

```text
zero-free: 1728
has a zero: 2368
```

They are independent checks; the proof in `main.tex` does not rely on them.

## Reproduce the verification

Python 3.12 is the tested version.

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
make verify
```

To run an implementation separately:

```bash
python -m verification.linear_criterion
python -m verification.direct_field
python -m verification.walsh_transform
```

## Build the paper

A TeX distribution containing `amsmath`, `amsthm`, `mathtools`, `microtype`,
`enumitem`, and `hyperref` is required.

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
