# The 5/6-Poly-Density Question has answer no

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23309437.svg)](https://doi.org/10.5281/zenodo.23309437)

**Paper:** Biktairov, Gąsieniec, Jiamjitrak, Namrata, Smith, Wild, *Simple approximation algorithms for
Polyamorous Scheduling*, [arXiv:2411.06292](https://arxiv.org/abs/2411.06292), Question 6.1:

> Does every Decision Poly Scheduling instance with poly density d ≤ 5/6 admit a schedule?

## Solution

**No.** Take a triangle 0–1–2 with pendant edges 0–3 and 1–4. The required frequencies are:

| edge | 0–1 | 0–2 | 0–3 | 1–2 | 1–4 |
|---|---|---|---|---|---|
| f | X | 4 | 2 | 4 | 2 |

This instance is infeasible for every X ≥ 1, and its poly density is exactly **3/4 + 1/X**.
X = 13 gives d = 43/52 < 5/6. Letting X grow gives infeasible instances with density arbitrarily close
to 3/4, so the poly density threshold is at most 3/4. The paper's Theorem 1.2 shows that every DPS instance with
d ≤ 1/4 is schedulable, so the threshold lies in [1/4, 3/4].

**Why it is infeasible.**
1. Let 0–1 meet on some day s ≥ 1.
2. Edges 0–3 and 1–4 have frequency 2 and conflict with 0–1, so both must meet on days s−1 and s+1.
3. Vertices 0 and 1 are therefore busy on days s−1, s and s+1.
4. The 4-day window [s−1, s+2] must contain both 0–2 and 1–2, so both fall on day s+2.
5. But 0–2 and 1–2 share vertex 2, so they cannot meet on the same day.

**Density.** Vertices 0 and 1 each carry load 1/X + 1/4 + 1/2 = 3/4 + 1/X, which bounds d from below.
A fractional cover of the edges by maximal matchings with total weight 3/4 + 1/X bounds it from above.
The cover puts 1/X on {01} and 1/4 on each of {02,14}, {03,12} and {03,14}.

**Lean 4 (Mathlib).** [`PolyDensity.lean`](PolyDensity.lean) states Definitions 2.2 and 4.4 of the paper for
arbitrary simple graphs. It proves:
- `poly_density_question_false`: the answer to Question 6.1 is no;
- `infeasible_below`: there are infeasible instances with density in (3/4, 3/4 + ε) for every ε > 0.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`. To check it, run `lake exe cache get && lake build`.

## How it was found

A Claude loop exploring open problems from recent math papers. [`reproduce.jl`](reproduce.jl) regenerates the
supporting computations ([`output.txt`](output.txt)).
