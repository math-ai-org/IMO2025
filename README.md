# IMO 2025 Lean Formalizations

Lean 4 formalizations of problems from the 2025 International Mathematical Olympiad.

## Status

| Problem | File | Status |
| --- | --- | --- |
| 1 | [`IMO2025P1.lean`](./IMO2025P1.lean) | Proved |
| 2 | [`IMO2025P2.lean`](./IMO2025P2.lean) | Proved |
| 3 | [`IMO2025P3.lean`](./IMO2025P3.lean) | Proved |
| 4 | [`IMO2025P4.lean`](./IMO2025P4.lean) | Proved |
| 5 | [`IMO2025P5.lean`](./IMO2025P5.lean) | Proved |
| 6 | [`IMO2025P6.lean`](./IMO2025P6.lean) | Proved |

For Problem 1, the Lean encoding proves that the possible numbers of sunny
lines are exactly `0`, `1`, and `3`.

For Problem 3, the least admissible constant is `4`.

For Problem 4, all possible initial values are

```text
a₁ = 6 · 12^k · m,
```

where `k ≥ 0`, `m` is a positive odd integer, and `5 ∤ m`; equivalently,
`gcd(m, 10) = 1`. For example, the first nonconstant admissible orbit is
`72 → 78 → 78 → ⋯`.

For Problem 5, the Lean encoding classifies every real parameter `c`:

- Alice has a winning strategy exactly when `1 / √2 < c`.
- Bazza has a winning strategy exactly when `c < 1 / √2`.
- At `c = 1 / √2`, neither player has a winning strategy.

Restricting to the original problem's positive parameter gives Bazza's interval
`0 < c < 1 / √2`.

For Problem 6, the Lean encoding proves that the minimum number of rectangles
in a valid `2025 × 2025` configuration is `2112`, including both a construction
attaining the bound and a universal lower-bound argument.

## Toolchain

- Lean `4.30.0-rc2`
- Mathlib `v4.30.0-rc2`
- Lake dependency versions are pinned in [`lake-manifest.json`](./lake-manifest.json).

## Build

Install [Lean through Elan](https://lean-lang.org/lean4/doc/setup.html), then run:

```bash
git clone https://github.com/math-ai-org/IMO2025.git
cd IMO2025
lake build
```

To build one problem only:

```bash
lake build IMO2025P1
# or
lake build IMO2025P2
# or
lake build IMO2025P3
# or
lake build IMO2025P4
# or
lake build IMO2025P5
# or
lake build IMO2025P6
```

## Repository conventions

- Problem files are named `IMO2025P<N>.lean`.
- Public declarations use the namespace `IMO2025P<N>`.
- Each problem is registered as a `lean_lib` target in [`lakefile.toml`](./lakefile.toml).
- New proofs should compile with the pinned project toolchain and avoid placeholders or custom axioms.

## License

This repository is licensed under the [Apache License 2.0](./LICENSE).
