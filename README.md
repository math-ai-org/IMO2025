# IMO 2025 Lean Formalizations

Lean 4 formalizations of problems from the 2025 International Mathematical Olympiad.

## Status

| Problem | File | Status |
| --- | --- | --- |
| 5 | [`IMO2025P5.lean`](./IMO2025P5.lean) | Proved |

For Problem 5, the Lean encoding classifies every real parameter `c`:

- Alice has a winning strategy exactly when `1 / √2 < c`.
- Bazza has a winning strategy exactly when `c < 1 / √2`.
- At `c = 1 / √2`, neither player has a winning strategy.

Restricting to the original problem's positive parameter gives Bazza's interval
`0 < c < 1 / √2`.

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

To build Problem 5 only:

```bash
lake build IMO2025P5
```

## Repository conventions

- Problem files are named `IMO2025P<N>.lean`.
- Public declarations use the namespace `IMO2025P<N>`.
- Each problem is registered as a `lean_lib` target in [`lakefile.toml`](./lakefile.toml).
- New proofs should compile with the pinned project toolchain and avoid placeholders or custom axioms.

## License

This repository is licensed under the [Apache License 2.0](./LICENSE).
