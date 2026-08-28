# IMO 2025 Lean Formalizations

## Problem 5

`IMO2025/P5.lean` proves the exact game-theoretic classification encoded in the file:

- Alice has a winning strategy exactly when `1 / √2 < c`.
- Bazza has a winning strategy exactly when `c < 1 / √2`.
- At `c = 1 / √2`, neither player has a winning strategy.

The Lean encoding quantifies over every real `c`. Restricting to the original problem's positive parameter gives Bazza's interval `0 < c < 1 / √2`.

### Verification

```bash
lake update
lake build
```

The proof contains no `sorry`, `admit`, or custom axioms. Its transitive axiom usage is limited to Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.
