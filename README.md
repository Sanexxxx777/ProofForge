# ProofForge

An AI-agent pipeline that produces machine-verified Lean 4 / Mathlib proofs.

Agents decompose a problem, prove the pieces, and formalize them in Lean. The Lean kernel rechecks every step: `#print axioms` shows only the standard axioms, and `native_decide` is never used. A wrong proof does not compile — so "the AI proved it" is not something you take on trust; the checker either accepts it or it doesn't.

## Contributions to Google DeepMind's formal-conjectures

- **Erdős #1084** — `f₁(n) = n − 1` for unit-distance configurations on a line.
  Merged: https://github.com/google-deepmind/formal-conjectures/pull/4245
- **Erdős #1052** — the 5th unitary perfect number, `146361946186458562560000` (24 digits), proved via multiplicativity of the unitary divisor-sum `σ*`. It was an unproved `sorry` in the repo.
  In review: https://github.com/google-deepmind/formal-conjectures/pull/4244

Both proofs are kernel-verified. The Lean sources are in [`proofs/`](proofs/).

## How it works

1. **Survey** — find the known approach for the problem.
2. **Decompose** — split it into atomic lemmas.
3. **Prove + verify** — agents prove each piece; an adversarial pass tries to refute it.
4. **Formalize** — translate to Lean 4 / Mathlib and compile until the kernel accepts it.

---

Built by Aleksandr Shulgin · [shulgin.is-a.dev](https://shulgin.is-a.dev)
