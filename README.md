# ProofForge

An AI-agent pipeline that produces machine-verified Lean 4 / Mathlib proofs.

Agents decompose a problem, prove the pieces, and formalize them in Lean. The Lean kernel rechecks every step: `#print axioms` shows only the standard axioms, and `native_decide` is never used. A wrong proof does not compile — so "the AI proved it" is not something you take on trust; the checker either accepts it or it doesn't.

## Contributions to Google DeepMind's formal-conjectures

Four pull requests merged into [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures):

| PR | Problem | What it contributes |
|----|---------|---------------------|
| [#4245](https://github.com/google-deepmind/formal-conjectures/pull/4245) | Erdős #1084 | `f₁(n) = n − 1` for unit-distance configurations on a line — the upper bound proved. |
| [#4244](https://github.com/google-deepmind/formal-conjectures/pull/4244) | Erdős #1052 | The 5th unitary perfect number, `146361946186458562560000` (24 digits), via multiplicativity of the unitary divisor-sum `σ*`. It was an unproved `sorry` in the repo. |
| [#4361](https://github.com/google-deepmind/formal-conjectures/pull/4361) | Erdős #418 | The Odd Noncototient Conjecture stated formally. |
| [#4364](https://github.com/google-deepmind/formal-conjectures/pull/4364) | Green's open problems #64 | The Ω(p−2)-odd infinitude question formalized. |

Two more are open at the time of writing: [#4379](https://github.com/google-deepmind/formal-conjectures/pull/4379) (linking a formal proof of the unit-distance disproof for Erdős #90) and [#4360](https://github.com/google-deepmind/formal-conjectures/pull/4360) (a faster proof of `isUnitaryPerfect_87360`).

All merged proofs are kernel-verified. The Lean sources for the first two are in [`proofs/`](proofs/); the rest live upstream in the repository they were contributed to.

## Related Erdős repositories

This repo covers Lean 4 formalization only. Two other repos tackle different
Erdős problems with different methods:

- [erdos-computational-bounds](https://github.com/Sanexxxx777/erdos-computational-bounds) —
  SAT + LRAT certificate and a segmented sieve for Erdős #273, #385, #647
  (no Lean, no ML).
- [erdos-openevolve](https://github.com/Sanexxxx777/erdos-openevolve) — an
  evolutionary LLM coding pipeline reproducing a numerical SOTA bound for the
  minimum overlap problem; not a formal proof.

## How it works

1. **Survey** — find the known approach for the problem.
2. **Decompose** — split it into atomic lemmas.
3. **Prove + verify** — agents prove each piece; an adversarial pass tries to refute it.
4. **Formalize** — translate to Lean 4 / Mathlib and compile until the kernel accepts it.

---

Built by Aleksandr Shulgin (@Aleksandr_NFA) · [shulgin.is-a.dev](https://shulgin.is-a.dev)

## License

Apache License 2.0, matching [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures), where these proofs were contributed and where their canonical versions live. The Lean files in `proofs/` carry the upstream copyright header of The Formal Conjectures Authors.
