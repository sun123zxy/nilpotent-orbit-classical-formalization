# Formalization of Dominance-Order Covers for Admissible Partitions of Classical Types

This Lean 4 project formalizes some partition combinatorics used for
nilpotent orbits in classical Lie algebras. Currently we have formalized the characterization of the covering relation of the dominance order for admissible partitions of each classical type (A, C and B / D).

We are working on a paper where we explain how the project is structured and designed and how we use LLM and agentic tools to assist with the formalization. Currently it's not available, but we will link it here when it's ready. For now please refer to the classical literatures:

- Gerstenhaber, Murray. “Dominance Over The Classical Groups.” Annals of Mathematics 74, no. 3 (1961): 532–69. https://doi.org/10.2307/1970297.
- Hesselink, Wim. “Singularities in the Nilpotent Scheme of a Classical Group.” Transactions of the American Mathematical Society 222 (1976): 1–32. https://doi.org/10.2307/1997656.

## Version

- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`
- Mathlib: `v4.30.0-rc2`
- Build: `lake build`

## Structure

- `YoungDiagramPartition.lean`: conversion lemmas between `YoungDiagram` and
  `Nat.Partition`.
- `Dominance/Basic.lean`: row lengths, prefix sums, dominance order, and common
  row/prefix lemmas.
- `Dominance/BoxDrop.lean`: the explicit one-box-drop construction and its
  dominance facts.
- `Dominance/Move.lean`: shared row-equality predicates and subtype cover
  minimality helpers.
- `Dominance/CoverA/Minimality.lean`: the interval argument showing canonical
  A-type drops have no strict intermediate partition.
- `Dominance/CoverA.lean`: the A-type cover characterization corresponding to
  `#prp-cover-a`.
- `Dominance/Classical.lean`: C- and B/D-type admissibility, admissible-partition
  subtypes, and shared parity/counting lemmas.
- `Dominance/DoubleDrop.lean`: shared order facts for two successive one-box drops.
- `Dominance/CoverC/Moves.lean`: the five C-type move-shape predicates.
- `Dominance/CoverC/Surplus.lean`: prefix-surplus and parity helpers for C-type
  cover arguments.
- `Dominance/CoverC/Admissibility.lean`: proofs that the five C-type move shapes
  preserve C-admissibility.
- `Dominance/CoverC/DoubleDrop.lean`: explicit C-type double-drop move wrappers.
- `Dominance/CoverC/Forward.lean`: the forward C-type cover theorem.
- `Dominance/CoverC/Reverse.lean`: currently formalized reverse fragments.
- `Dominance/CoverC.lean`: thin entry module for the C-type cover files.
- `Dominance/CoverBD/*`: the parallel B/D-type move, surplus, admissibility,
  double-drop, and forward-cover files.
