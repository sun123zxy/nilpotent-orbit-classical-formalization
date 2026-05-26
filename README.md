# Formalization of Dominance-Order Covers for Partitions

This Lean 4 project formalizes some partition combinatorics used for
nilpotent orbits in classical Lie algebras. The current focus is the
dominance-order cover statements.

- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`
- Mathlib: `v4.30.0-rc2`
- Build: `lake build`

We are working on a paper where we explain how the project is structured and designed and how we use LLM and agentic tools to assist with the formalization. Currently it's not available, but we will link it here when it's ready.

## Structure

- `YoungDiagramPartition.lean`: conversion lemmas between `YoungDiagram` and
  `Nat.Partition`.
- `Dominance/Basic.lean`: row lengths, prefix sums, dominance order, and common
  row/prefix lemmas.
- `Dominance/BoxDrop.lean`: the explicit one-box-drop construction and its
  dominance facts.
- `Dominance/CoverA/Minimality.lean`: the interval argument showing canonical
  A-type drops have no strict intermediate partition.
- `Dominance/CoverA.lean`: the A-type cover characterization corresponding to
  `#prp-cover-a`.
- `Dominance/Classical.lean`: C-type admissibility and the admissible-partition subtype.
- `Dominance/CoverC/Moves.lean`: the five C-type move-shape predicates.
- `Dominance/CoverC/Surplus.lean`: prefix-surplus and parity helpers for C-type
  cover arguments.
- `Dominance/CoverC/Admissibility.lean`: proofs that the five C-type move shapes
  preserve C-admissibility.
- `Dominance/CoverC/DoubleDrop.lean`: explicit C-type double-drop constructions
  and dominance facts.
- `Dominance/CoverC/Forward.lean`: the forward C-type cover theorem.
- `Dominance/CoverC/Reverse.lean`: currently formalized reverse fragments.
- `Dominance/CoverC.lean`: thin entry module for the C-type cover files.
