import NilpotentOrbitClassicalFormalization.Dominance.Basic
import Mathlib.Order.Cover

/-!
# Shared row-move infrastructure

This file contains small predicates and subtype-cover helpers shared by the
classical-type cover statements.
-/

namespace Nat.Partition

def rowEqExcept₂ {N : ℕ} (lam mu : Nat.Partition N) (a b : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → mu.rowLen k = lam.rowLen k

def rowEqExcept₃ {N : ℕ} (lam mu : Nat.Partition N) (a b c : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → k ≠ c → mu.rowLen k = lam.rowLen k

def rowEqExcept₄ {N : ℕ} (lam mu : Nat.Partition N) (a b c d : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → k ≠ c → k ≠ d → mu.rowLen k = lam.rowLen k

lemma eq_of_between_subtype {α : Type*} [PartialOrder α]
    {mu lam nu : α} (h : mu ⋖ lam) (hmu_le_nu : mu ≤ nu) (hnu_le_lam : nu ≤ lam)
    (hnu_ne_lam : nu ≠ lam) :
    nu = mu := by
  rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
  · exact hnu_eq_mu
  · exact False.elim (hnu_ne_lam hnu_eq_lam)

end Nat.Partition
