import NilpotentOrbitClassicalFormalization.Dominance.CoverC.Forward

/-!
# C-type reverse fragments

Split from `Dominance/CoverC.lean` to keep the C-type cover formalization navigable.
-/

namespace Nat.Partition

theorem isCoverBoxDrop_of_isCMove₁ {N : ℕ} {lam mu : Nat.Partition N}
    (h : IsCMove₁ lam mu) :
    IsCoverBoxDrop lam mu := by
  rcases h with
    ⟨s, t, hst, _hs_even, _ht_even, hexact, hs, ht, hrest⟩
  have hsource : lam.rowLen (s + 1) < lam.rowLen s := by
    have hanti : mu.rowLen (s + 1) ≤ mu.rowLen s :=
      (YoungDiagram.ofPartition mu).rowLen_anti s (s + 1) (Nat.le_succ s)
    by_cases hs1t : s + 1 = t
    · rw [hs1t]
      omega
    · have hs1s : s + 1 ≠ s := by linarith
      have hrow := hrest (s + 1) hs1s hs1t
      rw [hrow] at hanti
      omega
  have htarget : lam.rowLen t < lam.rowLen (t - 1) := by
    have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le s) hst
    by_cases hpreds : t - 1 = s
    · have hpred : t = s + 1 := by omega
      rw [hpreds]
      omega
    · have hanti : mu.rowLen t ≤ mu.rowLen (t - 1) :=
        (YoungDiagram.ofPartition mu).rowLen_anti (t - 1) t
          (by omega)
      have hpredt : t - 1 ≠ t := by omega
      have hrow := hrest (t - 1) hpreds hpredt
      rw [ht, hrow] at hanti
      omega
  have hgap : lam.rowLen t + 1 < lam.rowLen s := by linarith
  refine ⟨s, t, hst, hsource, htarget, hgap, ?_, ?_⟩
  · right
    omega
  · apply ext_of_rowLen_eq
    intro k
    rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    by_cases hks : k = s
    · subst k
      rw [if_pos rfl]
      omega
    · by_cases hkt : k = t
      · subst k
        rw [if_neg (ne_of_gt hst), if_pos rfl]
        exact ht
      · rw [if_neg hks, if_neg hkt]
        exact hrest k hks hkt

theorem CPartition.covBy_of_isCMove₁ {n : ℕ} {mu lam : CPartition n}
    (h : IsCMove₁ (lam : Nat.Partition (2 * n)) mu) :
    mu ⋖ lam :=
  CPartition.covBy_of_covBy_val (covBy_of_isCoverBoxDrop (isCoverBoxDrop_of_isCMove₁ h))


end Nat.Partition
