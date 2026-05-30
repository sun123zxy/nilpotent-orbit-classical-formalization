import NilpotentOrbitClassicalFormalization.Dominance.CoverA.Minimality
import Mathlib.Order.Cover

/-!
# A-type dominance covers

This file formalizes the A-type characterization of covering relations for the
dominance order on partitions.
-/

open Finset

namespace Nat.Partition

/-- The conclusion of the A-type covering relation proposition. -/
def IsBoxDrop {n : ℕ} (lam mu : Nat.Partition n) : Prop :=
  ∃ i j : ℕ, i < j ∧
    lam.rowLen i = mu.rowLen i + 1 ∧
    mu.rowLen j = lam.rowLen j + 1 ∧
    ∀ k : ℕ, k ≠ i → k ≠ j → mu.rowLen k = lam.rowLen k

/--
The canonical one-box drops that are covers in the full partition dominance order.

Besides the local Young-diagram validity checks for `boxDropPartition`, the final
disjunction records the A-type minimality condition: either the source and target
rows are adjacent, or the target row is exactly two boxes shorter than the source row.
-/
def IsCoverBoxDrop {n : ℕ} (lam mu : Nat.Partition n) : Prop :=
  ∃ (s t : ℕ) (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s),
      (t = s + 1 ∨ lam.rowLen t + 2 = lam.rowLen s) ∧
        mu = boxDropPartition lam hst hsource htarget hgap

lemma exists_source_row_of_covBy {n : ℕ} {mu lam : Nat.Partition n} (h : mu ⋖ lam) :
    ∃ i : ℕ, mu.rowLen i < lam.rowLen i :=
  exists_rowLen_lt_of_lt h.lt

lemma isBoxDrop_of_eq_boxDropPartition {n : ℕ} {mu lam : Nat.Partition n} {s t : ℕ}
    (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hmu : mu = boxDropPartition lam hst hsource htarget hgap) :
    IsBoxDrop lam mu := by
  subst mu
  refine ⟨s, t, hst, ?_, ?_, ?_⟩
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap, if_pos rfl]
    omega
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [ne_of_gt hst]
  · intro k hks hkt
    rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [hks, hkt]

lemma boxDropPartition_lt_original {n : ℕ} (lam : Nat.Partition n) {s t : ℕ}
    (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) :
    boxDropPartition lam hst hsource htarget hgap < lam := by
  refine ⟨boxDropPartition_le_original lam hst hsource htarget hgap, ?_⟩
  intro hlam_le
  have hprefix := hlam_le (s + 1)
  have hmid : s < s + 1 ∧ s + 1 ≤ t :=
    ⟨Nat.lt_succ_self s, Nat.succ_le_of_lt hst⟩
  rw [prefixSum_boxDropPartition_of_mid lam hst hsource htarget hgap hmid] at hprefix
  rw [prefixSum_succ] at hprefix
  omega

lemma isCoverBoxDrop_le {n : ℕ} {lam mu : Nat.Partition n}
    (h : IsCoverBoxDrop lam mu) : mu ≤ lam := by
  rcases h with ⟨s, t, hst, hsource, htarget, hgap, _, rfl⟩
  exact boxDropPartition_le_original lam hst hsource htarget hgap

lemma isCoverBoxDrop_lt {n : ℕ} {lam mu : Nat.Partition n}
    (h : IsCoverBoxDrop lam mu) : mu < lam := by
  rcases h with ⟨s, t, hst, hsource, htarget, hgap, _, rfl⟩
  exact boxDropPartition_lt_original lam hst hsource htarget hgap

lemma isCoverBoxDrop_isBoxDrop {n : ℕ} {lam mu : Nat.Partition n}
    (h : IsCoverBoxDrop lam mu) : IsBoxDrop lam mu := by
  rcases h with ⟨s, t, hst, hsource, htarget, hgap, _, hmu⟩
  exact isBoxDrop_of_eq_boxDropPartition hst hsource htarget hgap hmu

lemma exists_isCoverBoxDrop_between_of_lt {n : ℕ} {mu lam : Nat.Partition n}
    (h : mu < lam) :
  ∃ nu : Nat.Partition n, IsCoverBoxDrop lam nu ∧ mu ≤ nu ∧ nu ≤ lam ∧ nu ≠ lam := by
  classical
  rcases nonempty_firstDropData_of_lt h with ⟨D⟩
  by_cases hexact : lam.rowLen D.j + 2 = lam.rowLen D.i0
  · rcases nonempty_plateauSourceData lam D.hi0j
      (lt_trans (Nat.lt_succ_self _) D.hgap_i0) with ⟨S⟩
    have htarget : lam.rowLen D.j < lam.rowLen (D.j - 1) := D.rowLen_j_lt_pred
    have hgap : lam.rowLen D.j + 1 < lam.rowLen S.s := by
      rw [S.hsrow]
      exact D.hgap_i0
    let nu := boxDropPartition lam S.hsj S.hsource htarget hgap
    have hmu_le_nu : mu ≤ nu :=
      le_boxDropPartition_of_prefix_surplus S.hsj S.hsource htarget hgap h.1
        (prefix_surplus_of_rowLen_le_before_target S.hi0s D.hrowBefore D.hstrict)
    have hnu_le_lam : nu ≤ lam :=
      boxDropPartition_le_original lam S.hsj S.hsource htarget hgap
    have hnu_ne_lam : nu ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen S.s) hEq
      change (boxDropPartition lam S.hsj S.hsource htarget hgap).rowLen S.s =
        lam.rowLen S.s at hroweq
      rw [rowLen_boxDropPartition lam S.hsj S.hsource htarget hgap, if_pos rfl] at hroweq
      omega
    refine ⟨nu, ?_, hmu_le_nu, hnu_le_lam, hnu_ne_lam⟩
    refine ⟨S.s, D.j, S.hsj, S.hsource, htarget, hgap, ?_, rfl⟩
    right
    rw [S.hsrow]
    exact hexact
  · have hst : D.j - 1 < D.j := D.pred_lt_j
    have hlower : lam.rowLen D.i0 ≤ lam.rowLen (D.j - 1) + 1 :=
      D.rowLen_i0_le_pred_add_one
    have hjgap_large : lam.rowLen D.j + 2 < lam.rowLen D.i0 := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt D.hgap_i0) hexact
    have hsource : lam.rowLen ((D.j - 1) + 1) < lam.rowLen (D.j - 1) := by
      have hjpred : (D.j - 1) + 1 = D.j := Nat.sub_add_cancel D.j_pos
      rw [hjpred]
      linarith
    have htarget : lam.rowLen D.j < lam.rowLen (D.j - 1) := by
      linarith
    have hgap : lam.rowLen D.j + 1 < lam.rowLen (D.j - 1) := by
      linarith
    let nu := boxDropPartition lam hst hsource htarget hgap
    have hmu_le_nu : mu ≤ nu :=
      le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.1
        (prefix_surplus_of_rowLen_le_before_target D.i0_le_pred D.hrowBefore D.hstrict)
    have hnu_le_lam : nu ≤ lam :=
      boxDropPartition_le_original lam hst hsource htarget hgap
    have hnu_ne_lam : nu ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen (D.j - 1)) hEq
      change (boxDropPartition lam hst hsource htarget hgap).rowLen (D.j - 1) =
        lam.rowLen (D.j - 1) at hroweq
      rw [rowLen_boxDropPartition lam hst hsource htarget hgap, if_pos rfl] at hroweq
      omega
    refine ⟨nu, ?_, hmu_le_nu, hnu_le_lam, hnu_ne_lam⟩
    refine ⟨D.j - 1, D.j, hst, hsource, htarget, hgap, ?_, rfl⟩
    left
    exact (Nat.sub_add_cancel D.j_pos).symm

/-- A dominance cover is one of the canonical one-box drops. -/
theorem isCoverBoxDrop_of_covBy {n : ℕ} {mu lam : Nat.Partition n} (h : mu ⋖ lam) :
    IsCoverBoxDrop lam mu := by
  classical
  rcases nonempty_firstDropData_of_lt h.lt with ⟨D⟩
  by_cases hexact : lam.rowLen D.j + 2 = lam.rowLen D.i0
  · rcases nonempty_plateauSourceData lam D.hi0j
      (lt_trans (Nat.lt_succ_self _) D.hgap_i0) with ⟨S⟩
    have htarget : lam.rowLen D.j < lam.rowLen (D.j - 1) := D.rowLen_j_lt_pred
    have hgap : lam.rowLen D.j + 1 < lam.rowLen S.s := by
      rw [S.hsrow]
      exact D.hgap_i0
    have hmu_le_nu :
        mu ≤ boxDropPartition lam S.hsj S.hsource htarget hgap :=
      le_boxDropPartition_of_prefix_surplus S.hsj S.hsource htarget hgap h.le
        (prefix_surplus_of_rowLen_le_before_target S.hi0s D.hrowBefore D.hstrict)
    have hnu_le_lam :
        boxDropPartition lam S.hsj S.hsource htarget hgap ≤ lam :=
      boxDropPartition_le_original lam S.hsj S.hsource htarget hgap
    have hnu_ne_lam : boxDropPartition lam S.hsj S.hsource htarget hgap ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen S.s) hEq
      change (boxDropPartition lam S.hsj S.hsource htarget hgap).rowLen S.s =
        lam.rowLen S.s at hroweq
      rw [rowLen_boxDropPartition lam S.hsj S.hsource htarget hgap, if_pos rfl] at hroweq
      omega
    refine ⟨S.s, D.j, S.hsj, S.hsource, htarget, hgap, ?_,
      (eq_of_between h hmu_le_nu hnu_le_lam hnu_ne_lam).symm⟩
    right
    rw [S.hsrow]
    exact hexact
  · have hst : D.j - 1 < D.j := D.pred_lt_j
    have hlower : lam.rowLen D.i0 ≤ lam.rowLen (D.j - 1) + 1 :=
      D.rowLen_i0_le_pred_add_one
    have hjgap_large : lam.rowLen D.j + 2 < lam.rowLen D.i0 := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt D.hgap_i0) hexact
    have hsource : lam.rowLen ((D.j - 1) + 1) < lam.rowLen (D.j - 1) := by
      have hjpred : (D.j - 1) + 1 = D.j := Nat.sub_add_cancel D.j_pos
      rw [hjpred]
      linarith
    have htarget : lam.rowLen D.j < lam.rowLen (D.j - 1) := by
      linarith
    have hgap : lam.rowLen D.j + 1 < lam.rowLen (D.j - 1) := by
      linarith
    have hmu_le_nu :
        mu ≤ boxDropPartition lam hst hsource htarget hgap :=
      le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.le
        (prefix_surplus_of_rowLen_le_before_target D.i0_le_pred D.hrowBefore D.hstrict)
    have hnu_le_lam :
        boxDropPartition lam hst hsource htarget hgap ≤ lam :=
      boxDropPartition_le_original lam hst hsource htarget hgap
    have hnu_ne_lam : boxDropPartition lam hst hsource htarget hgap ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen (D.j - 1)) hEq
      change (boxDropPartition lam hst hsource htarget hgap).rowLen (D.j - 1) =
        lam.rowLen (D.j - 1) at hroweq
      rw [rowLen_boxDropPartition lam hst hsource htarget hgap, if_pos rfl] at hroweq
      omega
    refine ⟨D.j - 1, D.j, hst, hsource, htarget, hgap, ?_,
      (eq_of_between h hmu_le_nu hnu_le_lam hnu_ne_lam).symm⟩
    left
    exact (Nat.sub_add_cancel D.j_pos).symm

/-- Covering in dominance order moves exactly one box from an earlier row to a later row. -/
theorem isBoxDrop_of_covBy {n : ℕ} {mu lam : Nat.Partition n} (h : mu ⋖ lam) :
    IsBoxDrop lam mu := by
  exact isCoverBoxDrop_isBoxDrop (isCoverBoxDrop_of_covBy h)

theorem covBy_of_isCoverBoxDrop {n : ℕ} {mu lam : Nat.Partition n}
    (h : IsCoverBoxDrop lam mu) : mu ⋖ lam := by
  rcases h with ⟨s, t, hst, hsource, htarget, hgap, hminimal, rfl⟩
  rw [covBy_iff_lt_and_eq_or_eq]
  refine ⟨boxDropPartition_lt_original lam hst hsource htarget hgap, ?_⟩
  intro nu hmu_le_nu hnu_le_lam
  rcases hminimal with hadj | hexact
  · exact eq_boxDropPartition_or_eq_original_of_between_adjacent lam hst hsource htarget hgap
      hadj hmu_le_nu hnu_le_lam
  · exact eq_boxDropPartition_or_eq_original_of_between_exact lam hst hsource htarget hgap
      hexact hmu_le_nu hnu_le_lam

theorem covBy_iff_isCoverBoxDrop {n : ℕ} {mu lam : Nat.Partition n} :
    mu ⋖ lam ↔ IsCoverBoxDrop lam mu :=
  ⟨isCoverBoxDrop_of_covBy, covBy_of_isCoverBoxDrop⟩

end Nat.Partition
