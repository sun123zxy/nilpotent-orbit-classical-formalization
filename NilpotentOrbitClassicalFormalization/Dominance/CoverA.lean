import NilpotentOrbitClassicalFormalization.Dominance.CoverA.Minimality
import Mathlib.Order.Cover

/-!
# A-type dominance covers

This file formalizes the A-type characterization of covering relations for the
dominance order on partitions.
-/

open Finset

namespace Nat.Partition

/-- The conclusion of the A-type covering relation proposition in `docs/dominance.qmd`. -/
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
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp
    have hpos : 0 < lam.rowLen s := by omega
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
  have hmid : s < s + 1 ∧ s + 1 ≤ t := by omega
  rw [prefixSum_boxDropPartition_of_mid lam hst hsource htarget hgap hmid] at hprefix
  rw [prefixSum_succ] at hprefix
  have hpos : 0 < lam.rowLen s := by omega
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
  rcases exists_first_rowLen_lt_of_lt h with ⟨i0, hbefore, hstrict⟩
  let targetExists := exists_drop_target_of_first_row (mu := mu) (lam := lam)
    hbefore hstrict
  let j := Nat.find targetExists
  have hj_spec : i0 < j ∧ lam.rowLen j + 1 < lam.rowLen i0 :=
    Nat.find_spec targetExists
  have hi0j : i0 < j := hj_spec.1
  have hjgap_i0 : lam.rowLen j + 1 < lam.rowLen i0 := hj_spec.2
  have hnoDrop :
      ∀ r : ℕ, i0 ≤ r → r < j → ¬lam.rowLen r + 1 < lam.rowLen i0 := by
    intro r hi0r hrj hdrop
    rcases eq_or_lt_of_le hi0r with rfl | hi0r_lt
    · omega
    · exact Nat.find_min targetExists hrj ⟨hi0r_lt, hdrop⟩
  have hrowBefore : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r :=
    rowLen_mu_le_lam_before_target hbefore hstrict hnoDrop
  by_cases hexact : lam.rowLen j + 2 = lam.rowLen i0
  · have hjdrop : lam.rowLen j < lam.rowLen i0 := by omega
    rcases exists_plateau_source lam hi0j hjdrop with
      ⟨s, hi0s, hsj, hsrow, hsource⟩
    have htarget : lam.rowLen j < lam.rowLen (j - 1) := by
      have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i0) hi0j
      have hi0pred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
      have hpred_lt : j - 1 < j := Nat.sub_one_lt_of_lt hjpos
      have hnopred := hnoDrop (j - 1) hi0pred hpred_lt
      have hlower : lam.rowLen i0 ≤ lam.rowLen (j - 1) + 1 := le_of_not_gt hnopred
      omega
    have hgap : lam.rowLen j + 1 < lam.rowLen s := by
      rw [hsrow]
      exact hjgap_i0
    let nu := boxDropPartition lam hsj hsource htarget hgap
    have hmu_le_nu : mu ≤ nu :=
      le_boxDropPartition_of_prefix_surplus hsj hsource htarget hgap h.1
        (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict)
    have hnu_le_lam : nu ≤ lam :=
      boxDropPartition_le_original lam hsj hsource htarget hgap
    have hnu_ne_lam : nu ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen s) hEq
      change (boxDropPartition lam hsj hsource htarget hgap).rowLen s = lam.rowLen s at hroweq
      rw [rowLen_boxDropPartition lam hsj hsource htarget hgap] at hroweq
      simp at hroweq
      have hpos : 0 < lam.rowLen s := by omega
      omega
    refine ⟨nu, ?_, hmu_le_nu, hnu_le_lam, hnu_ne_lam⟩
    refine ⟨s, j, hsj, hsource, htarget, hgap, ?_, rfl⟩
    right
    omega
  · have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i0) hi0j
    have hst : j - 1 < j := Nat.sub_one_lt_of_lt hjpos
    have hi0pred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
    have hnopred := hnoDrop (j - 1) hi0pred hst
    have hlower : lam.rowLen i0 ≤ lam.rowLen (j - 1) + 1 := le_of_not_gt hnopred
    have hjgap_large : lam.rowLen j + 2 < lam.rowLen i0 := by
      have hle : lam.rowLen j + 2 ≤ lam.rowLen i0 := by omega
      exact lt_of_le_of_ne hle hexact
    have hsource : lam.rowLen ((j - 1) + 1) < lam.rowLen (j - 1) := by
      have hjpred : (j - 1) + 1 = j := Nat.sub_add_cancel hjpos
      rw [hjpred]
      omega
    have htarget : lam.rowLen j < lam.rowLen (j - 1) := by
      omega
    have hgap : lam.rowLen j + 1 < lam.rowLen (j - 1) := by
      omega
    let nu := boxDropPartition lam hst hsource htarget hgap
    have hmu_le_nu : mu ≤ nu :=
      le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.1
        (prefix_surplus_of_rowLen_le_before_target hi0pred hrowBefore hstrict)
    have hnu_le_lam : nu ≤ lam :=
      boxDropPartition_le_original lam hst hsource htarget hgap
    have hnu_ne_lam : nu ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen (j - 1)) hEq
      change (boxDropPartition lam hst hsource htarget hgap).rowLen (j - 1) =
        lam.rowLen (j - 1) at hroweq
      rw [rowLen_boxDropPartition lam hst hsource htarget hgap] at hroweq
      simp at hroweq
      have hpos : 0 < lam.rowLen (j - 1) := by omega
      omega
    refine ⟨nu, ?_, hmu_le_nu, hnu_le_lam, hnu_ne_lam⟩
    refine ⟨j - 1, j, hst, hsource, htarget, hgap, ?_, rfl⟩
    left
    exact (Nat.sub_add_cancel hjpos).symm

/-- A dominance cover is one of the canonical one-box drops. -/
theorem isCoverBoxDrop_of_covBy {n : ℕ} {mu lam : Nat.Partition n} (h : mu ⋖ lam) :
    IsCoverBoxDrop lam mu := by
  classical
  rcases exists_first_rowLen_lt_of_lt h.lt with ⟨i0, hbefore, hstrict⟩
  let targetExists := exists_drop_target_of_first_row (mu := mu) (lam := lam)
    hbefore hstrict
  let j := Nat.find targetExists
  have hj_spec : i0 < j ∧ lam.rowLen j + 1 < lam.rowLen i0 :=
    Nat.find_spec targetExists
  have hi0j : i0 < j := hj_spec.1
  have hjgap_i0 : lam.rowLen j + 1 < lam.rowLen i0 := hj_spec.2
  have hnoDrop :
      ∀ r : ℕ, i0 ≤ r → r < j → ¬lam.rowLen r + 1 < lam.rowLen i0 := by
    intro r hi0r hrj hdrop
    rcases eq_or_lt_of_le hi0r with rfl | hi0r_lt
    · omega
    · exact Nat.find_min targetExists hrj ⟨hi0r_lt, hdrop⟩
  have hrowBefore : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r :=
    rowLen_mu_le_lam_before_target hbefore hstrict hnoDrop
  by_cases hexact : lam.rowLen j + 2 = lam.rowLen i0
  · have hjdrop : lam.rowLen j < lam.rowLen i0 := by omega
    rcases exists_plateau_source lam hi0j hjdrop with
      ⟨s, hi0s, hsj, hsrow, hsource⟩
    have htarget : lam.rowLen j < lam.rowLen (j - 1) := by
      have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i0) hi0j
      have hi0pred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
      have hpred_lt : j - 1 < j := Nat.sub_one_lt_of_lt hjpos
      have hnopred := hnoDrop (j - 1) hi0pred hpred_lt
      have hlower : lam.rowLen i0 ≤ lam.rowLen (j - 1) + 1 := le_of_not_gt hnopred
      omega
    have hgap : lam.rowLen j + 1 < lam.rowLen s := by
      rw [hsrow]
      exact hjgap_i0
    have hmu_le_nu :
        mu ≤ boxDropPartition lam hsj hsource htarget hgap :=
      le_boxDropPartition_of_prefix_surplus hsj hsource htarget hgap h.le
        (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict)
    have hnu_le_lam :
        boxDropPartition lam hsj hsource htarget hgap ≤ lam :=
      boxDropPartition_le_original lam hsj hsource htarget hgap
    have hnu_ne_lam : boxDropPartition lam hsj hsource htarget hgap ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen s) hEq
      change (boxDropPartition lam hsj hsource htarget hgap).rowLen s = lam.rowLen s at hroweq
      rw [rowLen_boxDropPartition lam hsj hsource htarget hgap] at hroweq
      simp at hroweq
      have hpos : 0 < lam.rowLen s := by omega
      omega
    rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
    · refine ⟨s, j, hsj, hsource, htarget, hgap, ?_, hnu_eq_mu.symm⟩
      right
      omega
    · exact False.elim (hnu_ne_lam hnu_eq_lam)
  · have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i0) hi0j
    have hst : j - 1 < j := Nat.sub_one_lt_of_lt hjpos
    have hi0pred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
    have hnopred := hnoDrop (j - 1) hi0pred hst
    have hlower : lam.rowLen i0 ≤ lam.rowLen (j - 1) + 1 := le_of_not_gt hnopred
    have hjgap_large : lam.rowLen j + 2 < lam.rowLen i0 := by
      have hle : lam.rowLen j + 2 ≤ lam.rowLen i0 := by omega
      exact lt_of_le_of_ne hle hexact
    have hsource : lam.rowLen ((j - 1) + 1) < lam.rowLen (j - 1) := by
      have hjpred : (j - 1) + 1 = j := Nat.sub_add_cancel hjpos
      rw [hjpred]
      omega
    have htarget : lam.rowLen j < lam.rowLen (j - 1) := by
      omega
    have hgap : lam.rowLen j + 1 < lam.rowLen (j - 1) := by
      omega
    have hmu_le_nu :
        mu ≤ boxDropPartition lam hst hsource htarget hgap :=
      le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.le
        (prefix_surplus_of_rowLen_le_before_target hi0pred hrowBefore hstrict)
    have hnu_le_lam :
        boxDropPartition lam hst hsource htarget hgap ≤ lam :=
      boxDropPartition_le_original lam hst hsource htarget hgap
    have hnu_ne_lam : boxDropPartition lam hst hsource htarget hgap ≠ lam := by
      intro hEq
      have hroweq := congrArg (fun p : Nat.Partition n => p.rowLen (j - 1)) hEq
      change (boxDropPartition lam hst hsource htarget hgap).rowLen (j - 1) =
        lam.rowLen (j - 1) at hroweq
      rw [rowLen_boxDropPartition lam hst hsource htarget hgap] at hroweq
      simp at hroweq
      have hpos : 0 < lam.rowLen (j - 1) := by omega
      omega
    rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
    · refine ⟨j - 1, j, hst, hsource, htarget, hgap, ?_, hnu_eq_mu.symm⟩
      left
      exact (Nat.sub_add_cancel hjpos).symm
    · exact False.elim (hnu_ne_lam hnu_eq_lam)

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
