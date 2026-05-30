import NilpotentOrbitClassicalFormalization.YoungDiagramPartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Dominance order basics for partitions

This file defines dominance order on `Nat.Partition` via prefix sums and proves the
general prefix and row-selection lemmas used by covering-relation arguments.
-/

open Finset

namespace Nat.Partition

/-- The padded row length sequence of a partition. -/
noncomputable abbrev rowLen {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ :=
  (YoungDiagram.ofPartition p).rowLen i

/-- Sum of the first `k` padded row lengths. -/
noncomputable abbrev prefixSum {n : ℕ} (p : Nat.Partition n) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, p.rowLen i

/-- Dominance order on partitions, with the larger orbit/partition on the left. -/
noncomputable def Dominates {n : ℕ} (lam mu : Nat.Partition n) : Prop :=
  ∀ k : ℕ, mu.prefixSum k ≤ lam.prefixSum k

lemma ext_of_rowLen_eq {n : ℕ} {p q : Nat.Partition n}
    (hrow : ∀ i : ℕ, p.rowLen i = q.rowLen i) : p = q := by
  have hdiagram : YoungDiagram.ofPartition p = YoungDiagram.ofPartition q := by
    ext c
    rcases c with ⟨i, j⟩
    simp [YoungDiagram.mem_iff_lt_rowLen, hrow i]
  apply Nat.Partition.ext
  rw [← YoungDiagram.rowLens_ofPartition_eq_parts p,
    ← YoungDiagram.rowLens_ofPartition_eq_parts q]
  exact congrArg (fun μ : YoungDiagram => (μ.rowLens : Multiset ℕ)) hdiagram

lemma rowLen_eq_of_prefixSum_eq {n : ℕ} {p q : Nat.Partition n}
    (hprefix : ∀ k : ℕ, p.prefixSum k = q.prefixSum k) :
    ∀ i : ℕ, p.rowLen i = q.rowLen i := by
  intro i
  have hsucc := hprefix (i + 1)
  have hi := hprefix i
  change (∑ x ∈ Finset.range i, p.rowLen x) =
    ∑ x ∈ Finset.range i, q.rowLen x at hi
  rw [prefixSum, prefixSum, Finset.sum_range_succ, Finset.sum_range_succ,
    hi] at hsucc
  exact Nat.add_left_cancel hsucc

lemma prefixSum_succ {n : ℕ} (p : Nat.Partition n) (i : ℕ) :
    p.prefixSum (i + 1) = p.prefixSum i + p.rowLen i := by
  rw [prefixSum, prefixSum, Finset.sum_range_succ]

/-- The parity of a prefix sum is the parity of the number of odd rows in it. -/
lemma even_prefixSum_iff_even_oddRows_card {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    Even (p.prefixSum k) ↔
      Even (((Finset.range k).filter fun r => Odd (p.rowLen r)).card) := by
  simpa [prefixSum] using Finset.even_sum_iff_even_card_odd
    (s := Finset.range k) (f := fun r => p.rowLen r)

lemma rowLen_eq_prefixSum_succ_sub {n : ℕ} (p : Nat.Partition n) (i : ℕ) :
    p.rowLen i = p.prefixSum (i + 1) - p.prefixSum i := by
  rw [prefixSum_succ]
  omega

lemma prefixSum_pos_of_rowLen_pos {n : ℕ} (p : Nat.Partition n) {i k : ℕ}
    (hik : i < k) (hpos : 0 < p.rowLen i) :
    0 < p.prefixSum k := by
  rw [prefixSum]
  have hi : i ∈ Finset.range k := by simpa using hik
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)

noncomputable instance instLE (n : ℕ) : LE (Nat.Partition n) where
  le mu lam := lam.Dominates mu

@[simp]
lemma le_iff_dominates {n : ℕ} {mu lam : Nat.Partition n} :
    mu ≤ lam ↔ lam.Dominates mu :=
  Iff.rfl

noncomputable instance instPartialOrder (n : ℕ) : PartialOrder (Nat.Partition n) where
  le := (· ≤ ·)
  lt p q := p ≤ q ∧ ¬q ≤ p
  le_refl p := by
    intro k
    rfl
  le_trans a b c hab hbc := by
    intro k
    exact le_trans (hab k) (hbc k)
  lt_iff_le_not_ge p q := Iff.rfl
  le_antisymm a b hab hba := by
    apply ext_of_rowLen_eq
    apply rowLen_eq_of_prefixSum_eq
    intro k
    exact le_antisymm (hab k) (hba k)

lemma eq_of_between {n : ℕ} {mu lam nu : Nat.Partition n}
    (h : mu ⋖ lam) (hmu_le_nu : mu ≤ nu) (hnu_le_lam : nu ≤ lam)
    (hnu_ne_lam : nu ≠ lam) :
    nu = mu := by
  rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
  · exact hnu_eq_mu
  · exact False.elim (hnu_ne_lam hnu_eq_lam)

lemma exists_prefixSum_lt_of_lt {n : ℕ} {mu lam : Nat.Partition n} (h : mu < lam) :
    ∃ k : ℕ, mu.prefixSum k < lam.prefixSum k := by
  rcases h with ⟨_hle, hnot⟩
  rw [le_iff_dominates] at hnot
  simp only [Dominates, not_forall, not_le] at hnot
  exact hnot

lemma prefixSum_colLen_eq {n : ℕ} (p : Nat.Partition n) :
    p.prefixSum ((YoungDiagram.ofPartition p).colLen 0) = n := by
  have h := YoungDiagram.sum_rowLens_eq_card (YoungDiagram.ofPartition p)
  calc
    p.prefixSum ((YoungDiagram.ofPartition p).colLen 0)
        = (YoungDiagram.ofPartition p).rowLens.sum := by
          rw [prefixSum, YoungDiagram.rowLens]
          generalize (YoungDiagram.ofPartition p).colLen 0 = m
          induction m with
          | zero => simp
          | succ m ih =>
              rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
              simp
    _ = (YoungDiagram.ofPartition p).card := h
    _ = n := YoungDiagram.card_ofPartition p

lemma rowLen_eq_zero_of_colLen_le {n : ℕ} (p : Nat.Partition n) {i : ℕ}
    (hi : (YoungDiagram.ofPartition p).colLen 0 ≤ i) : p.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hcell : (i, 0) ∈ YoungDiagram.ofPartition p := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    exact hpos
  have hlt : i < (YoungDiagram.ofPartition p).colLen 0 := by
    rwa [← YoungDiagram.mem_iff_lt_colLen]
  omega

lemma prefixSum_eq_of_colLen_le {n : ℕ} (p : Nat.Partition n) {k : ℕ}
    (hk : (YoungDiagram.ofPartition p).colLen 0 ≤ k) : p.prefixSum k = n := by
  let c := (YoungDiagram.ofPartition p).colLen 0
  change p.prefixSum k = n
  have hbase : p.prefixSum c = n := prefixSum_colLen_eq p
  have hstep : ∀ m ≥ c, p.prefixSum m = n → p.prefixSum (m + 1) = n := by
    intro m hm hpm
    rw [prefixSum, Finset.sum_range_succ]
    change (∑ x ∈ Finset.range m, p.rowLen x) + p.rowLen m = n
    rw [← prefixSum, hpm]
    have hz : p.rowLen m = 0 := rowLen_eq_zero_of_colLen_le p hm
    simp [hz]
  exact Nat.le_induction hbase hstep k hk

lemma exists_rowLen_lt_of_lt {n : ℕ} {mu lam : Nat.Partition n} (h : mu < lam) :
    ∃ i : ℕ, mu.rowLen i < lam.rowLen i := by
  classical
  let k := Nat.find (exists_prefixSum_lt_of_lt h)
  have hk : mu.prefixSum k < lam.prefixSum k :=
    Nat.find_spec (exists_prefixSum_lt_of_lt h)
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hk' : mu.prefixSum k < lam.prefixSum k := hk
    rw [hk0] at hk'
    simp [prefixSum] at hk'
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
  let i := k - 1
  have hk_eq : k = i + 1 := by
    dsimp [i]
    exact (Nat.sub_eq_iff_eq_add hk_pos).mp rfl
  have hprev_not : ¬mu.prefixSum i < lam.prefixSum i := by
    dsimp [i]
    exact Nat.find_min (exists_prefixSum_lt_of_lt h) (Nat.sub_lt hk_pos Nat.zero_lt_one)
  have hprev_le : mu.prefixSum i ≤ lam.prefixSum i := h.1 i
  have hprev_eq : mu.prefixSum i = lam.prefixSum i :=
    le_antisymm hprev_le (not_lt.mp hprev_not)
  have hprev_eq' :
      (∑ x ∈ Finset.range i, mu.rowLen x) =
        ∑ x ∈ Finset.range i, lam.rowLen x := hprev_eq
  use i
  rw [hk_eq, prefixSum, prefixSum, Finset.sum_range_succ, Finset.sum_range_succ,
    hprev_eq'] at hk
  exact Nat.lt_of_add_lt_add_left hk

lemma exists_first_rowLen_lt_of_lt {n : ℕ} {mu lam : Nat.Partition n} (h : mu < lam) :
    ∃ i0 : ℕ, (∀ r : ℕ, r < i0 → mu.rowLen r = lam.rowLen r) ∧
      mu.rowLen i0 < lam.rowLen i0 := by
  classical
  let k := Nat.find (exists_prefixSum_lt_of_lt h)
  have hk : mu.prefixSum k < lam.prefixSum k :=
    Nat.find_spec (exists_prefixSum_lt_of_lt h)
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hk' : mu.prefixSum k < lam.prefixSum k := hk
    rw [hk0] at hk'
    simp [prefixSum] at hk'
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
  let i0 := k - 1
  have hi0_lt_k : i0 < k := by
    dsimp [i0]
    omega
  have hk_eq : k = i0 + 1 := by
    dsimp [i0]
    exact (Nat.sub_eq_iff_eq_add hk_pos).mp rfl
  have hprefix_before (m : ℕ) (hm : m ≤ i0) : mu.prefixSum m = lam.prefixSum m := by
    have hnot : ¬mu.prefixSum m < lam.prefixSum m := by
      exact Nat.find_min (exists_prefixSum_lt_of_lt h) (lt_of_le_of_lt hm hi0_lt_k)
    exact le_antisymm (h.1 m) (not_lt.mp hnot)
  refine ⟨i0, ?_, ?_⟩
  · intro r hr
    have hr_le : r ≤ i0 := le_of_lt hr
    have hrsucc_le : r + 1 ≤ i0 := Nat.succ_le_of_lt hr
    have hprev := hprefix_before r hr_le
    have hsucc := hprefix_before (r + 1) hrsucc_le
    change (∑ x ∈ Finset.range r, mu.rowLen x) =
      ∑ x ∈ Finset.range r, lam.rowLen x at hprev
    rw [prefixSum, prefixSum, Finset.sum_range_succ, Finset.sum_range_succ, hprev] at hsucc
    exact Nat.add_left_cancel hsucc
  · have hprev_eq : mu.prefixSum i0 = lam.prefixSum i0 := hprefix_before i0 le_rfl
    have hprev_eq' :
        (∑ x ∈ Finset.range i0, mu.rowLen x) =
          ∑ x ∈ Finset.range i0, lam.rowLen x := hprev_eq
    rw [hk_eq, prefixSum, prefixSum, Finset.sum_range_succ, Finset.sum_range_succ,
      hprev_eq'] at hk
    exact Nat.lt_of_add_lt_add_left hk

lemma exists_rowLen_gt_of_rowLen_lt {n : ℕ} {mu lam : Nat.Partition n}
    (hlt : ∃ i : ℕ, mu.rowLen i < lam.rowLen i) :
    ∃ j : ℕ, lam.rowLen j < mu.rowLen j := by
  classical
  by_contra hnot
  push Not at hnot
  rcases hlt with ⟨i, hi⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hmuK : mu.prefixSum K = n := prefixSum_eq_of_colLen_le mu (le_max_left _ _)
  have hlamK : lam.prefixSum K = n := prefixSum_eq_of_colLen_le lam (le_max_right _ _)
  have hiK : i ∈ range K := by
    rw [mem_range]
    have hpos : 0 < lam.rowLen i := lt_of_le_of_lt (Nat.zero_le _) hi
    have hicol : i < (YoungDiagram.ofPartition lam).colLen 0 := by
      rwa [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    exact lt_of_lt_of_le hicol (le_max_right _ _)
  have hsumlt : mu.prefixSum K < lam.prefixSum K := by
    simp only [prefixSum]
    exact Finset.sum_lt_sum (fun r _ => hnot r) ⟨i, hiK, hi⟩
  omega

lemma exists_drop_target_of_first_row {n : ℕ} {mu lam : Nat.Partition n}
    {i0 : ℕ}
    (hbefore : ∀ r : ℕ, r < i0 → mu.rowLen r = lam.rowLen r)
    (hstrict : mu.rowLen i0 < lam.rowLen i0) :
    ∃ j : ℕ, i0 < j ∧ lam.rowLen j + 1 < lam.rowLen i0 := by
  rcases exists_rowLen_gt_of_rowLen_lt (mu := mu) (lam := lam) ⟨i0, hstrict⟩ with
    ⟨j, hj⟩
  have hi0j : i0 < j := by
    rcases lt_trichotomy j i0 with hji | hji | hji
    · have heq := hbefore j hji
      omega
    · subst j
      omega
    · exact hji
  refine ⟨j, hi0j, ?_⟩
  have hmu_le : mu.rowLen j ≤ mu.rowLen i0 :=
    (YoungDiagram.ofPartition mu).rowLen_anti i0 j hi0j.le
  omega

lemma exists_plateau_source {n : ℕ} (lam : Nat.Partition n) {i0 j : ℕ}
    (hi0j : i0 < j) (hjdrop : lam.rowLen j < lam.rowLen i0) :
    ∃ s : ℕ, i0 ≤ s ∧ s < j ∧ lam.rowLen s = lam.rowLen i0 ∧
      lam.rowLen (s + 1) < lam.rowLen s := by
  classical
  let P : ℕ → Prop := fun r => lam.rowLen r = lam.rowLen i0
  let s := Nat.findGreatest P (j - 1)
  have hi0_le_jpred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
  have hPi0 : P i0 := rfl
  have hsP : P s := Nat.findGreatest_spec (P := P) hi0_le_jpred hPi0
  have hi0s : i0 ≤ s := Nat.le_findGreatest (P := P) hi0_le_jpred hPi0
  have hsjpred : s ≤ j - 1 := Nat.findGreatest_le (P := P) (j - 1)
  have hsj : s < j := by omega
  refine ⟨s, hi0s, hsj, hsP, ?_⟩
  have hs_next_le : lam.rowLen (s + 1) ≤ lam.rowLen s :=
    (YoungDiagram.ofPartition lam).rowLen_anti s (s + 1) (Nat.le_succ s)
  apply lt_of_le_of_ne hs_next_le
  intro heq
  have hPnext : P (s + 1) := by
    dsimp [P]
    rw [heq, hsP]
  by_cases hsnext_j : s + 1 = j
  · have hjrow : lam.rowLen j = lam.rowLen i0 := by
      simpa [P, hsnext_j] using hPnext
    omega
  · have hsnext_lt_j : s + 1 < j := lt_of_le_of_ne (Nat.succ_le_iff.mpr hsj) hsnext_j
    have hsnext_le_jpred : s + 1 ≤ j - 1 := Nat.le_sub_one_of_lt hsnext_lt_j
    exact Nat.findGreatest_is_greatest (P := P) (by linarith : s < s + 1)
      hsnext_le_jpred hPnext

/-- The bottom row of the constant-height plateau starting at a first source row. -/
structure PlateauSourceData {n : ℕ} (lam : Nat.Partition n) (i0 j : ℕ) where
  s : ℕ
  hi0s : i0 ≤ s
  hsj : s < j
  hsrow : lam.rowLen s = lam.rowLen i0
  hsource : lam.rowLen (s + 1) < lam.rowLen s

lemma nonempty_plateauSourceData {n : ℕ} (lam : Nat.Partition n) {i0 j : ℕ}
    (hi0j : i0 < j) (hjdrop : lam.rowLen j < lam.rowLen i0) :
    Nonempty (PlateauSourceData lam i0 j) := by
  rcases exists_plateau_source lam hi0j hjdrop with
    ⟨s, hi0s, hsj, hsrow, hsource⟩
  exact ⟨{
    s := s
    hi0s := hi0s
    hsj := hsj
    hsrow := hsrow
    hsource := hsource
  }⟩


lemma prefixSum_succ_le_of_rowLen_le_of_rowLen_lt {n : ℕ} {mu lam : Nat.Partition n}
    {i0 k : ℕ} (hi0k : i0 < k)
    (hrow : ∀ r : ℕ, r < k → mu.rowLen r ≤ lam.rowLen r)
    (hstrict : mu.rowLen i0 < lam.rowLen i0) :
    mu.prefixSum k + 1 ≤ lam.prefixSum k := by
  have hi0mem : i0 ∈ range k := by simpa using hi0k
  rw [prefixSum, prefixSum]
  rw [← Finset.add_sum_erase (range k) (fun r => mu.rowLen r) hi0mem]
  rw [← Finset.add_sum_erase (range k) (fun r => lam.rowLen r) hi0mem]
  have hrest :
      ∑ r ∈ (range k).erase i0, mu.rowLen r ≤
        ∑ r ∈ (range k).erase i0, lam.rowLen r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hrow r (Finset.mem_range.mp (Finset.mem_erase.mp hr).2)
  omega

lemma prefixSum_add_two_le_of_rowLen_le_of_rowLen_add_two_le {n : ℕ}
    {mu lam : Nat.Partition n} {i0 k : ℕ} (hi0k : i0 < k)
    (hrow : ∀ r : ℕ, r < k → mu.rowLen r ≤ lam.rowLen r)
    (hstrict : mu.rowLen i0 + 2 ≤ lam.rowLen i0) :
    mu.prefixSum k + 2 ≤ lam.prefixSum k := by
  have hi0mem : i0 ∈ range k := by simpa using hi0k
  rw [prefixSum, prefixSum]
  rw [← Finset.add_sum_erase (range k) (fun r => mu.rowLen r) hi0mem]
  rw [← Finset.add_sum_erase (range k) (fun r => lam.rowLen r) hi0mem]
  have hrest :
      ∑ r ∈ (range k).erase i0, mu.rowLen r ≤
        ∑ r ∈ (range k).erase i0, lam.rowLen r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hrow r (Finset.mem_range.mp (Finset.mem_erase.mp hr).2)
  omega

lemma prefixSum_add_two_le_of_rowLen_le_of_two_rowLen_lt {n : ℕ}
    {mu lam : Nat.Partition n} {i₁ i₂ k : ℕ} (hi₁k : i₁ < k) (hi₂k : i₂ < k)
    (hne : i₁ ≠ i₂)
    (hrow : ∀ r : ℕ, r < k → mu.rowLen r ≤ lam.rowLen r)
    (hstrict₁ : mu.rowLen i₁ < lam.rowLen i₁)
    (hstrict₂ : mu.rowLen i₂ < lam.rowLen i₂) :
    mu.prefixSum k + 2 ≤ lam.prefixSum k := by
  have hi₁mem : i₁ ∈ range k := by simpa using hi₁k
  have hi₂mem : i₂ ∈ (range k).erase i₁ := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hne, by simpa using hi₂k⟩
  rw [prefixSum, prefixSum]
  rw [← Finset.add_sum_erase (range k) (fun r => mu.rowLen r) hi₁mem]
  rw [← Finset.add_sum_erase ((range k).erase i₁) (fun r => mu.rowLen r) hi₂mem]
  rw [← Finset.add_sum_erase (range k) (fun r => lam.rowLen r) hi₁mem]
  rw [← Finset.add_sum_erase ((range k).erase i₁) (fun r => lam.rowLen r) hi₂mem]
  have hrest :
      ∑ r ∈ ((range k).erase i₁).erase i₂, mu.rowLen r ≤
        ∑ r ∈ ((range k).erase i₁).erase i₂, lam.rowLen r := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' : r ∈ (range k).erase i₁ := (Finset.mem_erase.mp hr).2
    exact hrow r (Finset.mem_range.mp (Finset.mem_erase.mp hr').2)
  omega

lemma prefixSum_succ_add_one_le_of_prefixSum_add_two_le_of_rowLen_le_add_one
    {n : ℕ} {mu lam : Nat.Partition n} {j : ℕ}
    (hprefix : mu.prefixSum j + 2 ≤ lam.prefixSum j)
    (hrow : mu.rowLen j ≤ lam.rowLen j + 1) :
    mu.prefixSum (j + 1) + 1 ≤ lam.prefixSum (j + 1) := by
  rw [prefixSum, prefixSum, Finset.sum_range_succ, Finset.sum_range_succ]
  change mu.prefixSum j + mu.rowLen j + 1 ≤ lam.prefixSum j + lam.rowLen j
  omega

lemma rowLen_eq_of_not_prefixSum_add_two_le {n : ℕ} {mu lam : Nat.Partition n}
    {i0 r k : ℕ} (hi0k : i0 < k) (hrk : r < k) (hne : r ≠ i0)
    (hrow : ∀ a : ℕ, a < k → mu.rowLen a ≤ lam.rowLen a)
    (hstrict : mu.rowLen i0 < lam.rowLen i0)
    (hnot : ¬mu.prefixSum k + 2 ≤ lam.prefixSum k) :
    mu.rowLen r = lam.rowLen r := by
  apply le_antisymm (hrow r hrk)
  by_contra hlt_not
  have hlt : mu.rowLen r < lam.rowLen r := lt_of_not_ge hlt_not
  exact hnot (prefixSum_add_two_le_of_rowLen_le_of_two_rowLen_lt hi0k hrk
    (Ne.symm hne) hrow hstrict hlt)

lemma rowLen_mu_le_lam_before_target {n : ℕ} {mu lam : Nat.Partition n}
    {i0 j : ℕ}
    (hbefore : ∀ r : ℕ, r < i0 → mu.rowLen r = lam.rowLen r)
    (hstrict : mu.rowLen i0 < lam.rowLen i0)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j → ¬ lam.rowLen r + 1 < lam.rowLen i0) :
    ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r := by
  intro r hrj
  by_cases hri0 : r < i0
  · exact le_of_eq (hbefore r hri0)
  · have hi0r : i0 ≤ r := Nat.le_of_not_gt hri0
    have hmu_le : mu.rowLen r ≤ mu.rowLen i0 :=
      (YoungDiagram.ofPartition mu).rowLen_anti i0 r hi0r
    have hlam_lower : lam.rowLen i0 ≤ lam.rowLen r + 1 :=
      le_of_not_gt (hnoDrop r hi0r hrj)
    omega

/-- The first source row and first possible target row in a strict dominance interval. -/
structure FirstDropData {n : ℕ} (mu lam : Nat.Partition n) where
  i0 : ℕ
  j : ℕ
  hbefore : ∀ r : ℕ, r < i0 → mu.rowLen r = lam.rowLen r
  hstrict : mu.rowLen i0 < lam.rowLen i0
  hi0j : i0 < j
  hgap_i0 : lam.rowLen j + 1 < lam.rowLen i0
  hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j → ¬lam.rowLen r + 1 < lam.rowLen i0
  hrowBefore : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r

lemma nonempty_firstDropData_of_lt {n : ℕ} {mu lam : Nat.Partition n}
    (h : mu < lam) :
    Nonempty (FirstDropData mu lam) := by
  classical
  rcases exists_first_rowLen_lt_of_lt h with ⟨i0, hbefore, hstrict⟩
  let targetExists := exists_drop_target_of_first_row (mu := mu) (lam := lam)
    hbefore hstrict
  let j := Nat.find targetExists
  have hj_spec : i0 < j ∧ lam.rowLen j + 1 < lam.rowLen i0 :=
    Nat.find_spec targetExists
  have hi0j : i0 < j := hj_spec.1
  have hgap_i0 : lam.rowLen j + 1 < lam.rowLen i0 := hj_spec.2
  have hnoDrop :
      ∀ r : ℕ, i0 ≤ r → r < j → ¬lam.rowLen r + 1 < lam.rowLen i0 := by
    intro r hi0r hrj hdrop
    rcases eq_or_lt_of_le hi0r with rfl | hi0r_lt
    · omega
    · exact Nat.find_min targetExists hrj ⟨hi0r_lt, hdrop⟩
  exact ⟨{
    i0 := i0
    j := j
    hbefore := hbefore
    hstrict := hstrict
    hi0j := hi0j
    hgap_i0 := hgap_i0
    hnoDrop := hnoDrop
    hrowBefore := rowLen_mu_le_lam_before_target hbefore hstrict hnoDrop
  }⟩

namespace FirstDropData

variable {n : ℕ} {mu lam : Nat.Partition n} (D : FirstDropData mu lam)

lemma j_pos : 0 < D.j :=
  lt_of_le_of_lt (Nat.zero_le D.i0) D.hi0j

lemma pred_lt_j : D.j - 1 < D.j :=
  Nat.sub_one_lt_of_lt D.j_pos

lemma i0_le_pred : D.i0 ≤ D.j - 1 :=
  Nat.le_sub_one_of_lt D.hi0j

lemma rowLen_i0_le_pred_add_one :
    lam.rowLen D.i0 ≤ lam.rowLen (D.j - 1) + 1 :=
  le_of_not_gt (D.hnoDrop (D.j - 1) D.i0_le_pred D.pred_lt_j)

lemma rowLen_j_lt_pred :
    lam.rowLen D.j < lam.rowLen (D.j - 1) := by
  have hlower := D.rowLen_i0_le_pred_add_one
  have hgap := D.hgap_i0
  omega

end FirstDropData

lemma rowLen_eq_pred_of_source_lt_of_noDrop {n : ℕ} {lam : Nat.Partition n}
    {i0 s j r : ℕ} (hi0s : i0 ≤ s) (hsr : s < r) (hrj : r < j)
    (hsrow : lam.rowLen s = lam.rowLen i0)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j → ¬ lam.rowLen r + 1 < lam.rowLen i0) :
    lam.rowLen r = lam.rowLen s - 1 := by
  have hi0r : i0 ≤ r := le_trans hi0s hsr.le
  have hlower : lam.rowLen i0 ≤ lam.rowLen r + 1 :=
    le_of_not_gt (hnoDrop r hi0r hrj)
  have hupper : lam.rowLen r < lam.rowLen i0 := by
    have hs1r : s + 1 ≤ r := Nat.succ_le_iff.mpr hsr
    have hr_le_s1 : lam.rowLen r ≤ lam.rowLen (s + 1) :=
      (YoungDiagram.ofPartition lam).rowLen_anti (s + 1) r hs1r
    omega
  omega

lemma prefix_surplus_of_rowLen_le_before_target {n : ℕ} {mu lam : Nat.Partition n}
    {i0 s j : ℕ} (hi0s : i0 ≤ s)
    (hrow : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r)
    (hstrict : mu.rowLen i0 < lam.rowLen i0) :
    ∀ k : ℕ, s < k → k ≤ j → mu.prefixSum k + 1 ≤ lam.prefixSum k := by
  intro k hsk hkj
  apply prefixSum_succ_le_of_rowLen_le_of_rowLen_lt (i0 := i0)
  · exact lt_of_le_of_lt hi0s hsk
  · intro r hrk
    exact hrow r (lt_of_lt_of_le hrk hkj)
  · exact hstrict

lemma prefix_surplus₂_of_rowLen_le_before_target_of_add_two_le {n : ℕ}
    {mu lam : Nat.Partition n} {i0 s j : ℕ} (hi0s : i0 ≤ s)
    (hrow : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r)
    (hstrict : mu.rowLen i0 + 2 ≤ lam.rowLen i0) :
    ∀ k : ℕ, s < k → k ≤ j → mu.prefixSum k + 2 ≤ lam.prefixSum k := by
  intro k hsk hkj
  apply prefixSum_add_two_le_of_rowLen_le_of_rowLen_add_two_le (i0 := i0)
  · exact lt_of_le_of_lt hi0s hsk
  · intro r hrk
    exact hrow r (lt_of_lt_of_le hrk hkj)
  · exact hstrict

lemma prefix_surplus₂_of_rowLen_le_before_target_of_two_rowLen_lt {n : ℕ}
    {mu lam : Nat.Partition n} {i₁ i₂ s j : ℕ} (hi₁s : i₁ ≤ s)
    (hi₂s : i₂ ≤ s) (hne : i₁ ≠ i₂)
    (hrow : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r)
    (hstrict₁ : mu.rowLen i₁ < lam.rowLen i₁)
    (hstrict₂ : mu.rowLen i₂ < lam.rowLen i₂) :
    ∀ k : ℕ, s < k → k ≤ j → mu.prefixSum k + 2 ≤ lam.prefixSum k := by
  intro k hsk hkj
  apply prefixSum_add_two_le_of_rowLen_le_of_two_rowLen_lt (i₁ := i₁) (i₂ := i₂)
  · exact lt_of_le_of_lt hi₁s hsk
  · exact lt_of_le_of_lt hi₂s hsk
  · exact hne
  · intro r hrk
    exact hrow r (lt_of_lt_of_le hrk hkj)
  · exact hstrict₁
  · exact hstrict₂

lemma prefix_surplus₂_of_first_lt_source {n : ℕ} {mu lam : Nat.Partition n}
    {i0 s j : ℕ} (hstrict : mu.rowLen i0 < lam.rowLen i0) (hi0s : i0 ≤ s)
    (hi0_lt_s : i0 < s) (hsrow : lam.rowLen s = lam.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j → mu.rowLen r ≤ lam.rowLen r) :
    ∀ k : ℕ, s < k → k ≤ j → mu.prefixSum k + 2 ≤ lam.prefixSum k := by
  have hi0s_succ : i0 + 1 ≤ s := Nat.succ_le_iff.mpr hi0_lt_s
  have hrow_succ : lam.rowLen (i0 + 1) = lam.rowLen i0 := by
    have hle₁ : lam.rowLen (i0 + 1) ≤ lam.rowLen i0 :=
      (YoungDiagram.ofPartition lam).rowLen_anti i0 (i0 + 1) (Nat.le_succ i0)
    have hle₂ : lam.rowLen s ≤ lam.rowLen (i0 + 1) :=
      (YoungDiagram.ofPartition lam).rowLen_anti (i0 + 1) s hi0s_succ
    omega
  have hstrict_succ : mu.rowLen (i0 + 1) < lam.rowLen (i0 + 1) := by
    have hmu_le : mu.rowLen (i0 + 1) ≤ mu.rowLen i0 :=
      (YoungDiagram.ofPartition mu).rowLen_anti i0 (i0 + 1) (Nat.le_succ i0)
    omega
  exact prefix_surplus₂_of_rowLen_le_before_target_of_two_rowLen_lt
    (i₁ := i0) (i₂ := i0 + 1) (s := s) (j := j) hi0s hi0s_succ
    (by omega) hrowBefore hstrict hstrict_succ

end Nat.Partition
