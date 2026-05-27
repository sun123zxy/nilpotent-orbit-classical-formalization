import NilpotentOrbitClassicalFormalization.Dominance.CoverA

/-!
# Classical-type admissible partitions

This file records the parity condition for C-type nilpotent orbits and the
corresponding subtype of admissible partitions.
-/

namespace Nat.Partition

/-- C-type admissibility: every odd row length occurs with even multiplicity. -/
def IsCPartition {N : ℕ} (p : Nat.Partition N) : Prop :=
  ∀ m : ℕ, Odd m → Even (p.parts.count m)

/-- C-type admissible partitions of `2 * n`. -/
abbrev CPartition (n : ℕ) := {p : Nat.Partition (2 * n) // IsCPartition p}

lemma rowLens_count_eq_parts_count {N : ℕ} (p : Nat.Partition N) (m : ℕ) :
    ((YoungDiagram.ofPartition p).rowLens.count m) = p.parts.count m := by
  rw [← Multiset.coe_count]
  exact congrArg (fun s : Multiset ℕ => s.count m)
    (YoungDiagram.rowLens_ofPartition_eq_parts p)

lemma parts_count_eq_rowLens_count {N : ℕ} (p : Nat.Partition N) (m : ℕ) :
    p.parts.count m = ((YoungDiagram.ofPartition p).rowLens.count m) :=
  (rowLens_count_eq_parts_count p m).symm

lemma rowLens_count_even_of_isCPartition {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) {m : ℕ} (hodd : Odd m) :
    Even ((YoungDiagram.ofPartition p).rowLens.count m) := by
  rw [rowLens_count_eq_parts_count]
  exact hp m hodd

lemma cPartition_le_iff {n : ℕ} {mu lam : CPartition n} :
    mu ≤ lam ↔ (mu : Nat.Partition (2 * n)) ≤ lam :=
  Iff.rfl

lemma cPartition_lt_iff {n : ℕ} {mu lam : CPartition n} :
    mu < lam ↔ (mu : Nat.Partition (2 * n)) < lam :=
  Iff.rfl

lemma CPartition.covBy_of_covBy_val {n : ℕ} {mu lam : CPartition n}
    (h : (mu : Nat.Partition (2 * n)) ⋖ lam) :
    mu ⋖ lam := by
  rw [covBy_iff_lt_and_eq_or_eq]
  refine ⟨h.1, ?_⟩
  intro nu hmu_le_nu hnu_le_lam
  rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
  · left
    exact Subtype.ext hnu_eq_mu
  · right
    exact Subtype.ext hnu_eq_lam

lemma CPartition.eq_of_between {n : ℕ} {mu lam nu : CPartition n}
    (h : mu ⋖ lam) (hmu_le_nu : mu ≤ nu) (hnu_le_lam : nu ≤ lam)
    (hnu_ne_lam : nu ≠ lam) :
    nu = mu := by
  rcases h.eq_or_eq hmu_le_nu hnu_le_lam with hnu_eq_mu | hnu_eq_lam
  · exact hnu_eq_mu
  · exact False.elim (hnu_ne_lam hnu_eq_lam)

lemma rowLen_mem_rowLens_of_pos {N : ℕ} (p : Nat.Partition N) {i : ℕ}
    (hpos : 0 < p.rowLen i) :
    p.rowLen i ∈ (YoungDiagram.ofPartition p).rowLens := by
  rw [YoungDiagram.rowLens, List.mem_map]
  refine ⟨i, ?_, rfl⟩
  rw [List.mem_range, ← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  exact hpos

lemma rowLens_count_eq_card_filter {N : ℕ} (p : Nat.Partition N) (m : ℕ) :
    ((YoungDiagram.ofPartition p).rowLens.count m) =
      ((Finset.range ((YoungDiagram.ofPartition p).colLen 0)).filter
        fun i => p.rowLen i = m).card := by
  rw [YoungDiagram.rowLens]
  change (List.map p.rowLen (List.range ((YoungDiagram.ofPartition p).colLen 0))).count m = _
  generalize (YoungDiagram.ofPartition p).colLen 0 = c
  induction c with
  | zero => simp
  | succ c ih =>
      rw [List.range_succ, List.map_append, List.count_append, ih]
      have hrange : Finset.range (c + 1) = insert c (Finset.range c) := by
        ext x
        rw [Finset.mem_range, Finset.mem_insert, Finset.mem_range]
        omega
      rw [hrange]
      by_cases h : p.rowLen c = m
      · rw [Finset.filter_insert]
        simp [h]
      · rw [Finset.filter_insert]
        simp [h]

lemma rowLens_count_eq_card_filter_range {N : ℕ} (p : Nat.Partition N)
    {K m : ℕ} (hK : (YoungDiagram.ofPartition p).colLen 0 ≤ K) (hmpos : 0 < m) :
    ((YoungDiagram.ofPartition p).rowLens.count m) =
      ((Finset.range K).filter fun i => p.rowLen i = m).card := by
  rw [rowLens_count_eq_card_filter p m]
  congr 1
  ext i
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hrow⟩
    exact ⟨by simpa using lt_of_lt_of_le (Finset.mem_range.mp hi) hK, hrow⟩
  · rintro ⟨hiK, hrow⟩
    refine ⟨?_, hrow⟩
    rw [Finset.mem_range]
    by_contra hle
    have hz := rowLen_eq_zero_of_colLen_le p (Nat.le_of_not_gt hle)
    omega

lemma rowLens_count_eq_one_of_isolated {N : ℕ} (p : Nat.Partition N) {i m : ℕ}
    (hi : p.rowLen i = m) (hpos : 0 < m)
    (hprev : i = 0 ∨ p.rowLen (i - 1) ≠ m)
    (hnext : p.rowLen (i + 1) < m) :
    ((YoungDiagram.ofPartition p).rowLens.count m) = 1 := by
  rw [rowLens_count_eq_card_filter p m]
  have hirange : i ∈ Finset.range ((YoungDiagram.ofPartition p).colLen 0) := by
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    change 0 < p.rowLen i
    rwa [hi]
  have hfilter :
      ((Finset.range ((YoungDiagram.ofPartition p).colLen 0)).filter
        fun r => p.rowLen r = m) = {i} := by
    ext r
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hrange, hr⟩
      rcases lt_trichotomy r i with hri | rfl | hir
      · rcases hprev with hi0 | hprev_ne
        · omega
        · have hpred_gt : m < p.rowLen (i - 1) := by
            have hle : m ≤ p.rowLen (i - 1) := by
              rw [← hi]
              exact (YoungDiagram.ofPartition p).rowLen_anti (i - 1) i (by omega)
            exact lt_of_le_of_ne hle (Ne.symm hprev_ne)
          have hr_ge : p.rowLen (i - 1) ≤ p.rowLen r :=
            (YoungDiagram.ofPartition p).rowLen_anti r (i - 1) (by omega)
          omega
      · rfl
      · have hr_le : p.rowLen r ≤ p.rowLen (i + 1) :=
          (YoungDiagram.ofPartition p).rowLen_anti (i + 1) r (by omega)
        omega
    · intro rfl
      exact ⟨hirange, hi⟩
  rw [hfilter]
  simp

/--
In a C-partition, an odd row length cannot occur as an isolated bottom row of its
constant-height plateau.
-/
lemma exists_prev_rowLen_eq_of_odd_of_next_lt {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) {i : ℕ} (hodd : Odd (p.rowLen i))
    (hnext : p.rowLen (i + 1) < p.rowLen i) :
    0 < i ∧ p.rowLen (i - 1) = p.rowLen i := by
  by_contra hbad
  have hprev : i = 0 ∨ p.rowLen (i - 1) ≠ p.rowLen i := by
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · refine Or.inr ?_
      intro heq
      exact hbad ⟨Nat.pos_of_ne_zero hi0, heq⟩
  have hcount :
      ((YoungDiagram.ofPartition p).rowLens.count (p.rowLen i)) = 1 :=
    rowLens_count_eq_one_of_isolated p rfl hodd.pos hprev hnext
  have heven := rowLens_count_even_of_isCPartition hp hodd
  rw [hcount] at heven
  exact Nat.not_even_one heven

/--
In a C-partition, an odd row length cannot occur as an isolated top row of its
constant-height plateau.
-/
lemma next_rowLen_eq_of_odd_of_prev_lt {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) {i : ℕ} (hodd : Odd (p.rowLen i))
    (hprev : p.rowLen i < p.rowLen (i - 1)) :
    p.rowLen (i + 1) = p.rowLen i := by
  by_contra hbad
  have hnext_le : p.rowLen (i + 1) ≤ p.rowLen i :=
    (YoungDiagram.ofPartition p).rowLen_anti i (i + 1) (Nat.le_succ i)
  have hnext : p.rowLen (i + 1) < p.rowLen i :=
    lt_of_le_of_ne hnext_le hbad
  have hcount :
      ((YoungDiagram.ofPartition p).rowLens.count (p.rowLen i)) = 1 :=
    rowLens_count_eq_one_of_isolated p rfl hodd.pos
      (Or.inr (ne_of_gt hprev)) hnext
  have heven := rowLens_count_even_of_isCPartition hp hodd
  rw [hcount] at heven
  exact Nat.not_even_one heven

/-- Count a whole constant-height plateau in the row-length list. -/
lemma rowLens_count_eq_sub_of_plateau {N : ℕ} (p : Nat.Partition N)
    {a b m : ℕ}
    (hrow : ∀ r : ℕ, a ≤ r → r < b → p.rowLen r = m)
    (hprev : a = 0 ∨ m < p.rowLen (a - 1))
    (hnext : p.rowLen b < m) :
    ((YoungDiagram.ofPartition p).rowLens.count m) = b - a := by
  rw [rowLens_count_eq_card_filter p m]
  have hmpos : 0 < m := by omega
  have hfilter :
      ((Finset.range ((YoungDiagram.ofPartition p).colLen 0)).filter
        fun r => p.rowLen r = m) = Finset.Ico a b := by
    ext r
    rw [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨_, hr⟩
      constructor
      · by_contra hra
        have hra_le : r ≤ a - 1 := by omega
        rcases hprev with ha0 | hprev_lt
        · omega
        · have hle : p.rowLen (a - 1) ≤ p.rowLen r :=
            (YoungDiagram.ofPartition p).rowLen_anti r (a - 1) hra_le
          omega
      · by_contra hbr
        have hle : p.rowLen r ≤ p.rowLen b :=
          (YoungDiagram.ofPartition p).rowLen_anti b r (by omega)
        omega
    · rintro ⟨har, hrb⟩
      have hrange : r ∈ Finset.range ((YoungDiagram.ofPartition p).colLen 0) := by
        rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen,
          YoungDiagram.mem_iff_lt_rowLen]
        change 0 < p.rowLen r
        rw [hrow r har hrb]
        exact hmpos
      exact ⟨hrange, hrow r har hrb⟩
  rw [hfilter, Nat.card_Ico]

lemma even_sub_of_odd_plateau {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) {a b m : ℕ} (hodd : Odd m)
    (hrow : ∀ r : ℕ, a ≤ r → r < b → p.rowLen r = m)
    (hprev : a = 0 ∨ m < p.rowLen (a - 1))
    (hnext : p.rowLen b < m) :
    Even (b - a) := by
  have hcount := rowLens_count_eq_sub_of_plateau p hrow hprev hnext
  rw [← hcount]
  exact rowLens_count_even_of_isCPartition hp hodd

/-- Choose the top row of the constant-height plateau ending at `k`. -/
lemma exists_plateau_start {N : ℕ} (p : Nat.Partition N) {k : ℕ} :
    ∃ a : ℕ, a ≤ k ∧ p.rowLen a = p.rowLen k ∧
      (∀ r : ℕ, a ≤ r → r ≤ k → p.rowLen r = p.rowLen k) ∧
      (a = 0 ∨ p.rowLen k < p.rowLen (a - 1)) := by
  classical
  let P : ℕ → Prop := fun r => r ≤ k ∧ p.rowLen r = p.rowLen k
  let a := Nat.find (show ∃ r, P r from ⟨k, le_rfl, rfl⟩)
  have haP : P a := Nat.find_spec (show ∃ r, P r from ⟨k, le_rfl, rfl⟩)
  refine ⟨a, haP.1, haP.2, ?_, ?_⟩
  · intro r har hrk
    have hle₁ : p.rowLen r ≤ p.rowLen a :=
      (YoungDiagram.ofPartition p).rowLen_anti a r har
    have hle₂ : p.rowLen k ≤ p.rowLen r :=
      (YoungDiagram.ofPartition p).rowLen_anti r k hrk
    omega
  · by_cases ha0 : a = 0
    · exact Or.inl ha0
    · refine Or.inr ?_
      have hapred_lt : a - 1 < a := Nat.sub_one_lt_of_lt (Nat.pos_of_ne_zero ha0)
      have hnotP :
          ¬P (a - 1) :=
        Nat.find_min (show ∃ r, P r from ⟨k, le_rfl, rfl⟩) hapred_lt
      have hle : p.rowLen k ≤ p.rowLen (a - 1) := by
        have hpred_le_a : a - 1 ≤ a := by omega
        have hrow : p.rowLen a ≤ p.rowLen (a - 1) :=
          (YoungDiagram.ofPartition p).rowLen_anti (a - 1) a hpred_le_a
        rw [haP.2] at hrow
        exact hrow
      exact lt_of_le_of_ne hle (by
        intro hEq
        apply hnotP
        constructor
        · omega
        · exact hEq.symm)

/--
In a C-partition, the prefix ending at the bottom of a constant-height plateau has
even total size.
-/
lemma even_prefixSum_of_next_lt {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) :
    ∀ k : ℕ, p.rowLen (k + 1) < p.rowLen k → Even (p.prefixSum (k + 1)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hnext
      rcases exists_plateau_start p (k := k) with
        ⟨a, hak, harow, hplateau, hprev⟩
      have hprefix_a : Even (p.prefixSum a) := by
        by_cases ha0 : a = 0
        · subst a
          simp [prefixSum]
        · have hapred_lt_k : a - 1 < k := by omega
          have hdrop_prev : p.rowLen ((a - 1) + 1) < p.rowLen (a - 1) := by
            have ha_eq : (a - 1) + 1 = a := Nat.sub_add_cancel (Nat.pos_of_ne_zero ha0)
            rcases hprev with hzero | hprev_lt
            · omega
            · rw [ha_eq]
              rw [harow]
              exact hprev_lt
          have hprev_even := ih (a - 1) hapred_lt_k hdrop_prev
          rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero ha0)] at hprev_even
      have hsplit :
          Finset.range (k + 1) = Finset.range a ∪ Finset.Ico a (k + 1) := by
        ext x
        rw [Finset.mem_range, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
      have hdisjoint : Disjoint (Finset.range a) (Finset.Ico a (k + 1)) := by
        rw [Finset.disjoint_left]
        intro x hxrange hxIco
        rw [Finset.mem_range] at hxrange
        rw [Finset.mem_Ico] at hxIco
        omega
      have hrowIco : ∀ r ∈ Finset.Ico a (k + 1), p.rowLen r = p.rowLen k := by
        intro r hr
        rw [Finset.mem_Ico] at hr
        exact hplateau r hr.1 (by omega)
      have hsumIco :
          (∑ r ∈ Finset.Ico a (k + 1), p.rowLen r) =
            ((k + 1) - a) * p.rowLen k := by
        calc
          (∑ r ∈ Finset.Ico a (k + 1), p.rowLen r)
              = ∑ r ∈ Finset.Ico a (k + 1), p.rowLen k := by
                apply Finset.sum_congr rfl
                intro r hr
                exact hrowIco r hr
          _ = ((Finset.Ico a (k + 1)).card) * p.rowLen k := by simp
          _ = ((k + 1) - a) * p.rowLen k := by rw [Nat.card_Ico]
      rw [prefixSum, hsplit, Finset.sum_union hdisjoint]
      change Even (p.prefixSum a + ∑ x ∈ Finset.Ico a (k + 1), p.rowLen x)
      rw [hsumIco]
      have hplateauEven : Even (((k + 1) - a) * p.rowLen k) := by
        rcases Nat.even_or_odd (p.rowLen k) with hm_even | hm_odd
        · rcases hm_even with ⟨c, hc⟩
          refine ⟨((k + 1) - a) * c, ?_⟩
          rw [hc]
          ring
        · have hrow_plateau :
              ∀ r : ℕ, a ≤ r → r < k + 1 → p.rowLen r = p.rowLen k := by
            intro r har hrk
            exact hplateau r har (by omega)
          have hcount_even : Even ((k + 1) - a) := by
            have hcount := even_sub_of_odd_plateau (p := p) (a := a) (b := k + 1)
              (m := p.rowLen k) hp hm_odd hrow_plateau hprev hnext
            simpa using hcount
          rcases hcount_even with ⟨c, hc⟩
          refine ⟨c * p.rowLen k, ?_⟩
          rw [hc]
          ring
      exact Even.add hprefix_a hplateauEven

/-- At the first row of an odd plateau, the prefix including that row is odd. -/
lemma odd_prefixSum_succ_of_odd_of_prev_lt {N : ℕ} {p : Nat.Partition N}
    (hp : IsCPartition p) {j : ℕ} (hodd : Odd (p.rowLen j))
    (hprev : p.rowLen j < p.rowLen (j - 1)) :
    Odd (p.prefixSum (j + 1)) := by
  have hjpos : 0 < j := by
    by_contra hnot
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hnot
    subst j
    simp at hprev
  have heven_prev : Even (p.prefixSum ((j - 1) + 1)) :=
    even_prefixSum_of_next_lt hp (j - 1) (by
      rw [Nat.sub_add_cancel hjpos]
      exact hprev)
  rw [Nat.sub_add_cancel hjpos] at heven_prev
  rw [prefixSum_succ]
  rcases heven_prev with ⟨a, ha⟩
  rcases hodd with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  omega

end Nat.Partition
