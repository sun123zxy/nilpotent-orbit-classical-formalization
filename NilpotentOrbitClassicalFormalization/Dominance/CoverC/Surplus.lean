import NilpotentOrbitClassicalFormalization.Dominance.CoverC.Moves

/-!
# C-type cover surplus lemmas

Split from `Dominance/CoverC.lean` to keep the C-type cover formalization navigable.
-/

namespace Nat.Partition


lemma CPartition.isCMove_of_between {n : ℕ} {mu lam nu : CPartition n}
    (h : mu ⋖ lam) (hmu_le_nu : mu ≤ nu) (hnu_le_lam : nu ≤ lam)
    (hnu_ne_lam : nu ≠ lam) (hmove : IsCMove lam nu) :
    IsCMove lam mu := by
  have hnu_eq_mu := CPartition.eq_of_between h hmu_le_nu hnu_le_lam hnu_ne_lam
  subst nu
  exact hmove

lemma CPartition.two_lt_target_sub_two_of_even_source {n : ℕ} {lam : CPartition n}
    {i0 s j : ℕ} (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition (2 * n)).rowLen r + 1 < lam.val.rowLen i0)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hlarge : (lam : Nat.Partition (2 * n)).rowLen j + 2 < lam.val.rowLen s) :
    s < j - 2 := by
  have hle : s + 2 ≤ j := by omega
  rcases lt_or_eq_of_le hle with hlt | hEq
  · omega
  · let m := (lam : Nat.Partition (2 * n)).rowLen s - 1
    have hmrow : ∀ r : ℕ, s + 1 ≤ r → r < j →
        (lam : Nat.Partition (2 * n)).rowLen r = m := by
      intro r hsr hrj
      dsimp [m]
      exact Nat.Partition.rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) hrj
        hsrow hsource hnoDrop
    have hmodd : Odd m := by
      rcases hseven with ⟨a, ha⟩
      dsimp [m]
      refine ⟨a - 1, ?_⟩
      have hpos : 0 < (lam : Nat.Partition (2 * n)).rowLen s := by omega
      omega
    have hprev : m < (lam : Nat.Partition (2 * n)).rowLen ((s + 1) - 1) := by
      dsimp [m]
      omega
    have hnext : (lam : Nat.Partition (2 * n)).rowLen j < m := by
      dsimp [m]
      omega
    have hcount_even :
        Even (j - (s + 1)) :=
      even_sub_of_odd_plateau (p := (lam : Nat.Partition (2 * n))) (a := s + 1)
        (b := j) (m := m) lam.property hmodd hmrow (Or.inr hprev) hnext
    have hcount_one : j - (s + 1) = 1 := by omega
    rw [hcount_one] at hcount_even
    exact False.elim (Nat.not_even_one hcount_even)

lemma CPartition.first_strict_lt_odd_plateau_bottom {n : ℕ} {mu lam : CPartition n}
    {i0 s : ℕ}
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hi0s : i0 ≤ s)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s)) :
    i0 < s := by
  rcases lt_or_eq_of_le hi0s with hi0s_lt | hi0s_eq
  · exact hi0s_lt
  · subst i0
    let m := (lam : Nat.Partition (2 * n)).rowLen s
    have hmpos : 0 < m := by
      dsimp [m]
      exact hsodd.pos
    have hmu_s_lt : (mu : Nat.Partition (2 * n)).rowLen s < m := by
      dsimp [m] at hstrict ⊢
      simpa using hstrict
    let K := max ((YoungDiagram.ofPartition (mu : Nat.Partition (2 * n))).colLen 0)
      ((YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).colLen 0)
    let muRows :=
      (Finset.range K).filter fun r => (mu : Nat.Partition (2 * n)).rowLen r = m
    let lamRows :=
      (Finset.range K).filter fun r => (lam : Nat.Partition (2 * n)).rowLen r = m
    have hcount_mu :
        ((YoungDiagram.ofPartition (mu : Nat.Partition (2 * n))).rowLens.count m) =
          muRows.card := by
      dsimp [muRows, K]
      exact rowLens_count_eq_card_filter_range (mu : Nat.Partition (2 * n))
        (le_max_left _ _) hmpos
    have hcount_lam :
        ((YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).rowLens.count m) =
          lamRows.card := by
      dsimp [lamRows, K]
      exact rowLens_count_eq_card_filter_range (lam : Nat.Partition (2 * n))
        (le_max_right _ _) hmpos
    have hs_lam : s ∈ lamRows := by
      dsimp [lamRows, K, m]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        exact lt_of_lt_of_le
          (by
            rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
            exact hmpos)
          (le_max_right _ _)
      · rfl
    have hfilters : muRows = lamRows.erase s := by
      ext r
      dsimp [muRows, lamRows, K]
      rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨hrange, hmurow⟩
        refine ⟨?_, hrange, ?_⟩
        · intro hrs
          subst r
          omega
        · rcases lt_trichotomy r s with hrs | rfl | hsr
          · rw [← hbefore r hrs]
            exact hmurow
          · omega
          · have hmu_le : (mu : Nat.Partition (2 * n)).rowLen r ≤
                (mu : Nat.Partition (2 * n)).rowLen s :=
              (YoungDiagram.ofPartition (mu : Nat.Partition (2 * n))).rowLen_anti s r hsr.le
            omega
      · rintro ⟨hrs_ne, hrange, hlamrow⟩
        refine ⟨hrange, ?_⟩
        rcases lt_trichotomy r s with hrs | rfl | hsr
        · rw [hbefore r hrs]
          exact hlamrow
        · exact False.elim (hrs_ne rfl)
        · have hlam_le : (lam : Nat.Partition (2 * n)).rowLen r ≤
              (lam : Nat.Partition (2 * n)).rowLen (s + 1) :=
            (YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).rowLen_anti
              (s + 1) r (by omega)
          omega
    have hcard_mu : muRows.card = lamRows.card - 1 := by
      rw [hfilters]
      exact Finset.card_erase_of_mem hs_lam
    have hmu_even : Even muRows.card := by
      rw [← hcount_mu]
      exact rowLens_count_even_of_isCPartition mu.property (by simpa [m] using hsodd)
    have hlam_even : Even lamRows.card := by
      rw [← hcount_lam]
      exact rowLens_count_even_of_isCPartition lam.property (by simpa [m] using hsodd)
    rcases hmu_even with ⟨a, ha⟩
    rcases hlam_even with ⟨b, hb⟩
    have hlam_pos : 0 < lamRows.card := Finset.card_pos.mpr ⟨s, hs_lam⟩
    rw [ha, hb] at hcard_mu
    rw [hb] at hlam_pos
    omega

lemma CPartition.prefix_surplus₂_of_odd_source {n : ℕ} {mu lam : CPartition n}
    {i0 s j : ℕ}
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hi0s : i0 ≤ s)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r) :
    ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
  have hi0s_lt : i0 < s :=
    CPartition.first_strict_lt_odd_plateau_bottom hbefore hstrict hi0s hsrow hsource hsodd
  have hi0s_succ : i0 + 1 ≤ s := Nat.succ_le_iff.mpr hi0s_lt
  have hrow_succ : (lam : Nat.Partition (2 * n)).rowLen (i0 + 1) =
      lam.val.rowLen i0 := by
    have hle₁ : (lam : Nat.Partition (2 * n)).rowLen (i0 + 1) ≤ lam.val.rowLen i0 :=
      (YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).rowLen_anti
        i0 (i0 + 1) (Nat.le_succ i0)
    have hle₂ : (lam : Nat.Partition (2 * n)).rowLen s ≤ lam.val.rowLen (i0 + 1) :=
      (YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).rowLen_anti
        (i0 + 1) s hi0s_succ
    omega
  have hstrict_succ :
      (mu : Nat.Partition (2 * n)).rowLen (i0 + 1) <
        lam.val.rowLen (i0 + 1) := by
    have hmu_le : (mu : Nat.Partition (2 * n)).rowLen (i0 + 1) ≤
        (mu : Nat.Partition (2 * n)).rowLen i0 :=
      (YoungDiagram.ofPartition (mu : Nat.Partition (2 * n))).rowLen_anti
        i0 (i0 + 1) (Nat.le_succ i0)
    omega
  exact prefix_surplus₂_of_rowLen_le_before_target_of_two_rowLen_lt
    (i₁ := i0) (i₂ := i0 + 1) (s := s) (j := j) hi0s hi0s_succ
    (by omega) hrowBefore hstrict hstrict_succ

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

lemma CPartition.prefix_surplus₂_of_even_source_adjacent {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ}
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hi0s : i0 ≤ s) (hj : j = s + 1)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s) :
    ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
  intro k hsk hkj
  have hk : k = j := by omega
  subst k
  by_cases hi0_lt_s : i0 < s
  · exact prefix_surplus₂_of_first_lt_source hstrict hi0s hi0_lt_s hsrow
      hrowBefore j hsk le_rfl
  · have hi0_eq_s : i0 = s := by omega
    subst i0
    have hone : (mu : Nat.Partition (2 * n)).prefixSum j + 1 ≤ lam.val.prefixSum j :=
      (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict) j hsk le_rfl
    by_contra hnot
    have hEq : lam.val.prefixSum j = (mu : Nat.Partition (2 * n)).prefixSum j + 1 := by
      omega
    subst j
    have hprefix_s : (mu : Nat.Partition (2 * n)).prefixSum s = lam.val.prefixSum s := by
      rw [prefixSum, prefixSum]
      apply Finset.sum_congr rfl
      intro r hr
      exact hbefore r (Finset.mem_range.mp hr)
    have hmu_s : (mu : Nat.Partition (2 * n)).rowLen s + 1 =
        (lam : Nat.Partition (2 * n)).rowLen s := by
      rw [prefixSum_succ, prefixSum_succ, hprefix_s] at hEq
      omega
    have hmu_next_le : (mu : Nat.Partition (2 * n)).rowLen (s + 1) ≤
        (lam : Nat.Partition (2 * n)).rowLen (s + 1) + 1 := by
      have hle2 := hmu_le_lam (s + 2)
      rw [prefixSum_succ (mu : Nat.Partition (2 * n)) (s + 1),
        prefixSum_succ (lam : Nat.Partition (2 * n)) (s + 1)] at hle2
      rw [hEq] at hle2
      omega
    have hmu_drop : (mu : Nat.Partition (2 * n)).rowLen (s + 1) <
        (mu : Nat.Partition (2 * n)).rowLen s := by
      omega
    have heven_mu : Even ((mu : Nat.Partition (2 * n)).prefixSum (s + 1)) :=
      even_prefixSum_of_next_lt mu.property s hmu_drop
    have heven_lam : Even ((lam : Nat.Partition (2 * n)).prefixSum (s + 1)) :=
      even_prefixSum_of_next_lt lam.property s hsource
    rw [hEq] at heven_lam
    rcases heven_mu with ⟨a, ha⟩
    rcases heven_lam with ⟨b, hb⟩
    omega

lemma CPartition.prefix_surplus₂_of_even_source_nonadjacent {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ}
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s) :
    ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
  intro k hjk hkj
  have hk : k = j := by omega
  subst k
  by_cases hi0_lt_s : i0 < s
  · exact prefix_surplus₂_of_first_lt_source hstrict hi0s hi0_lt_s hsrow
      hrowBefore j (by omega) le_rfl
  · have hi0_eq_s : i0 = s := by omega
    subst i0
    have hone : (mu : Nat.Partition (2 * n)).prefixSum j + 1 ≤ lam.val.prefixSum j :=
      (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict) j
        (by omega) le_rfl
    by_contra hnot
    have hEq : lam.val.prefixSum j = (mu : Nat.Partition (2 * n)).prefixSum j + 1 := by
      omega
    have hpred_eq : (mu : Nat.Partition (2 * n)).rowLen (j - 1) =
        (lam : Nat.Partition (2 * n)).rowLen (j - 1) :=
      rowLen_eq_of_not_prefixSum_add_two_le (i0 := s) (k := j)
        (by omega) (by omega) (by omega) hrowBefore hstrict hnot
    have hmu_j_le : (mu : Nat.Partition (2 * n)).rowLen j ≤
        (lam : Nat.Partition (2 * n)).rowLen j + 1 := by
      have hle2 := hmu_le_lam (j + 1)
      rw [prefixSum_succ (mu : Nat.Partition (2 * n)) j,
        prefixSum_succ (lam : Nat.Partition (2 * n)) j] at hle2
      rw [hEq] at hle2
      omega
    have hmu_drop : (mu : Nat.Partition (2 * n)).rowLen ((j - 1) + 1) <
        (mu : Nat.Partition (2 * n)).rowLen (j - 1) := by
      rw [Nat.sub_add_cancel (by omega : 0 < j)]
      rw [hpred_eq, hrow_mid]
      omega
    have heven_mu : Even ((mu : Nat.Partition (2 * n)).prefixSum ((j - 1) + 1)) :=
      even_prefixSum_of_next_lt mu.property (j - 1) hmu_drop
    have heven_lam : Even ((lam : Nat.Partition (2 * n)).prefixSum ((j - 1) + 1)) :=
      even_prefixSum_of_next_lt lam.property (j - 1) (by
        rw [Nat.sub_add_cancel (by omega : 0 < j)]
        exact htarget)
    rw [Nat.sub_add_cancel (by omega : 0 < j)] at heven_mu heven_lam
    rw [hEq] at heven_lam
    rcases heven_mu with ⟨a, ha⟩
    rcases heven_lam with ⟨b, hb⟩
    omega

lemma CPartition.prefix_surplus_right_of_odd_target {n : ℕ} {mu lam : CPartition n}
    {j : ℕ}
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hprefix : (mu : Nat.Partition (2 * n)).prefixSum j + 2 ≤ lam.val.prefixSum j)
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1)) :
    ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
  intro k hjk hkj
  have hk : k = j + 1 := by omega
  subst k
  by_contra hnot
  have hle := hmu_le_lam (j + 1)
  have hEq : (mu : Nat.Partition (2 * n)).prefixSum (j + 1) =
      lam.val.prefixSum (j + 1) := by
    omega
  have hmu_j_ge : (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤
      (mu : Nat.Partition (2 * n)).rowLen j := by
    rw [prefixSum_succ, prefixSum_succ] at hEq
    omega
  have hmu_next_le : (mu : Nat.Partition (2 * n)).rowLen (j + 1) ≤
      (lam : Nat.Partition (2 * n)).rowLen j := by
    have hle2 := hmu_le_lam (j + 2)
    rw [prefixSum_succ (mu : Nat.Partition (2 * n)) (j + 1),
      prefixSum_succ (lam : Nat.Partition (2 * n)) (j + 1)] at hle2
    rw [hEq] at hle2
    have hlam_next_le : (lam : Nat.Partition (2 * n)).rowLen (j + 1) ≤
        (lam : Nat.Partition (2 * n)).rowLen j :=
      (YoungDiagram.ofPartition (lam : Nat.Partition (2 * n))).rowLen_anti
        j (j + 1) (Nat.le_succ j)
    omega
  have hmu_drop : (mu : Nat.Partition (2 * n)).rowLen (j + 1) <
      (mu : Nat.Partition (2 * n)).rowLen j := by
    omega
  have heven_mu : Even ((mu : Nat.Partition (2 * n)).prefixSum (j + 1)) :=
    even_prefixSum_of_next_lt mu.property j hmu_drop
  have hodd_lam : Odd ((lam : Nat.Partition (2 * n)).prefixSum (j + 1)) :=
    odd_prefixSum_succ_of_odd_of_prev_lt lam.property hjodd htarget
  rw [hEq] at heven_mu
  exact (Nat.not_even_iff_odd.mpr hodd_lam) heven_mu


end Nat.Partition
