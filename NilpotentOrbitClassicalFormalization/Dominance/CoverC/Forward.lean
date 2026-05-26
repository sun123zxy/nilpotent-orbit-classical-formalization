import NilpotentOrbitClassicalFormalization.Dominance.CoverC.DoubleDrop

/-!
# C-type cover forward direction

Split from `Dominance/CoverC.lean` to keep the C-type cover formalization navigable.
-/

namespace Nat.Partition

lemma CPartition.isCMove_of_exact_even_branch {n : ℕ} {mu lam : CPartition n}
    {i0 s j : ℕ} (h : mu ⋖ lam) (hi0s : i0 ≤ s) (hsj : s < j)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 2) :
    IsCMove lam mu := by
  have hmu_le_nu :
      (mu : Nat.Partition (2 * n)) ≤ boxDropPartition lam.val hsj hsource htarget hgap :=
    le_boxDropPartition_of_prefix_surplus hsj hsource htarget hgap h.le
      (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict)
  exact CPartition.isCMove_of_boxDrop_even_exact h hsj hsource htarget hgap
    hmu_le_nu hseven hjeven hexact

lemma CPartition.isCMove_of_exact_odd_branch {n : ℕ} {mu lam : CPartition n}
    {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s) (hsj : s < j)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition (2 * n)).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 2) :
    IsCMove lam mu := by
  have hst : (s - 1) + 1 < j := by
    rw [Nat.sub_add_cancel hspos]
    exact hsj
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have htarget₁ : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) :=
    htarget
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hs_ne : (s - 1) + 1 ≠ s - 1 := by omega
    have hs_t : (s - 1) + 1 ≠ j := by omega
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_t : s - 1 ≠ j := by omega
    rw [if_pos rfl, if_neg hpred_s, if_neg hpred_t]
    have hs_eq : (s - 1) + 1 = s := Nat.sub_add_cancel hspos
    rw [hs_eq]
    rw [hspair]
    have hpos : 0 < (lam : Nat.Partition (2 * n)).rowLen s := by
      rw [← hspair]
      exact hsodd.pos
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (s - 1) + 1 := by omega
    have hj1j : j + 1 ≠ j := by omega
    have hjs : j ≠ (s - 1) + 1 := by omega
    rw [if_neg hj1s, if_neg hj1j, if_neg hjs, if_pos rfl]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (s - 1) + 1 := by omega
    have hj1j : j + 1 ≠ j := by omega
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_j : s - 1 ≠ j := by omega
    rw [if_neg hj1s, if_neg hj1j, if_neg hpred_s, if_neg hpred_j]
    rw [← htpair]
    rw [hspair, hexact]
    omega
  have hspair' :
      (lam : Nat.Partition (2 * n)).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  have hgap2 :
      (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen (s - 1) := by
    rw [hspair, hexact]
  exact CPartition.isCMove_of_doubleBoxDrop_sourcePair_targetPair h hst hsource₁
    htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle_left hmiddle_two
    hmiddle_right hsodd hspair' hjodd htpair hgap2

lemma CPartition.isCMove_of_exact_branch {n : ℕ} {mu lam : CPartition n}
    {i0 s j : ℕ} (h : mu ⋖ lam) (hi0s : i0 ≤ s) (hsj : s < j)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 2)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k) :
    IsCMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition (2 * n)).rowLen s) with hseven | hsodd
  · have hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j) := by
      rcases hseven with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    exact CPartition.isCMove_of_exact_even_branch h hi0s hsj hsource htarget hgap
      hrowBefore hstrict hseven hjeven hexact
  · have hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j) := by
      rcases hsodd with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    rcases exists_prev_rowLen_eq_of_odd_of_next_lt lam.property hsodd hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_odd_of_prev_lt lam.property hjodd htarget).symm
    have hsodd_prev : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)) := by
      rw [hspair]
      exact hsodd
    exact CPartition.isCMove_of_exact_odd_branch h hspos hsj hsource htarget hgap
      hspair htpair h.le hmiddle_left hmiddle_two hmiddle_right hsodd_prev hjodd hexact

lemma CPartition.isCMove_of_exact_branch_of_source_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 2) :
    IsCMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition (2 * n)).rowLen s) with hseven | hsodd
  · have hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j) := by
      rcases hseven with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    exact CPartition.isCMove_of_exact_even_branch h hi0s hsj hsource htarget hgap
      hrowBefore hstrict hseven hjeven hexact
  · have hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j) := by
      rcases hsodd with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    rcases exists_prev_rowLen_eq_of_odd_of_next_lt lam.property hsodd hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_odd_of_prev_lt lam.property hjodd htarget).symm
    have hi0_lt_s : i0 < s :=
      CPartition.first_strict_lt_odd_plateau_bottom hbefore hstrict hi0s hsrow hsource hsodd
    have hi0pred : i0 ≤ s - 1 := by omega
    have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
        (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k :=
      by
        have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
          hrowBefore hstrict
        intro k hsk hks
        exact hone k hsk (by omega)
    have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
        (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
      have htwo := CPartition.prefix_surplus₂_of_odd_source hbefore hstrict hi0s
        hsrow hsource hsodd hrowBefore
      intro k hsk hkj
      apply htwo k
      · rwa [Nat.sub_add_cancel hspos] at hsk
      · exact hkj
    have hrowj : (mu : Nat.Partition (2 * n)).rowLen j ≤
        (lam : Nat.Partition (2 * n)).rowLen j + 1 := by
      have hi0j : i0 < j := lt_of_le_of_lt hi0s hsj
      have hmu_le : (mu : Nat.Partition (2 * n)).rowLen j ≤
          (mu : Nat.Partition (2 * n)).rowLen i0 :=
        (YoungDiagram.ofPartition (mu : Nat.Partition (2 * n))).rowLen_anti
          i0 j hi0j.le
      omega
    have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
        (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
      intro k hjk hkj
      have hk : k = j + 1 := by omega
      subst k
      exact prefixSum_succ_add_one_le_of_prefixSum_add_two_le_of_rowLen_le_add_one
        (hmiddle_two j (by omega) le_rfl) hrowj
    have hsodd_prev : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)) := by
      rw [hspair]
      exact hsodd
    exact CPartition.isCMove_of_exact_odd_branch h hspos hsj hsource htarget hgap
      hspair htpair h.le hmiddle_left hmiddle_two hmiddle_right hsodd_prev hjodd hexact

lemma CPartition.isCMove_of_large_even_adjacent_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hj : j = s + 1)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap4 : (lam : Nat.Partition (2 * n)).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  subst j
  have hst : s < s + 1 := Nat.lt_succ_self s
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s := hsource
  have htarget₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen ((s + 1) - 1) :=
    htarget
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) + 1 < lam.val.rowLen s := hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    simp
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s + 1) - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    simp
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    simp
    omega
  exact CPartition.isCMove_of_doubleBoxDrop_same h hst hsource₁ htarget₁ hgap₁
    hsource₂ htarget₂ hgap₂ h.le hmiddle hseven hjeven hgap4

lemma CPartition.isCMove_of_even_odd_adjacent_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hj : j = s + 1)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hmiddle₂ : ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle₁ : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  subst j
  have hst : s < s + 1 := Nat.lt_succ_self s
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s := hsource
  have htarget₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) <
        lam.val.rowLen ((s + 1) - 1) :=
    htarget
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) + 1 < lam.val.rowLen s := hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    simp
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s + 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hs2s : (s + 1) + 1 ≠ s := by omega
    have hs2t : (s + 1) + 1 ≠ s + 1 := by omega
    have ht_s : s + 1 ≠ s := by omega
    rw [if_neg hs2s, if_neg hs2t, if_neg ht_s, if_pos rfl]
    rw [← htpair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s + 1) + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hs2s : (s + 1) + 1 ≠ s := by omega
    have hs2t : (s + 1) + 1 ≠ s + 1 := by omega
    rw [if_neg hs2s, if_neg hs2t, if_pos rfl]
    rw [← htpair]
    omega
  exact CPartition.isCMove_of_doubleBoxDrop_source_pairTarget h hst hsource₁
    htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle₂ hmiddle₁ hseven
    hjodd htpair hgap3

lemma CPartition.isCMove_of_large_even_nonadjacent_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle_pair : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hjgap : (lam : Nat.Partition (2 * n)).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hjpos : 0 < j := by omega
  have hj2_succ : (j - 2) + 1 = j - 1 := by omega
  have hj2_lt_j : j - 2 + 1 < j := by omega
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (((j - 2) + 1) + 1) <
        lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ]
    have hjpred_succ : (j - 1) + 1 = j := by omega
    rw [hjpred_succ, hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen
          ((j - 2) + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hleft : (j - 2) + 1 ≠ j - 2 := by omega
    have hleft_t : (j - 2) + 1 ≠ j := by omega
    have hright : j - 2 ≠ (j - 2) + 1 := by omega
    have hright_t : j - 2 ≠ j := by omega
    rw [if_pos rfl, if_neg hright, if_neg hright_t]
    rw [hj2_succ, hrow_mid, hrow_mid_prev]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hjsrc : j ≠ (j - 2) + 1 := by omega
    have hpred_src : j - 1 = (j - 2) + 1 := by omega
    have hpred_t : j - 1 ≠ j := by omega
    rw [if_neg hjsrc, if_pos rfl, if_pos hpred_src]
    rw [hrow_mid]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j + 1 <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hjsrc : j ≠ (j - 2) + 1 := by omega
    have hright : j - 2 ≠ (j - 2) + 1 := by omega
    have hright_t : j - 2 ≠ j := by omega
    rw [if_neg hjsrc, if_pos rfl, if_neg hright, if_neg hright_t]
    rw [hrow_mid_prev]
    omega
  have hmidOdd : Odd ((lam : Nat.Partition (2 * n)).rowLen (j - 2)) := by
    rcases hseven with ⟨a, ha⟩
    rw [hrow_mid_prev]
    refine ⟨a - 1, ?_⟩
    omega
  have hpair : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid_prev, hrow_mid]
  have hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen (j - 2) := by
    rw [hrow_mid_prev]
    omega
  exact CPartition.isCMove_of_doubleBoxDrop_sourcePair_target h hj2_lt_j hsource₁ htarget₁
    hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_pair hmiddle_target hmidOdd hpair
    hjeven hgap3

lemma CPartition.isCMove_of_large_even_nonadjacent_branch_of_pair_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hjgap : (lam : Nat.Partition (2 * n)).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hi0_pair : i0 ≤ j - 2 := by omega
  have hmiddle_pair : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0_pair
      hrowBefore hstrict
    intro k hjk hkj
    exact hone k hjk (by omega)
  exact CPartition.isCMove_of_large_even_nonadjacent_branch h hsj hmiddle_pair
    hmiddle_target hrow_mid hrow_mid_prev hseven hjeven hjgap

lemma CPartition.isCMove_of_even_odd_nonadjacent_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle_left : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hjgap : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hj2_succ : (j - 2) + 1 = j - 1 := by omega
  have hj2_lt_j : j - 2 + 1 < j := by omega
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (((j - 2) + 1) + 1) <
        lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ]
    have hjpred_succ : (j - 1) + 1 = j := by omega
    rw [hjpred_succ, hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen
          ((j - 2) + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hright : j - 2 ≠ (j - 2) + 1 := by omega
    have hright_t : j - 2 ≠ j := by omega
    rw [if_pos rfl, if_neg hright, if_neg hright_t]
    rw [hj2_succ, hrow_mid, hrow_mid_prev]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (j - 2) + 1 := by omega
    have hj1t : j + 1 ≠ j := by omega
    have hjs : j ≠ (j - 2) + 1 := by omega
    rw [if_neg hj1s, if_neg hj1t, if_neg hjs, if_pos rfl]
    rw [← htpair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (j - 2) + 1 := by omega
    have hj1t : j + 1 ≠ j := by omega
    have hright : j - 2 ≠ (j - 2) + 1 := by omega
    have hright_t : j - 2 ≠ j := by omega
    rw [if_neg hj1s, if_neg hj1t, if_neg hright, if_neg hright_t]
    rw [← htpair, hrow_mid_prev]
    omega
  have hmidOdd : Odd ((lam : Nat.Partition (2 * n)).rowLen (j - 2)) := by
    rcases hseven with ⟨a, ha⟩
    rw [hrow_mid_prev]
    refine ⟨a - 1, ?_⟩
    omega
  have hpair : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid_prev, hrow_mid]
  have hgap2 : (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen (j - 2) := by
    rw [hrow_mid_prev]
    omega
  exact CPartition.isCMove_of_doubleBoxDrop_sourcePair_targetPair h hj2_lt_j
    hsource₁ htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left
    hmiddle_two hmiddle_right hmidOdd hpair hjodd htpair hgap2

lemma CPartition.isCMove_of_even_odd_nonadjacent_branch_of_pair_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition (2 * n)).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hjgap : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hi0_pair : i0 ≤ j - 2 := by omega
  have hmiddle_left : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0_pair
      hrowBefore hstrict
    intro k hsk hkj
    exact hone k hsk (by omega)
  exact CPartition.isCMove_of_even_odd_nonadjacent_branch h hsj hmiddle_left
    hmiddle_two hmiddle_right hrow_mid hrow_mid_prev hseven hjodd htpair hjgap

lemma CPartition.isCMove_of_even_source_large_branch {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hlarge : (lam : Nat.Partition (2 * n)).rowLen j + 2 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition (2 * n)).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s)) :
    IsCMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition (2 * n)).rowLen j) with hjeven | hjodd
  · have hgap4 : (lam : Nat.Partition (2 * n)).rowLen j + 4 ≤ lam.val.rowLen s := by
      rcases hseven with ⟨a, ha⟩
      rcases hjeven with ⟨b, hb⟩
      omega
    by_cases hadj : j = s + 1
    · have hmiddle : ∀ k : ℕ, s < k → k ≤ j →
          (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus₂_of_even_source_adjacent h.le hbefore hstrict
          hi0s hadj hsrow hsource hrowBefore (by omega)
      exact CPartition.isCMove_of_large_even_adjacent_branch h hadj hsource
        htarget hgap hmiddle hseven hjeven hgap4
    · have hsj_nonadj : s + 1 < j := by omega
      have hs_j2 : s < j - 2 :=
        CPartition.two_lt_target_sub_two_of_even_source hi0s hsj_nonadj hsrow
          hsource hnoDrop hseven hlarge
      have hrow_mid :
          (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1 :=
        rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) (by omega) hsrow
          hsource hnoDrop
      have hrow_mid_prev :
          (lam : Nat.Partition (2 * n)).rowLen (j - 2) = lam.val.rowLen s - 1 :=
        rowLen_eq_pred_of_source_lt_of_noDrop hi0s hs_j2 (by omega) hsrow
          hsource hnoDrop
      have hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
          (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus₂_of_even_source_nonadjacent h.le hstrict hi0s
          hsj_nonadj hsrow htarget hrowBefore hrow_mid (by omega)
      exact CPartition.isCMove_of_large_even_nonadjacent_branch_of_pair_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hmiddle_target hrow_mid hrow_mid_prev
        hseven hjeven hgap4
  · have htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_odd_of_prev_lt lam.property hjodd htarget).symm
    have hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s := by
      rcases hseven with ⟨a, ha⟩
      rcases hjodd with ⟨b, hb⟩
      omega
    by_cases hadj : j = s + 1
    · have hmiddle₂ : ∀ k : ℕ, s < k → k ≤ j →
          (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus₂_of_even_source_adjacent h.le hbefore hstrict
          hi0s hadj hsrow hsource hrowBefore hgap3
      have hprefix_j : (mu : Nat.Partition (2 * n)).prefixSum j + 2 ≤
          lam.val.prefixSum j := hmiddle₂ j (by omega) le_rfl
      have hmiddle₁ : ∀ k : ℕ, j < k → k ≤ j + 1 →
          (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus_right_of_odd_target h.le hprefix_j hjodd htarget
      exact CPartition.isCMove_of_even_odd_adjacent_branch h hadj hsource htarget
        hgap hmiddle₂ hmiddle₁ hseven hjodd htpair hgap3
    · have hsj_nonadj : s + 1 < j := by omega
      have hs_j2 : s < j - 2 :=
        CPartition.two_lt_target_sub_two_of_even_source hi0s hsj_nonadj hsrow
          hsource hnoDrop hseven hlarge
      have hrow_mid :
          (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1 :=
        rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) (by omega) hsrow
          hsource hnoDrop
      have hrow_mid_prev :
          (lam : Nat.Partition (2 * n)).rowLen (j - 2) = lam.val.rowLen s - 1 :=
        rowLen_eq_pred_of_source_lt_of_noDrop hi0s hs_j2 (by omega) hsrow
          hsource hnoDrop
      have hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
          (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus₂_of_even_source_nonadjacent h.le hstrict hi0s
          hsj_nonadj hsrow htarget hrowBefore hrow_mid hgap3
      have hprefix_j : (mu : Nat.Partition (2 * n)).prefixSum j + 2 ≤
          lam.val.prefixSum j := hmiddle_two j (by omega) le_rfl
      have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
          (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k :=
        CPartition.prefix_surplus_right_of_odd_target h.le hprefix_j hjodd htarget
      exact CPartition.isCMove_of_even_odd_nonadjacent_branch_of_pair_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hmiddle_two hmiddle_right hrow_mid
        hrow_mid_prev hseven hjodd htpair hgap3

lemma CPartition.isCMove_of_odd_even_adjacent_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s)
    (hj : j = s + 1)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition (2 * n)).rowLen (s - 1) = lam.val.rowLen s)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen (s - 1)) :
    IsCMove lam mu := by
  subst j
  have hst : (s - 1) + 1 < s + 1 := by
    rw [Nat.sub_add_cancel hspos]
    exact Nat.lt_succ_self s
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have htarget₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) <
        lam.val.rowLen ((s + 1) - 1) :=
    htarget
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen (s + 1) + 1 <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hs_ne : (s - 1) + 1 ≠ s - 1 := by omega
    have hs_t : (s - 1) + 1 ≠ s + 1 := by omega
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_t : s - 1 ≠ s + 1 := by omega
    rw [if_pos rfl, if_neg hpred_s, if_neg hpred_t]
    rw [Nat.sub_add_cancel hspos, hspair]
    have hpos : 0 < (lam : Nat.Partition (2 * n)).rowLen s := by
      rw [← hspair]
      exact hsodd.pos
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s + 1) - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have ht_s : s + 1 ≠ (s - 1) + 1 := by omega
    have hpred_eq : (s + 1) - 1 = (s - 1) + 1 := by omega
    have hpred_t : (s + 1) - 1 ≠ s + 1 := by omega
    rw [if_neg ht_s, if_pos rfl, if_pos hpred_eq]
    have hpred_s : (s + 1) - 1 = s := by omega
    rw [hpred_s, ← hspair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have ht_s : s + 1 ≠ (s - 1) + 1 := by omega
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_t : s - 1 ≠ s + 1 := by omega
    rw [if_neg ht_s, if_pos rfl, if_neg hpred_s, if_neg hpred_t]
    omega
  have hspair' :
      (lam : Nat.Partition (2 * n)).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  exact CPartition.isCMove_of_doubleBoxDrop_sourcePair_target h hst hsource₁ htarget₁
    hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left hmiddle_two hsodd hspair'
    hjeven hgap3

lemma CPartition.isCMove_of_odd_even_adjacent_branch_of_source_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hspos : 0 < s) (hj : j = s + 1)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition (2 * n)).rowLen (s - 1) = lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen (s - 1)) :
    IsCMove lam mu := by
  have hsodd_source : Odd ((lam : Nat.Partition (2 * n)).rowLen s) := by
    rw [← hspair]
    exact hsodd
  have hi0_lt_s : i0 < s :=
    CPartition.first_strict_lt_odd_plateau_bottom hbefore hstrict hi0s hsrow hsource
      hsodd_source
  have hi0pred : i0 ≤ s - 1 := by omega
  have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hks
    exact hone k hsk (by omega)
  have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := CPartition.prefix_surplus₂_of_odd_source hbefore hstrict hi0s
      hsrow hsource hsodd_source hrowBefore
    intro k hsk hkj
    apply htwo k
    · rwa [Nat.sub_add_cancel hspos] at hsk
    · exact hkj
  exact CPartition.isCMove_of_odd_even_adjacent_branch h hspos hj hsource htarget hgap
    hspair hmiddle_left hmiddle_two hsodd hjeven hgap3

lemma CPartition.isCMove_of_odd_even_nonadjacent_exact_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 3) :
    IsCMove lam mu := by
  have hst : j - 1 < j := by omega
  have hsource : (lam : Nat.Partition (2 * n)).rowLen ((j - 1) + 1) <
      lam.val.rowLen (j - 1) := by
    rw [Nat.sub_add_cancel (by omega : 0 < j), hrow_mid, hexact]
    omega
  have htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid, hexact]
    omega
  have hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen (j - 1) := by
    rw [hrow_mid, hexact]
    omega
  have hsourceEven : Even ((lam : Nat.Partition (2 * n)).rowLen (j - 1)) := by
    rcases hsodd with ⟨a, ha⟩
    rw [hrow_mid]
    refine ⟨a, ?_⟩
    omega
  have hsourceExact :
      (lam : Nat.Partition (2 * n)).rowLen (j - 1) =
        (lam : Nat.Partition (2 * n)).rowLen j + 2 := by
    rw [hrow_mid, hexact]
    omega
  have hmu_le_nu :
      (mu : Nat.Partition (2 * n)) ≤ boxDropPartition lam.val hst hsource htarget hgap :=
    le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.le hmiddle
  exact CPartition.isCMove_of_boxDrop_even_exact h hst hsource htarget hgap hmu_le_nu
    hsourceEven hjeven hsourceExact

lemma CPartition.isCMove_of_odd_even_nonadjacent_exact_branch_of_source_surplus
    {n : ℕ} {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 3) :
    IsCMove lam mu := by
  have hi0pred : i0 ≤ j - 1 := by omega
  have hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hkj
    exact hone k hsk hkj
  exact CPartition.isCMove_of_odd_even_nonadjacent_exact_branch h hsj hmiddle
    hrow_mid hsodd hjeven hexact

lemma CPartition.isCMove_of_odd_even_nonadjacent_large_branch {n : ℕ}
    {mu lam : CPartition n} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap5 : (lam : Nat.Partition (2 * n)).rowLen j + 5 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hst : j - 1 < j := by omega
  have hsource₁ : (lam : Nat.Partition (2 * n)).rowLen ((j - 1) + 1) <
      lam.val.rowLen (j - 1) := by
    rw [Nat.sub_add_cancel (by omega : 0 < j), hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1 + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj_s : j ≠ j - 1 := by omega
    have hpred_s : j - 1 = j - 1 := rfl
    have hpred_t : j - 1 ≠ j := by omega
    rw [Nat.sub_add_cancel (by omega : 0 < j)]
    rw [if_neg hj_s, if_pos rfl, if_pos hpred_s]
    rw [hrow_mid]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj_s : j ≠ j - 1 := by omega
    have hpred_s : j - 1 = j - 1 := rfl
    rw [if_neg hj_s, if_pos rfl, if_pos hpred_s]
    rw [hrow_mid]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj_s : j ≠ j - 1 := by omega
    have hpred_s : j - 1 = j - 1 := rfl
    rw [if_neg hj_s, if_pos rfl, if_pos hpred_s]
    rw [hrow_mid]
    omega
  have hsourceEven : Even ((lam : Nat.Partition (2 * n)).rowLen (j - 1)) := by
    rcases hsodd with ⟨a, ha⟩
    rw [hrow_mid]
    refine ⟨a, ?_⟩
    omega
  have hgap4 :
      (lam : Nat.Partition (2 * n)).rowLen j + 4 ≤ lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  exact CPartition.isCMove_of_doubleBoxDrop_same h hst hsource₁ htarget₁ hgap₁
    hsource₂ htarget₂ hgap₂ h.le hmiddle hsourceEven hjeven hgap4

lemma CPartition.isCMove_of_odd_even_nonadjacent_large_branch_of_source_surplus
    {n : ℕ} {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hrow_mid : (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap5 : (lam : Nat.Partition (2 * n)).rowLen j + 5 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  have hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := CPartition.prefix_surplus₂_of_odd_source hbefore hstrict hi0s
      hsrow hsource hsodd hrowBefore
    intro k hjk hkj
    exact htwo k (by omega) hkj
  exact CPartition.isCMove_of_odd_even_nonadjacent_large_branch h hsj hmiddle
    hrow_mid hsodd hjeven hgap5

lemma CPartition.isCMove_of_odd_even_branch_of_source_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition (2 * n)).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hjeven : Even ((lam : Nat.Partition (2 * n)).rowLen j)) :
    IsCMove lam mu := by
  rcases exists_prev_rowLen_eq_of_odd_of_next_lt lam.property hsodd hsource with
    ⟨hspos, hspair⟩
  have hsodd_prev : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)) := by
    rw [hspair]
    exact hsodd
  have hgap3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤
      lam.val.rowLen (s - 1) := by
    rw [hspair]
    rcases hsodd with ⟨a, ha⟩
    rcases hjeven with ⟨b, hb⟩
    omega
  by_cases hadj : j = s + 1
  · exact CPartition.isCMove_of_odd_even_adjacent_branch_of_source_surplus h hbefore
      hi0s hspos hadj hsrow hsource htarget hgap hspair hrowBefore hstrict
      hsodd_prev hjeven hgap3
  · have hsj_nonadj : s + 1 < j := by omega
    have hrow_mid :
        (lam : Nat.Partition (2 * n)).rowLen (j - 1) = lam.val.rowLen s - 1 :=
      rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) (by omega) hsrow
        hsource hnoDrop
    by_cases hexact : (lam : Nat.Partition (2 * n)).rowLen s =
        (lam : Nat.Partition (2 * n)).rowLen j + 3
    · exact CPartition.isCMove_of_odd_even_nonadjacent_exact_branch_of_source_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hrow_mid hsodd hjeven hexact
    · have hgap5 :
          (lam : Nat.Partition (2 * n)).rowLen j + 5 ≤ lam.val.rowLen s := by
        have hle3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 ≤ lam.val.rowLen s := by
          rcases hsodd with ⟨a, ha⟩
          rcases hjeven with ⟨b, hb⟩
          omega
        have hlt3 : (lam : Nat.Partition (2 * n)).rowLen j + 3 < lam.val.rowLen s :=
          lt_of_le_of_ne hle3 (Ne.symm hexact)
        rcases hsodd with ⟨a, ha⟩
        rcases hjeven with ⟨b, hb⟩
        omega
      exact CPartition.isCMove_of_odd_even_nonadjacent_large_branch_of_source_surplus h
        hbefore hi0s hsj_nonadj hsrow hsource hrowBefore hstrict hrow_mid hsodd
        hjeven hgap5

lemma CPartition.isCMove_of_odd_odd_branch {n : ℕ} {mu lam : CPartition n}
    {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s) (hsj : s < j)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition (2 * n)).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap2 : (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen (s - 1)) :
    IsCMove lam mu := by
  have hst : (s - 1) + 1 < j := by
    rw [Nat.sub_add_cancel hspos]
    exact hsj
  have hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have htarget₁ : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) :=
    htarget
  have hgap₁ :
      (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_t : s - 1 ≠ j := by omega
    rw [if_pos rfl, if_neg hpred_s, if_neg hpred_t]
    rw [Nat.sub_add_cancel hspos, hspair]
    have hpos : 0 < (lam : Nat.Partition (2 * n)).rowLen s := by
      rw [← hspair]
      exact hsodd.pos
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (s - 1) + 1 := by omega
    have hj1j : j + 1 ≠ j := by omega
    have hjs : j ≠ (s - 1) + 1 := by omega
    rw [if_neg hj1s, if_neg hj1j, if_neg hjs, if_pos rfl]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    have hj1s : j + 1 ≠ (s - 1) + 1 := by omega
    have hj1j : j + 1 ≠ j := by omega
    have hpred_s : s - 1 ≠ (s - 1) + 1 := by omega
    have hpred_j : s - 1 ≠ j := by omega
    rw [if_neg hj1s, if_neg hj1j, if_neg hpred_s, if_neg hpred_j]
    rw [← htpair]
    omega
  have hspair' :
      (lam : Nat.Partition (2 * n)).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  exact CPartition.isCMove_of_doubleBoxDrop_sourcePair_targetPair h hst hsource₁
    htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left hmiddle_two
    hmiddle_right hsodd hspair' hjodd htpair hgap2

lemma CPartition.isCMove_of_odd_odd_branch_of_source_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hspos : 0 < s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition (2 * n)).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1))
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)))
    (hjodd : Odd ((lam : Nat.Partition (2 * n)).rowLen j))
    (hgap2 : (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen (s - 1)) :
    IsCMove lam mu := by
  have hsodd_source : Odd ((lam : Nat.Partition (2 * n)).rowLen s) := by
    rw [← hspair]
    exact hsodd
  have hi0_lt_s : i0 < s :=
    CPartition.first_strict_lt_odd_plateau_bottom hbefore hstrict hi0s hsrow hsource
      hsodd_source
  have hi0pred : i0 ≤ s - 1 := by omega
  have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hks
    exact hone k hsk (by omega)
  have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := CPartition.prefix_surplus₂_of_odd_source hbefore hstrict hi0s
      hsrow hsource hsodd_source hrowBefore
    intro k hsk hkj
    apply htwo k
    · rwa [Nat.sub_add_cancel hspos] at hsk
    · exact hkj
  exact CPartition.isCMove_of_odd_odd_branch h hspos hsj hsource htarget hgap
    hspair htpair hmiddle_left hmiddle_two hmiddle_right hsodd hjodd hgap2

lemma CPartition.isCMove_of_odd_source_branch_of_source_surplus {n : ℕ}
    {mu lam : CPartition n} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition (2 * n)).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition (2 * n)).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition (2 * n)).rowLen i0 < lam.val.rowLen i0)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s)) :
    IsCMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition (2 * n)).rowLen j) with hjeven | hjodd
  · exact CPartition.isCMove_of_odd_even_branch_of_source_surplus h hbefore hi0s hsj
      hsrow hsource htarget hgap hnoDrop hrowBefore hstrict hsodd hjeven
  · rcases exists_prev_rowLen_eq_of_odd_of_next_lt lam.property hsodd hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition (2 * n)).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_odd_of_prev_lt lam.property hjodd htarget).symm
    have hsodd_prev : Odd ((lam : Nat.Partition (2 * n)).rowLen (s - 1)) := by
      rw [hspair]
      exact hsodd
    have hgap2 :
        (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen (s - 1) := by
      rw [hspair]
      rcases hsodd with ⟨a, ha⟩
      rcases hjodd with ⟨b, hb⟩
      omega
    have hprefix_j : (mu : Nat.Partition (2 * n)).prefixSum j + 2 ≤
        lam.val.prefixSum j := by
      have htwo := CPartition.prefix_surplus₂_of_odd_source hbefore hstrict hi0s
        hsrow hsource hsodd hrowBefore
      exact htwo j hsj le_rfl
    have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
        (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k :=
      CPartition.prefix_surplus_right_of_odd_target h.le hprefix_j hjodd htarget
    exact CPartition.isCMove_of_odd_odd_branch_of_source_surplus h hbefore hi0s hspos
      hsj hsrow hsource htarget hgap hspair htpair hrowBefore hstrict hmiddle_right
      hsodd_prev hjodd hgap2

/-- A C-type dominance cover has one of Hesselink's five visible move shapes. -/
theorem CPartition.isCMove_of_covBy {n : ℕ} {mu lam : CPartition n} (h : mu ⋖ lam) :
    IsCMove lam mu := by
  classical
  rcases exists_first_rowLen_lt_of_lt (cPartition_lt_iff.mp h.lt) with
    ⟨i0, hbefore, hstrict⟩
  let targetExists := exists_drop_target_of_first_row
    (mu := (mu : Nat.Partition (2 * n))) (lam := (lam : Nat.Partition (2 * n)))
    hbefore hstrict
  let j := Nat.find targetExists
  have hj_spec : i0 < j ∧
      (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen i0 :=
    Nat.find_spec targetExists
  have hi0j : i0 < j := hj_spec.1
  have hjgap_i0 : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen i0 :=
    hj_spec.2
  have hnoDrop :
      ∀ r : ℕ, i0 ≤ r → r < j →
        ¬(lam : Nat.Partition (2 * n)).rowLen r + 1 < lam.val.rowLen i0 := by
    intro r hi0r hrj hdrop
    rcases eq_or_lt_of_le hi0r with rfl | hi0r_lt
    · omega
    · exact Nat.find_min targetExists hrj ⟨hi0r_lt, hdrop⟩
  have hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition (2 * n)).rowLen r ≤ lam.val.rowLen r :=
    rowLen_mu_le_lam_before_target hbefore hstrict hnoDrop
  have hjdrop : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen i0 := by
    omega
  rcases exists_plateau_source (lam : Nat.Partition (2 * n)) hi0j hjdrop with
    ⟨s, hi0s, hsj, hsrow, hsource⟩
  have htarget : (lam : Nat.Partition (2 * n)).rowLen j < lam.val.rowLen (j - 1) := by
    have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i0) hi0j
    have hi0pred : i0 ≤ j - 1 := Nat.le_sub_one_of_lt hi0j
    have hpred_lt : j - 1 < j := Nat.sub_one_lt_of_lt hjpos
    have hnopred := hnoDrop (j - 1) hi0pred hpred_lt
    have hlower : (lam : Nat.Partition (2 * n)).rowLen i0 ≤
        lam.val.rowLen (j - 1) + 1 := le_of_not_gt hnopred
    omega
  have hgap : (lam : Nat.Partition (2 * n)).rowLen j + 1 < lam.val.rowLen s := by
    rw [hsrow]
    exact hjgap_i0
  by_cases hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen j + 2
  · exact CPartition.isCMove_of_exact_branch_of_source_surplus h hbefore hi0s hsj
      hsrow hsource htarget hgap hrowBefore hstrict hexact
  · have hlarge : (lam : Nat.Partition (2 * n)).rowLen j + 2 < lam.val.rowLen s := by
      have hle : (lam : Nat.Partition (2 * n)).rowLen j + 2 ≤ lam.val.rowLen s := by
        omega
      exact lt_of_le_of_ne hle (Ne.symm hexact)
    rcases Nat.even_or_odd ((lam : Nat.Partition (2 * n)).rowLen s) with hseven | hsodd
    · exact CPartition.isCMove_of_even_source_large_branch h hbefore hi0s hsj
        hsrow hsource htarget hgap hlarge hnoDrop hrowBefore hstrict hseven
    · exact CPartition.isCMove_of_odd_source_branch_of_source_surplus h hbefore
        hi0s hsj hsrow hsource htarget hgap hnoDrop hrowBefore hstrict hsodd


end Nat.Partition
