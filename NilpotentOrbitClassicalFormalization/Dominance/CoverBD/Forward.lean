import NilpotentOrbitClassicalFormalization.Dominance.CoverBD.DoubleDrop

/-!
# B/D-type cover forward direction

This file proves the forward B/D cover characterization by following the
first-gap construction used for type A and the parity case split of Hesselink's
B/D list.
-/

namespace Nat.Partition

lemma BDPartition.isBDMove_of_exact_odd_branch {N : ℕ} {mu lam : BDPartition N}
    {i0 s j : ℕ} (h : mu ⋖ lam) (hi0s : i0 ≤ s) (hsj : s < j)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 2) :
    IsBDMove lam mu := by
  have hmu_le_nu :
      (mu : Nat.Partition N) ≤ boxDropPartition lam.val hsj hsource htarget hgap :=
    le_boxDropPartition_of_prefix_surplus hsj hsource htarget hgap h.le
      (prefix_surplus_of_rowLen_le_before_target hi0s hrowBefore hstrict)
  exact BDPartition.isBDMove_of_boxDrop_odd_exact h hsj hsource htarget hgap
    hmu_le_nu hs_odd hj_odd hexact

lemma BDPartition.isBDMove_of_exact_even_branch {N : ℕ} {mu lam : BDPartition N}
    {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s) (hsj : s < j)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition N).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hmu_le_lam : (mu : Nat.Partition N) ≤ lam)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen (s - 1)))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 2) :
    IsBDMove lam mu := by
  have hst : (s - 1) + 1 < j := by
    rw [Nat.sub_add_cancel hspos]
    exact hsj
  have hsource₁ :
      (lam : Nat.Partition N).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have hgap₁ :
      (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_pos rfl, if_neg (by omega : s - 1 ≠ (s - 1) + 1),
      if_neg (by omega : s - 1 ≠ j)]
    have hs_eq : (s - 1) + 1 = s := Nat.sub_add_cancel hspos
    rw [hs_eq, hspair]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (s - 1) + 1),
      if_neg (by omega : j + 1 ≠ j), if_neg (by omega : j ≠ (s - 1) + 1),
      if_pos rfl]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (s - 1) + 1),
      if_neg (by omega : j + 1 ≠ j),
      if_neg (by omega : s - 1 ≠ (s - 1) + 1),
      if_neg (by omega : s - 1 ≠ j)]
    rw [← htpair, hspair, hexact]
    omega
  have hspair' :
      (lam : Nat.Partition N).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  have hgap2 :
      (lam : Nat.Partition N).rowLen j + 2 ≤ lam.val.rowLen (s - 1) := by
    rw [hspair, hexact]
  exact BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_targetPair h hst hsource₁
    htarget hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle_left hmiddle_two
    hmiddle_right hs_even hspair' hj_even htpair hgap2

lemma BDPartition.isBDMove_of_exact_branch {N : ℕ} {mu lam : BDPartition N}
    {i0 s j : ℕ} (h : mu ⋖ lam) (hi0s : i0 ≤ s) (hsj : s < j)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 2)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k) :
    IsBDMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition N).rowLen s) with hs_even | hs_odd
  · have hj_even : Even ((lam : Nat.Partition N).rowLen j) := by
      rcases hs_even with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    rcases exists_prev_rowLen_eq_of_even_of_next_lt lam.property hs_even hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_even_of_prev_lt lam.property hj_even htarget).symm
    have hs_even_prev : Even ((lam : Nat.Partition N).rowLen (s - 1)) := by
      rw [hspair]
      exact hs_even
    exact BDPartition.isBDMove_of_exact_even_branch h hspos hsj hsource htarget hgap
      hspair htpair h.le hmiddle_left hmiddle_two hmiddle_right hs_even_prev hj_even hexact
  · have hj_odd : Odd ((lam : Nat.Partition N).rowLen j) := by
      rcases hs_odd with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    exact BDPartition.isBDMove_of_exact_odd_branch h hi0s hsj hsource htarget hgap
      hrowBefore hstrict hs_odd hj_odd hexact

lemma BDPartition.isBDMove_of_exact_branch_of_source_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 2) :
    IsBDMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition N).rowLen s) with hs_even | hs_odd
  · have hj_even : Even ((lam : Nat.Partition N).rowLen j) := by
      rcases hs_even with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    rcases exists_prev_rowLen_eq_of_even_of_next_lt lam.property hs_even hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_even_of_prev_lt lam.property hj_even htarget).symm
    have hi0_lt_s : i0 < s :=
      BDPartition.first_strict_lt_even_plateau_bottom hbefore hstrict hi0s
        hsrow hsource hs_even
    have hi0pred : i0 ≤ s - 1 := by omega
    have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
        (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
      have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
        hrowBefore hstrict
      intro k hsk hks
      exact hone k hsk (by omega)
    have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
        (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k := by
      have htwo := BDPartition.prefix_surplus₂_of_even_source hbefore hstrict hi0s
        hsrow hsource hs_even hrowBefore
      intro k hsk hkj
      apply htwo k
      · rwa [Nat.sub_add_cancel hspos] at hsk
      · exact hkj
    have hrowj : (mu : Nat.Partition N).rowLen j ≤
        (lam : Nat.Partition N).rowLen j + 1 := by
      have hi0j : i0 < j := lt_of_le_of_lt hi0s hsj
      have hmu_le : (mu : Nat.Partition N).rowLen j ≤
          (mu : Nat.Partition N).rowLen i0 :=
        (YoungDiagram.ofPartition (mu : Nat.Partition N)).rowLen_anti
          i0 j hi0j.le
      omega
    have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
        (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
      intro k hjk hkj
      have hk : k = j + 1 := by omega
      subst k
      exact prefixSum_succ_add_one_le_of_prefixSum_add_two_le_of_rowLen_le_add_one
        (hmiddle_two j (by omega) le_rfl) hrowj
    have hs_even_prev : Even ((lam : Nat.Partition N).rowLen (s - 1)) := by
      rw [hspair]
      exact hs_even
    exact BDPartition.isBDMove_of_exact_even_branch h hspos hsj hsource htarget hgap
      hspair htpair h.le hmiddle_left hmiddle_two hmiddle_right hs_even_prev hj_even hexact
  · have hj_odd : Odd ((lam : Nat.Partition N).rowLen j) := by
      rcases hs_odd with ⟨a, ha⟩
      refine ⟨a - 1, ?_⟩
      omega
    exact BDPartition.isBDMove_of_exact_odd_branch h hi0s hsj hsource htarget hgap
      hrowBefore hstrict hs_odd hj_odd hexact

lemma BDPartition.isBDMove_of_large_odd_adjacent_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hj : j = s + 1)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hgap4 : (lam : Nat.Partition N).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  subst j
  have hst : s < s + 1 := Nat.lt_succ_self s
  have hsource₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen s := by
    simp only [rowLen_boxDropPartition lam.val hst hsource htarget hgap,
      if_neg (by omega : s + 1 ≠ s), ↓reduceIte]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen ((s + 1) - 1) := by
    simp only [rowLen_boxDropPartition lam.val hst hsource htarget hgap,
      Nat.add_sub_cancel, if_neg (by omega : s + 1 ≠ s), ↓reduceIte]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen (s + 1) + 1 <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen s := by
    simp only [rowLen_boxDropPartition lam.val hst hsource htarget hgap,
      if_neg (by omega : s + 1 ≠ s), ↓reduceIte]
    omega
  exact BDPartition.isBDMove_of_doubleBoxDrop_same h hst hsource htarget hgap
    hsource₂ htarget₂ hgap₂ h.le hmiddle hs_odd hj_odd hgap4

lemma BDPartition.isBDMove_of_odd_even_adjacent_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hj : j = s + 1)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hmiddle₂ : ∀ k : ℕ, s < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle₁ : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  subst j
  have hst : s < s + 1 := Nat.lt_succ_self s
  have hsource₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen s := by
    simp only [rowLen_boxDropPartition lam.val hst hsource htarget hgap,
      if_neg (by omega : s + 1 ≠ s), ↓reduceIte]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen ((s + 1) + 1) <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen (s + 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource htarget hgap]
    rw [rowLen_boxDropPartition lam.val hst hsource htarget hgap]
    rw [if_neg (by omega : (s + 1) + 1 ≠ s),
      if_neg (by omega : (s + 1) + 1 ≠ s + 1),
      if_neg (by omega : s + 1 ≠ s), if_pos rfl]
    rw [← htpair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource htarget hgap).rowLen ((s + 1) + 1) + 1 <
        (boxDropPartition lam.val hst hsource htarget hgap).rowLen s := by
    rw [rowLen_boxDropPartition lam.val hst hsource htarget hgap]
    rw [rowLen_boxDropPartition lam.val hst hsource htarget hgap]
    rw [if_neg (by omega : (s + 1) + 1 ≠ s),
      if_neg (by omega : (s + 1) + 1 ≠ s + 1), if_pos rfl]
    rw [← htpair]
    omega
  exact BDPartition.isBDMove_of_doubleBoxDrop_source_pairTarget h hst hsource htarget
    hgap hsource₂ htarget₂ hgap₂ h.le hmiddle₂ hmiddle₁ hs_odd hj_even htpair hgap3

lemma BDPartition.isBDMove_of_even_odd_adjacent_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s)
    (hj : j = s + 1)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition N).rowLen (s - 1) = lam.val.rowLen s)
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen (s - 1)))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen (s - 1)) :
    IsBDMove lam mu := by
  subst j
  have hst : (s - 1) + 1 < s + 1 := by
    rw [Nat.sub_add_cancel hspos]
    exact Nat.lt_succ_self s
  have hsource₁ :
      (lam : Nat.Partition N).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have hgap₁ :
      (lam : Nat.Partition N).rowLen (s + 1) + 1 <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_pos rfl, if_neg (by omega : s - 1 ≠ (s - 1) + 1),
      if_neg (by omega : s - 1 ≠ s + 1)]
    rw [Nat.sub_add_cancel hspos, hspair]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen ((s + 1) - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : s + 1 ≠ (s - 1) + 1), if_pos rfl,
      if_pos (by omega : (s + 1) - 1 = (s - 1) + 1)]
    rw [(by omega : (s + 1) - 1 = s), ← hspair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : s + 1 ≠ (s - 1) + 1), if_pos rfl,
      if_neg (by omega : s - 1 ≠ (s - 1) + 1), if_neg (by omega : s - 1 ≠ s + 1)]
    omega
  have hspair' :
      (lam : Nat.Partition N).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  exact BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_target h hst hsource₁ htarget
    hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left hmiddle_two hs_even hspair'
    hj_odd hgap3

lemma BDPartition.isBDMove_of_even_odd_adjacent_branch_of_source_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hspos : 0 < s) (hj : j = s + 1)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition N).rowLen (s - 1) = lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hs_even : Even ((lam : Nat.Partition N).rowLen (s - 1)))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen (s - 1)) :
    IsBDMove lam mu := by
  have hs_even_source : Even ((lam : Nat.Partition N).rowLen s) := by
    rw [← hspair]
    exact hs_even
  have hi0_lt_s : i0 < s :=
    BDPartition.first_strict_lt_even_plateau_bottom hbefore hstrict hi0s hsrow
      hsource hs_even_source
  have hi0pred : i0 ≤ s - 1 := by omega
  have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hks
    exact hone k hsk (by omega)
  have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := BDPartition.prefix_surplus₂_of_even_source hbefore hstrict hi0s
      hsrow hsource hs_even_source hrowBefore
    intro k hsk hkj
    apply htwo k
    · rwa [Nat.sub_add_cancel hspos] at hsk
    · exact hkj
  exact BDPartition.isBDMove_of_even_odd_adjacent_branch h hspos hj hsource htarget
    hgap hspair hmiddle_left hmiddle_two hs_even hj_odd hgap3

lemma BDPartition.isBDMove_of_large_odd_nonadjacent_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle_pair : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hjgap : (lam : Nat.Partition N).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hj2_succ : (j - 2) + 1 = j - 1 := by omega
  have hj2_lt_j : j - 2 + 1 < j := by omega
  have hsource₁ :
      (lam : Nat.Partition N).rowLen (((j - 2) + 1) + 1) <
        lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ]
    have hjpred_succ : (j - 1) + 1 = j := by omega
    rw [hjpred_succ, hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ :
      (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen
          ((j - 2) + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl, if_neg (by omega : j - 2 ≠ (j - 2) + 1),
      if_neg (by omega : j - 2 ≠ j)]
    rw [hj2_succ, hrow_mid, hrow_mid_prev]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j ≠ (j - 2) + 1), if_pos rfl,
      if_pos (by omega : j - 1 = (j - 2) + 1)]
    rw [hrow_mid]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j + 1 <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j ≠ (j - 2) + 1), if_pos rfl,
      if_neg (by omega : j - 2 ≠ (j - 2) + 1),
      if_neg (by omega : j - 2 ≠ j)]
    rw [hrow_mid_prev]
    omega
  have hmid_even : Even ((lam : Nat.Partition N).rowLen (j - 2)) := by
    rcases hs_odd with ⟨a, ha⟩
    rw [hrow_mid_prev]
    refine ⟨a, ?_⟩
    omega
  have hpair : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid_prev, hrow_mid]
  have hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen (j - 2) := by
    rw [hrow_mid_prev]
    omega
  exact BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_target h hj2_lt_j
    hsource₁ htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_pair
    hmiddle_target hmid_even hpair hj_odd hgap3

lemma BDPartition.isBDMove_of_large_odd_nonadjacent_branch_of_pair_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hjgap : (lam : Nat.Partition N).rowLen j + 4 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hi0_pair : i0 ≤ j - 2 := by omega
  have hmiddle_pair : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0_pair
      hrowBefore hstrict
    intro k hjk hkj
    exact hone k hjk (by omega)
  exact BDPartition.isBDMove_of_large_odd_nonadjacent_branch h hsj hmiddle_pair
    hmiddle_target hrow_mid hrow_mid_prev hs_odd hj_odd hjgap

lemma BDPartition.isBDMove_of_odd_even_nonadjacent_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle_left : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hjgap : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hj2_succ : (j - 2) + 1 = j - 1 := by omega
  have hj2_lt_j : j - 2 + 1 < j := by omega
  have hsource₁ :
      (lam : Nat.Partition N).rowLen (((j - 2) + 1) + 1) <
        lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ]
    have hjpred_succ : (j - 1) + 1 = j := by omega
    rw [hjpred_succ, hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ :
      (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen
          ((j - 2) + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl, if_neg (by omega : j - 2 ≠ (j - 2) + 1),
      if_neg (by omega : j - 2 ≠ j)]
    rw [hj2_succ, hrow_mid, hrow_mid_prev]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (j - 2) + 1),
      if_neg (by omega : j + 1 ≠ j), if_neg (by omega : j ≠ (j - 2) + 1),
      if_pos rfl]
    rw [← htpair]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁).rowLen (j - 2) := by
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hj2_lt_j hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (j - 2) + 1),
      if_neg (by omega : j + 1 ≠ j),
      if_neg (by omega : j - 2 ≠ (j - 2) + 1),
      if_neg (by omega : j - 2 ≠ j)]
    rw [← htpair, hrow_mid_prev]
    omega
  have hmid_even : Even ((lam : Nat.Partition N).rowLen (j - 2)) := by
    rcases hs_odd with ⟨a, ha⟩
    rw [hrow_mid_prev]
    refine ⟨a, ?_⟩
    omega
  have hpair : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen ((j - 2) + 1) := by
    rw [hj2_succ, hrow_mid_prev, hrow_mid]
  have hgap2 : (lam : Nat.Partition N).rowLen j + 2 ≤ lam.val.rowLen (j - 2) := by
    rw [hrow_mid_prev]
    omega
  exact BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_targetPair h hj2_lt_j
    hsource₁ htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left
    hmiddle_two hmiddle_right hmid_even hpair hj_even htpair hgap2

lemma BDPartition.isBDMove_of_odd_even_nonadjacent_branch_of_pair_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hrow_mid_prev : (lam : Nat.Partition N).rowLen (j - 2) =
      lam.val.rowLen s - 1)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hjgap : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hi0_pair : i0 ≤ j - 2 := by omega
  have hmiddle_left : ∀ k : ℕ, j - 2 < k → k ≤ (j - 2) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0_pair
      hrowBefore hstrict
    intro k hsk hkj
    exact hone k hsk (by omega)
  exact BDPartition.isBDMove_of_odd_even_nonadjacent_branch h hsj hmiddle_left
    hmiddle_two hmiddle_right hrow_mid hrow_mid_prev hs_odd hj_even htpair hjgap

lemma BDPartition.isBDMove_of_odd_source_large_branch {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hlarge : (lam : Nat.Partition N).rowLen j + 2 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition N).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s)) :
    IsBDMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition N).rowLen j) with hj_even | hj_odd
  · have htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_even_of_prev_lt lam.property hj_even htarget).symm
    have hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen s := by
      omega
    by_cases hadj : j = s + 1
    · have hmiddle₂ : ∀ k : ℕ, s < k → k ≤ j →
          (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus₂_of_odd_source_adjacent h.le hbefore hstrict
          hi0s hadj hsrow hsource hrowBefore hs_odd hgap3
      have hprefix_j : (mu : Nat.Partition N).prefixSum j + 2 ≤
          lam.val.prefixSum j := hmiddle₂ j (by omega) le_rfl
      have hmiddle₁ : ∀ k : ℕ, j < k → k ≤ j + 1 →
          (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus_right_of_even_target h.le hprefix_j hj_even htarget
      exact BDPartition.isBDMove_of_odd_even_adjacent_branch h hadj hsource htarget
        hgap hmiddle₂ hmiddle₁ hs_odd hj_even htpair hgap3
    · have hsj_nonadj : s + 1 < j := by omega
      have hrow_mid_all : ∀ r : ℕ, s + 1 ≤ r → r < j →
          (lam : Nat.Partition N).rowLen r = lam.val.rowLen s - 1 := by
        intro r hsr hrj
        exact rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) hrj
          hsrow hsource hnoDrop
      have hs_j2 : s < j - 2 :=
        BDPartition.two_lt_target_sub_two_of_odd_source hi0s hsj_nonadj hsrow
          hsource hnoDrop hs_odd hlarge
      have hrow_mid :
          (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1 :=
        hrow_mid_all (j - 1) (by omega) (by omega)
      have hrow_mid_prev :
          (lam : Nat.Partition N).rowLen (j - 2) = lam.val.rowLen s - 1 :=
        hrow_mid_all (j - 2) (by omega) (by omega)
      have hmiddle_two : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
          (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus₂_of_odd_source_nonadjacent h.le hbefore hstrict
          hi0s hsj_nonadj hsrow htarget hrowBefore hrow_mid_all hs_odd hgap3
      have hprefix_j : (mu : Nat.Partition N).prefixSum j + 2 ≤
          lam.val.prefixSum j := hmiddle_two j (by omega) le_rfl
      have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
          (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus_right_of_even_target h.le hprefix_j hj_even htarget
      exact BDPartition.isBDMove_of_odd_even_nonadjacent_branch_of_pair_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hmiddle_two hmiddle_right hrow_mid
        hrow_mid_prev hs_odd hj_even htpair hgap3
  · have hgap4 : (lam : Nat.Partition N).rowLen j + 4 ≤ lam.val.rowLen s := by
      rcases hs_odd with ⟨a, ha⟩
      rcases hj_odd with ⟨b, hb⟩
      omega
    by_cases hadj : j = s + 1
    · have hmiddle : ∀ k : ℕ, s < k → k ≤ j →
          (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus₂_of_odd_source_adjacent h.le hbefore hstrict
          hi0s hadj hsrow hsource hrowBefore hs_odd (by omega)
      exact BDPartition.isBDMove_of_large_odd_adjacent_branch h hadj hsource
        htarget hgap hmiddle hs_odd hj_odd hgap4
    · have hsj_nonadj : s + 1 < j := by omega
      have hrow_mid_all : ∀ r : ℕ, s + 1 ≤ r → r < j →
          (lam : Nat.Partition N).rowLen r = lam.val.rowLen s - 1 := by
        intro r hsr hrj
        exact rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) hrj
          hsrow hsource hnoDrop
      have hs_j2 : s < j - 2 :=
        BDPartition.two_lt_target_sub_two_of_odd_source hi0s hsj_nonadj hsrow
          hsource hnoDrop hs_odd hlarge
      have hrow_mid :
          (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1 :=
        hrow_mid_all (j - 1) (by omega) (by omega)
      have hrow_mid_prev :
          (lam : Nat.Partition N).rowLen (j - 2) = lam.val.rowLen s - 1 :=
        hrow_mid_all (j - 2) (by omega) (by omega)
      have hmiddle_target : ∀ k : ℕ, (j - 2) + 1 < k → k ≤ j →
          (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k :=
        BDPartition.prefix_surplus₂_of_odd_source_nonadjacent h.le hbefore hstrict
          hi0s hsj_nonadj hsrow htarget hrowBefore hrow_mid_all hs_odd (by omega)
      exact BDPartition.isBDMove_of_large_odd_nonadjacent_branch_of_pair_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hmiddle_target hrow_mid hrow_mid_prev
        hs_odd hj_odd hgap4

lemma BDPartition.isBDMove_of_even_odd_nonadjacent_exact_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 3) :
    IsBDMove lam mu := by
  have hst : j - 1 < j := by omega
  have hsource : (lam : Nat.Partition N).rowLen ((j - 1) + 1) <
      lam.val.rowLen (j - 1) := by
    rw [Nat.sub_add_cancel (by omega : 0 < j), hrow_mid, hexact]
    omega
  have htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid, hexact]
    omega
  have hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen (j - 1) := by
    rw [hrow_mid, hexact]
    omega
  have hsource_odd : Odd ((lam : Nat.Partition N).rowLen (j - 1)) := by
    rcases hs_even with ⟨a, ha⟩
    rw [hrow_mid]
    refine ⟨a - 1, ?_⟩
    omega
  have hsourceExact :
      (lam : Nat.Partition N).rowLen (j - 1) =
        (lam : Nat.Partition N).rowLen j + 2 := by
    rw [hrow_mid, hexact]
    omega
  have hmu_le_nu :
      (mu : Nat.Partition N) ≤ boxDropPartition lam.val hst hsource htarget hgap :=
    le_boxDropPartition_of_prefix_surplus hst hsource htarget hgap h.le hmiddle
  exact BDPartition.isBDMove_of_boxDrop_odd_exact h hst hsource htarget hgap hmu_le_nu
    hsource_odd hj_odd hsourceExact

lemma BDPartition.isBDMove_of_even_odd_nonadjacent_exact_branch_of_source_surplus
    {N : ℕ} {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen j + 3) :
    IsBDMove lam mu := by
  have hi0pred : i0 ≤ j - 1 := by omega
  have hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hkj
    exact hone k hsk hkj
  exact BDPartition.isBDMove_of_even_odd_nonadjacent_exact_branch h hsj hmiddle
    hrow_mid hs_even hj_odd hexact

lemma BDPartition.isBDMove_of_even_odd_nonadjacent_large_branch {N : ℕ}
    {mu lam : BDPartition N} {s j : ℕ} (h : mu ⋖ lam) (hsj : s + 1 < j)
    (hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hgap5 : (lam : Nat.Partition N).rowLen j + 5 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hst : j - 1 < j := by omega
  have hsource₁ : (lam : Nat.Partition N).rowLen ((j - 1) + 1) <
      lam.val.rowLen (j - 1) := by
    rw [Nat.sub_add_cancel (by omega : 0 < j), hrow_mid]
    omega
  have htarget₁ : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hgap₁ : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1 + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [Nat.sub_add_cancel (by omega : 0 < j)]
    rw [if_neg (by omega : j ≠ j - 1), if_pos rfl,
      if_pos (rfl : j - 1 = j - 1)]
    rw [hrow_mid]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j ≠ j - 1), if_pos rfl,
      if_pos (rfl : j - 1 = j - 1)]
    rw [hrow_mid]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen j + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (j - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁]
    rw [if_neg (by omega : j ≠ j - 1), if_pos rfl,
      if_pos (rfl : j - 1 = j - 1)]
    rw [hrow_mid]
    omega
  have hsource_odd : Odd ((lam : Nat.Partition N).rowLen (j - 1)) := by
    rcases hs_even with ⟨a, ha⟩
    rw [hrow_mid]
    refine ⟨a - 1, ?_⟩
    omega
  have hgap4 :
      (lam : Nat.Partition N).rowLen j + 4 ≤ lam.val.rowLen (j - 1) := by
    rw [hrow_mid]
    omega
  exact BDPartition.isBDMove_of_doubleBoxDrop_same h hst hsource₁ htarget₁ hgap₁
    hsource₂ htarget₂ hgap₂ h.le hmiddle hsource_odd hj_odd hgap4

lemma BDPartition.isBDMove_of_even_odd_nonadjacent_large_branch_of_source_surplus
    {N : ℕ} {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s + 1 < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hrow_mid : (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j))
    (hgap5 : (lam : Nat.Partition N).rowLen j + 5 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  have hmiddle : ∀ k : ℕ, j - 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := BDPartition.prefix_surplus₂_of_even_source hbefore hstrict hi0s
      hsrow hsource hs_even hrowBefore
    intro k hjk hkj
    exact htwo k (by omega) hkj
  exact BDPartition.isBDMove_of_even_odd_nonadjacent_large_branch h hsj hmiddle
    hrow_mid hs_even hj_odd hgap5

lemma BDPartition.isBDMove_of_even_odd_branch_of_source_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition N).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hj_odd : Odd ((lam : Nat.Partition N).rowLen j)) :
    IsBDMove lam mu := by
  rcases exists_prev_rowLen_eq_of_even_of_next_lt lam.property hs_even hsource with
    ⟨hspos, hspair⟩
  have hs_even_prev : Even ((lam : Nat.Partition N).rowLen (s - 1)) := by
    rw [hspair]
    exact hs_even
  have hgap3 : (lam : Nat.Partition N).rowLen j + 3 ≤
      lam.val.rowLen (s - 1) := by
    rw [hspair]
    rcases hs_even with ⟨a, ha⟩
    rcases hj_odd with ⟨b, hb⟩
    omega
  by_cases hadj : j = s + 1
  · exact BDPartition.isBDMove_of_even_odd_adjacent_branch_of_source_surplus h hbefore
      hi0s hspos hadj hsrow hsource htarget hgap hspair hrowBefore hstrict
      hs_even_prev hj_odd hgap3
  · have hsj_nonadj : s + 1 < j := by omega
    have hrow_mid :
        (lam : Nat.Partition N).rowLen (j - 1) = lam.val.rowLen s - 1 :=
      rowLen_eq_pred_of_source_lt_of_noDrop hi0s (by omega) (by omega) hsrow
        hsource hnoDrop
    by_cases hexact : (lam : Nat.Partition N).rowLen s =
        (lam : Nat.Partition N).rowLen j + 3
    · exact BDPartition.isBDMove_of_even_odd_nonadjacent_exact_branch_of_source_surplus h
        hi0s hsj_nonadj hrowBefore hstrict hrow_mid hs_even hj_odd hexact
    · have hgap5 :
          (lam : Nat.Partition N).rowLen j + 5 ≤ lam.val.rowLen s := by
        have hle3 : (lam : Nat.Partition N).rowLen j + 3 ≤ lam.val.rowLen s := by
          rcases hs_even with ⟨a, ha⟩
          rcases hj_odd with ⟨b, hb⟩
          omega
        have hlt3 : (lam : Nat.Partition N).rowLen j + 3 < lam.val.rowLen s :=
          lt_of_le_of_ne hle3 (Ne.symm hexact)
        rcases hs_even with ⟨a, ha⟩
        rcases hj_odd with ⟨b, hb⟩
        omega
      exact BDPartition.isBDMove_of_even_odd_nonadjacent_large_branch_of_source_surplus h
        hbefore hi0s hsj_nonadj hsrow hsource hrowBefore hstrict hrow_mid hs_even
        hj_odd hgap5

lemma BDPartition.isBDMove_of_even_even_branch {N : ℕ} {mu lam : BDPartition N}
    {s j : ℕ} (h : mu ⋖ lam) (hspos : 0 < s) (hsj : s < j)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition N).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen (s - 1)))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (hgap2 : (lam : Nat.Partition N).rowLen j + 2 ≤ lam.val.rowLen (s - 1)) :
    IsBDMove lam mu := by
  have hst : (s - 1) + 1 < j := by
    rw [Nat.sub_add_cancel hspos]
    exact hsj
  have hsource₁ :
      (lam : Nat.Partition N).rowLen (((s - 1) + 1) + 1) <
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hsource
  have hgap₁ :
      (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hgap
  have hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen ((s - 1) + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_pos rfl, if_neg (by omega : s - 1 ≠ (s - 1) + 1),
      if_neg (by omega : s - 1 ≠ j)]
    rw [Nat.sub_add_cancel hspos, hspair]
    omega
  have htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (j + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen j := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (s - 1) + 1),
      if_neg (by omega : j + 1 ≠ j), if_neg (by omega : j ≠ (s - 1) + 1),
      if_pos rfl]
    omega
  have hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (j + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget hgap₁).rowLen (s - 1) := by
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [rowLen_boxDropPartition lam.val hst hsource₁ htarget hgap₁]
    rw [if_neg (by omega : j + 1 ≠ (s - 1) + 1),
      if_neg (by omega : j + 1 ≠ j),
      if_neg (by omega : s - 1 ≠ (s - 1) + 1),
      if_neg (by omega : s - 1 ≠ j)]
    rw [← htpair]
    omega
  have hspair' :
      (lam : Nat.Partition N).rowLen (s - 1) =
        lam.val.rowLen ((s - 1) + 1) := by
    rw [Nat.sub_add_cancel hspos]
    exact hspair
  exact BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_targetPair h hst hsource₁
    htarget hgap₁ hsource₂ htarget₂ hgap₂ h.le hmiddle_left hmiddle_two
    hmiddle_right hs_even hspair' hj_even htpair hgap2

lemma BDPartition.isBDMove_of_even_even_branch_of_source_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hspos : 0 < s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hspair : (lam : Nat.Partition N).rowLen (s - 1) = lam.val.rowLen s)
    (htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1))
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen (s - 1)))
    (hj_even : Even ((lam : Nat.Partition N).rowLen j))
    (hgap2 : (lam : Nat.Partition N).rowLen j + 2 ≤ lam.val.rowLen (s - 1)) :
    IsBDMove lam mu := by
  have hs_even_source : Even ((lam : Nat.Partition N).rowLen s) := by
    rw [← hspair]
    exact hs_even
  have hi0_lt_s : i0 < s :=
    BDPartition.first_strict_lt_even_plateau_bottom hbefore hstrict hi0s hsrow hsource
      hs_even_source
  have hi0pred : i0 ≤ s - 1 := by omega
  have hmiddle_left : ∀ k : ℕ, s - 1 < k → k ≤ (s - 1) + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k := by
    have hone := prefix_surplus_of_rowLen_le_before_target (j := j) hi0pred
      hrowBefore hstrict
    intro k hsk hks
    exact hone k hsk (by omega)
  have hmiddle_two : ∀ k : ℕ, (s - 1) + 1 < k → k ≤ j →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k := by
    have htwo := BDPartition.prefix_surplus₂_of_even_source hbefore hstrict hi0s
      hsrow hsource hs_even_source hrowBefore
    intro k hsk hkj
    apply htwo k
    · rwa [Nat.sub_add_cancel hspos] at hsk
    · exact hkj
  exact BDPartition.isBDMove_of_even_even_branch h hspos hsj hsource htarget hgap
    hspair htpair hmiddle_left hmiddle_two hmiddle_right hs_even hj_even hgap2

lemma BDPartition.isBDMove_of_even_source_branch_of_source_surplus {N : ℕ}
    {mu lam : BDPartition N} {i0 s j : ℕ} (h : mu ⋖ lam)
    (hbefore : ∀ r : ℕ, r < i0 →
      (mu : Nat.Partition N).rowLen r = lam.val.rowLen r)
    (hi0s : i0 ≤ s) (hsj : s < j)
    (hsrow : (lam : Nat.Partition N).rowLen s = lam.val.rowLen i0)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen j < lam.val.rowLen (j - 1))
    (hgap : (lam : Nat.Partition N).rowLen j + 1 < lam.val.rowLen s)
    (hnoDrop : ∀ r : ℕ, i0 ≤ r → r < j →
      ¬(lam : Nat.Partition N).rowLen r + 1 < lam.val.rowLen i0)
    (hrowBefore : ∀ r : ℕ, r < j →
      (mu : Nat.Partition N).rowLen r ≤ lam.val.rowLen r)
    (hstrict : (mu : Nat.Partition N).rowLen i0 < lam.val.rowLen i0)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s)) :
    IsBDMove lam mu := by
  rcases Nat.even_or_odd ((lam : Nat.Partition N).rowLen j) with hj_even | hj_even
  · rcases exists_prev_rowLen_eq_of_even_of_next_lt lam.property hs_even hsource with
      ⟨hspos, hspair⟩
    have htpair : (lam : Nat.Partition N).rowLen j = lam.val.rowLen (j + 1) :=
      (next_rowLen_eq_of_even_of_prev_lt lam.property hj_even htarget).symm
    have hs_even_prev : Even ((lam : Nat.Partition N).rowLen (s - 1)) := by
      rw [hspair]
      exact hs_even
    have hgap2 :
        (lam : Nat.Partition N).rowLen j + 2 ≤ lam.val.rowLen (s - 1) := by
      rw [hspair]
      rcases hs_even with ⟨a, ha⟩
      rcases hj_even with ⟨b, hb⟩
      omega
    have hprefix_j : (mu : Nat.Partition N).prefixSum j + 2 ≤
        lam.val.prefixSum j := by
      have htwo := BDPartition.prefix_surplus₂_of_even_source hbefore hstrict hi0s
        hsrow hsource hs_even hrowBefore
      exact htwo j hsj le_rfl
    have hmiddle_right : ∀ k : ℕ, j < k → k ≤ j + 1 →
        (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k :=
      BDPartition.prefix_surplus_right_of_even_target h.le hprefix_j hj_even htarget
    exact BDPartition.isBDMove_of_even_even_branch_of_source_surplus h hbefore hi0s hspos
      hsj hsrow hsource htarget hgap hspair htpair hrowBefore hstrict hmiddle_right
      hs_even_prev hj_even hgap2
  · exact BDPartition.isBDMove_of_even_odd_branch_of_source_surplus h hbefore hi0s hsj
      hsrow hsource htarget hgap hnoDrop hrowBefore hstrict hs_even hj_even

/-- A B/D-type dominance cover has one of Hesselink's five visible move shapes. -/
theorem BDPartition.isBDMove_of_covBy {N : ℕ} {mu lam : BDPartition N} (h : mu ⋖ lam) :
    IsBDMove lam mu := by
  classical
  rcases nonempty_firstDropData_of_lt (bdPartition_lt_iff.mp h.lt) with ⟨D⟩
  rcases nonempty_plateauSourceData (lam : Nat.Partition N) D.hi0j
    (lt_trans (Nat.lt_succ_self _) D.hgap_i0) with ⟨S⟩
  have htarget : (lam : Nat.Partition N).rowLen D.j < lam.val.rowLen (D.j - 1) :=
    D.rowLen_j_lt_pred
  have hgap : (lam : Nat.Partition N).rowLen D.j + 1 < lam.val.rowLen S.s := by
    rw [S.hsrow]
    exact D.hgap_i0
  by_cases hexact : (lam : Nat.Partition N).rowLen S.s =
      (lam : Nat.Partition N).rowLen D.j + 2
  · exact BDPartition.isBDMove_of_exact_branch_of_source_surplus h D.hbefore S.hi0s
      S.hsj S.hsrow S.hsource htarget hgap D.hrowBefore D.hstrict hexact
  · have hlarge : (lam : Nat.Partition N).rowLen D.j + 2 < lam.val.rowLen S.s :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hgap) (Ne.symm hexact)
    rcases Nat.even_or_odd ((lam : Nat.Partition N).rowLen S.s) with hs_even | hs_odd
    · exact BDPartition.isBDMove_of_even_source_branch_of_source_surplus h D.hbefore
        S.hi0s S.hsj S.hsrow S.hsource htarget hgap D.hnoDrop D.hrowBefore
        D.hstrict hs_even
    · exact BDPartition.isBDMove_of_odd_source_large_branch h D.hbefore S.hi0s S.hsj
        S.hsrow S.hsource htarget hgap hlarge D.hnoDrop D.hrowBefore D.hstrict hs_odd


end Nat.Partition


