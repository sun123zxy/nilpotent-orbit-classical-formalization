import NilpotentOrbitClassicalFormalization.Dominance.CoverBD.Admissibility
import NilpotentOrbitClassicalFormalization.Dominance.DoubleDrop

/-!
# B/D-type double-drop constructions

This file extracts B/D move shapes from one-box and two-box drop constructions.
-/

namespace Nat.Partition

lemma isBDMove₂_of_eq_doubleBoxDrop_same {N : ℕ} {lam nu : Nat.Partition N}
    {s t : ℕ} (hst : s < t)
    (hsource₁ : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget₁ : lam.rowLen t < lam.rowLen (t - 1))
    (hgap₁ : lam.rowLen t + 1 < lam.rowLen s)
    (hsource₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hs_odd : Odd (lam.rowLen s)) (ht_odd : Odd (lam.rowLen t))
    (hgap4 : lam.rowLen t + 4 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        hst hsource₂ htarget₂ hgap₂) :
    IsBDMove₂ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  refine ⟨s, t, hst, hs_odd, ht_odd, hgap4, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hst hsource₂ htarget₂ hgap₂).rowLen s + 2
    rw [rowLen_boxDropPartition rho hst hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s - 1 by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      rw [if_pos rfl]]
    omega
  · change (boxDropPartition rho hst hsource₂ htarget₂ hgap₂).rowLen t =
      lam.rowLen t + 2
    rw [rowLen_boxDropPartition rho hst hsource₂ htarget₂ hgap₂]
    rw [if_neg (ne_of_gt hst), if_pos rfl]
    rw [show rho.rowLen t = lam.rowLen t + 1 by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      simp [ne_of_gt hst]]
  · intro k hks hkt
    change (boxDropPartition rho hst hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hst hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks, hkt]

lemma isBDMove₃_of_eq_doubleBoxDrop_source_pairTarget {N : ℕ}
    {lam nu : Nat.Partition N} {s t : ℕ} (hst : s < t)
    (hsource₁ : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget₁ : lam.rowLen t < lam.rowLen (t - 1))
    (hgap₁ : lam.rowLen t + 1 < lam.rowLen s)
    (hsource₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hs_odd : Odd (lam.rowLen s)) (ht_even : Even (lam.rowLen t))
    (htpair : lam.rowLen t = lam.rowLen (t + 1))
    (hgap3 : lam.rowLen t + 3 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂) :
    IsBDMove₃ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hst1 : s < t + 1 := lt_trans hst (Nat.lt_succ_self t)
  refine ⟨s, t, hst, hs_odd, ht_even, htpair, hgap3, ?_, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen s + 2
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s - 1 by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      rw [if_pos rfl]]
    omega
  · change (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen t =
      lam.rowLen t + 1
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    rw [if_neg (ne_of_gt hst), if_neg (by omega : t ≠ t + 1)]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [ne_of_gt hst]
  · change (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen (t + 1) =
      lam.rowLen (t + 1) + 1
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    have ht1s : t + 1 ≠ s := by omega
    rw [if_neg ht1s, if_pos rfl]
    change rho.rowLen (t + 1) + 1 = lam.rowLen (t + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    have ht1t : t + 1 ≠ t := by omega
    rw [if_neg ht1s, if_neg ht1t]
  · intro k hks hkt hkt1
    change (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks, hkt]

lemma isBDMove₄_of_eq_doubleBoxDrop_sourcePair_target {N : ℕ}
    {lam nu : Nat.Partition N} {s t : ℕ} (hst : s + 1 < t)
    (hsource₁ : lam.rowLen ((s + 1) + 1) < lam.rowLen (s + 1))
    (htarget₁ : lam.rowLen t < lam.rowLen (t - 1))
    (hgap₁ : lam.rowLen t + 1 < lam.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hs_even : Even (lam.rowLen s)) (hspair : lam.rowLen s = lam.rowLen (s + 1))
    (ht_odd : Odd (lam.rowLen t)) (hgap3 : lam.rowLen t + 3 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂) :
    IsBDMove₄ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hslt : s < t := lt_trans (Nat.lt_succ_self s) hst
  refine ⟨s, t, hst, hs_even, hspair, ht_odd, hgap3, ?_, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen s + 1
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      have hss1 : s ≠ s + 1 := by omega
      have hst_ne : s ≠ t := by omega
      rw [if_neg hss1, if_neg hst_ne]]
    have hpos : 0 < lam.rowLen s := by omega
    omega
  · change lam.rowLen (s + 1) =
      (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen (s + 1) + 1
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    have hs1s : s + 1 ≠ s := by omega
    have hs1t : s + 1 ≠ t := by omega
    rw [if_neg hs1s, if_neg hs1t]
    change lam.rowLen (s + 1) = rho.rowLen (s + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl]
    have hpos : 0 < lam.rowLen (s + 1) := by
      rw [← hspair]
      omega
    omega
  · change (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen t =
      lam.rowLen t + 2
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    rw [if_neg (ne_of_gt hslt), if_pos rfl]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [ne_of_gt hst]
  · intro k hks hks1 hkt
    change (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks1, hkt]

lemma isBDMove₅_of_eq_doubleBoxDrop_sourcePair_targetPair {N : ℕ}
    {lam nu : Nat.Partition N} {s t : ℕ} (hst : s + 1 < t)
    (hsource₁ : lam.rowLen ((s + 1) + 1) < lam.rowLen (s + 1))
    (htarget₁ : lam.rowLen t < lam.rowLen (t - 1))
    (hgap₁ : lam.rowLen t + 1 < lam.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hs_even : Even (lam.rowLen s)) (hspair : lam.rowLen s = lam.rowLen (s + 1))
    (ht_even : Even (lam.rowLen t)) (htpair : lam.rowLen t = lam.rowLen (t + 1))
    (hgap2 : lam.rowLen t + 2 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
        hsource₂ htarget₂ hgap₂) :
    IsBDMove₅ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hslt1 : s < t + 1 :=
    lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t))
  refine ⟨s, t, hst, hs_even, hspair, ht_even, htpair, hgap2, ?_, ?_, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen s + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      have hss1 : s ≠ s + 1 := by omega
      have hst_ne : s ≠ t := by omega
      rw [if_neg hss1, if_neg hst_ne]]
    have hpos : 0 < lam.rowLen s := by omega
    omega
  · change lam.rowLen (s + 1) =
      (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen (s + 1) + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have hs1s : s + 1 ≠ s := by omega
    have hs1t1 : s + 1 ≠ t + 1 := by omega
    rw [if_neg hs1s, if_neg hs1t1]
    change lam.rowLen (s + 1) = rho.rowLen (s + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl]
    have hpos : 0 < lam.rowLen (s + 1) := by
      rw [← hspair]
      omega
    omega
  · change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen t =
      lam.rowLen t + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have hts : t ≠ s := by omega
    have htt1 : t ≠ t + 1 := by omega
    rw [if_neg hts, if_neg htt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [ne_of_gt hst]
  · change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen (t + 1) =
      lam.rowLen (t + 1) + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have ht1s : t + 1 ≠ s := by omega
    rw [if_neg ht1s, if_pos rfl]
    change rho.rowLen (t + 1) + 1 = lam.rowLen (t + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    have ht1s1 : t + 1 ≠ s + 1 := by omega
    have ht1t : t + 1 ≠ t := by omega
    rw [if_neg ht1s1, if_neg ht1t]
  · intro k hks hks1 hkt hkt1
    change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks1, hkt]

lemma isBDMove₁_of_eq_boxDropPartition_odd_exact {N : ℕ}
    {lam nu : Nat.Partition N} {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hs_odd : Odd (lam.rowLen s)) (ht_odd : Odd (lam.rowLen t))
    (hexact : lam.rowLen s = lam.rowLen t + 2)
    (hnu : nu = boxDropPartition lam hst hsource htarget hgap) :
    IsBDMove₁ lam nu := by
  subst nu
  refine ⟨s, t, hst, hs_odd, ht_odd, hexact, ?_, ?_, ?_⟩
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap, if_pos rfl]
    omega
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [ne_of_gt hst]
  · intro k hks hkt
    rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [hks, hkt]

lemma BDPartition.isBDMove_of_boxDrop_odd_exact {N : ℕ} {mu lam : BDPartition N}
    {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition N).rowLen t < lam.val.rowLen (t - 1))
    (hgap : (lam : Nat.Partition N).rowLen t + 1 < lam.val.rowLen s)
    (hmu_le_nu :
      (mu : Nat.Partition N) ≤ boxDropPartition lam.val hst hsource htarget hgap)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (ht_odd : Odd ((lam : Nat.Partition N).rowLen t))
    (hexact : (lam : Nat.Partition N).rowLen s =
      (lam : Nat.Partition N).rowLen t + 2) :
    IsBDMove lam mu := by
  apply BDPartition.isBDMove_of_between_isBDMove₁ h hmu_le_nu
  · exact boxDropPartition_le_original lam.val hst hsource htarget hgap
  · intro hEq
    have hlt := boxDropPartition_lt_original lam.val hst hsource htarget hgap
    exact hlt.ne hEq
  · exact isBDMove₁_of_eq_boxDropPartition_odd_exact hst hsource htarget hgap
      hs_odd ht_odd hexact rfl

lemma BDPartition.isBDMove_of_doubleBoxDrop_same {N : ℕ} {mu lam : BDPartition N}
    {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource₁ : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget₁ : (lam : Nat.Partition N).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition N).rowLen t + 1 < lam.val.rowLen s)
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition N) ≤ lam)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ t →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (ht_odd : Odd ((lam : Nat.Partition N).rowLen t))
    (hgap4 : (lam : Nat.Partition N).rowLen t + 4 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    hst hsource₂ htarget₂ hgap₂
  apply BDPartition.isBDMove_of_between_isBDMove₂ (nu := nu) h
  · exact le_doubleBoxDrop_same_of_prefix_surplus₂ hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle
  · exact doubleBoxDrop_same_le_original lam.val hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_same_ne_original lam.val hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂
  · exact isBDMove₂_of_eq_doubleBoxDrop_same hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hs_odd ht_odd hgap4 rfl

lemma BDPartition.isBDMove_of_doubleBoxDrop_source_pairTarget {N : ℕ}
    {mu lam : BDPartition N} {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource₁ : (lam : Nat.Partition N).rowLen (s + 1) < lam.val.rowLen s)
    (htarget₁ : (lam : Nat.Partition N).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition N).rowLen t + 1 < lam.val.rowLen s)
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition N) ≤ lam)
    (hmiddle₂ : ∀ k : ℕ, s < k → k ≤ t →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle₁ : ∀ k : ℕ, t < k → k ≤ t + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_odd : Odd ((lam : Nat.Partition N).rowLen s))
    (ht_even : Even ((lam : Nat.Partition N).rowLen t))
    (htpair : (lam : Nat.Partition N).rowLen t = lam.val.rowLen (t + 1))
    (hgap3 : (lam : Nat.Partition N).rowLen t + 3 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂
  apply BDPartition.isBDMove_of_between_isBDMove₃ (nu := nu) h
  · exact le_doubleBoxDrop_source_pairTarget_of_prefix_surplus hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle₂ hmiddle₁
  · exact doubleBoxDrop_source_pairTarget_le_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_source_pairTarget_ne_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact isBDMove₃_of_eq_doubleBoxDrop_source_pairTarget hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hs_odd ht_even htpair hgap3 rfl

lemma BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_target {N : ℕ}
    {mu lam : BDPartition N} {s t : ℕ} (h : mu ⋖ lam) (hst : s + 1 < t)
    (hsource₁ :
      (lam : Nat.Partition N).rowLen ((s + 1) + 1) < lam.val.rowLen (s + 1))
    (htarget₁ : (lam : Nat.Partition N).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition N).rowLen t + 1 < lam.val.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition N) ≤ lam)
    (hmiddle₁ : ∀ k : ℕ, s < k → k ≤ s + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle₂ : ∀ k : ℕ, s + 1 < k → k ≤ t →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hspair : (lam : Nat.Partition N).rowLen s = lam.val.rowLen (s + 1))
    (ht_odd : Odd ((lam : Nat.Partition N).rowLen t))
    (hgap3 : (lam : Nat.Partition N).rowLen t + 3 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂
  apply BDPartition.isBDMove_of_between_isBDMove₄ (nu := nu) h
  · exact le_doubleBoxDrop_sourcePair_target_of_prefix_surplus hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle₁ hmiddle₂
  · exact doubleBoxDrop_sourcePair_target_le_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_sourcePair_target_ne_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact isBDMove₄_of_eq_doubleBoxDrop_sourcePair_target hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hs_even hspair ht_odd hgap3 rfl

lemma BDPartition.isBDMove_of_doubleBoxDrop_sourcePair_targetPair {N : ℕ}
    {mu lam : BDPartition N} {s t : ℕ} (h : mu ⋖ lam) (hst : s + 1 < t)
    (hsource₁ :
      (lam : Nat.Partition N).rowLen ((s + 1) + 1) < lam.val.rowLen (s + 1))
    (htarget₁ : (lam : Nat.Partition N).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition N).rowLen t + 1 < lam.val.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition N) ≤ lam)
    (hmiddle_left : ∀ k : ℕ, s < k → k ≤ s + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, s + 1 < k → k ≤ t →
      (mu : Nat.Partition N).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, t < k → k ≤ t + 1 →
      (mu : Nat.Partition N).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hs_even : Even ((lam : Nat.Partition N).rowLen s))
    (hspair : (lam : Nat.Partition N).rowLen s = lam.val.rowLen (s + 1))
    (ht_even : Even ((lam : Nat.Partition N).rowLen t))
    (htpair : (lam : Nat.Partition N).rowLen t = lam.val.rowLen (t + 1))
    (hgap2 : (lam : Nat.Partition N).rowLen t + 2 ≤ lam.val.rowLen s) :
    IsBDMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
    hsource₂ htarget₂ hgap₂
  apply BDPartition.isBDMove_of_between_isBDMove₅ (nu := nu) h
  · exact le_doubleBoxDrop_sourcePair_targetPair_of_prefix_surplus hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle_left
      hmiddle_two hmiddle_right
  · exact doubleBoxDrop_sourcePair_targetPair_le_original lam.val hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_sourcePair_targetPair_ne_original lam.val hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂
  · exact isBDMove₅_of_eq_doubleBoxDrop_sourcePair_targetPair hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hs_even hspair ht_even htpair hgap2 rfl


end Nat.Partition





