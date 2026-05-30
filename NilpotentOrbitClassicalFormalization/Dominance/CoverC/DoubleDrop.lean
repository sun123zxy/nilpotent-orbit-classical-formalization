import NilpotentOrbitClassicalFormalization.Dominance.CoverC.Admissibility
import NilpotentOrbitClassicalFormalization.Dominance.DoubleDrop

/-!
# C-type double-drop constructions

Split from `Dominance/CoverC.lean` to keep the C-type cover formalization navigable.
-/

namespace Nat.Partition

lemma isCMove₂_of_eq_doubleBoxDrop_same {N : ℕ} {lam nu : Nat.Partition N}
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
    (hseven : Even (lam.rowLen s)) (hteven : Even (lam.rowLen t))
    (hgap4 : lam.rowLen t + 4 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        hst hsource₂ htarget₂ hgap₂) :
    IsCMove₂ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  refine ⟨s, t, hst, hseven, hteven, hgap4, ?_, ?_, ?_⟩
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

lemma isCMove₃_of_eq_doubleBoxDrop_source_pairTarget {N : ℕ}
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
    (hseven : Even (lam.rowLen s)) (htodd : Odd (lam.rowLen t))
    (htpair : lam.rowLen t = lam.rowLen (t + 1))
    (hgap3 : lam.rowLen t + 3 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂) :
    IsCMove₃ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hst1 : s < t + 1 := lt_trans hst (Nat.lt_succ_self t)
  refine ⟨s, t, hst, hseven, htodd, htpair, hgap3, ?_, ?_, ?_, ?_⟩
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
    rw [if_neg (ne_of_gt hst), if_neg (by linarith : t ≠ t + 1)]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [ne_of_gt hst]
  · change (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen (t + 1) =
      lam.rowLen (t + 1) + 1
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    have ht1s : t + 1 ≠ s := by linarith
    rw [if_neg ht1s, if_pos rfl]
    change rho.rowLen (t + 1) + 1 = lam.rowLen (t + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    have ht1t : t + 1 ≠ t := by linarith
    rw [if_neg ht1s, if_neg ht1t]
  · intro k hks hkt hkt1
    change (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks, hkt]

lemma isCMove₄_of_eq_doubleBoxDrop_sourcePair_target {N : ℕ}
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
    (hsodd : Odd (lam.rowLen s)) (hspair : lam.rowLen s = lam.rowLen (s + 1))
    (hteven : Even (lam.rowLen t)) (hgap3 : lam.rowLen t + 3 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂) :
    IsCMove₄ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hslt : s < t := lt_trans (Nat.lt_succ_self s) hst
  refine ⟨s, t, hst, hsodd, hspair, hteven, hgap3, ?_, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen s + 1
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      have hss1 : s ≠ s + 1 := by linarith
      have hst_ne : s ≠ t := by linarith
      rw [if_neg hss1, if_neg hst_ne]]
    have hpos : 0 < lam.rowLen s := hsodd.pos
    omega
  · change lam.rowLen (s + 1) =
      (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).rowLen (s + 1) + 1
    rw [rowLen_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
    have hs1s : s + 1 ≠ s := by linarith
    have hs1t : s + 1 ≠ t := by linarith
    rw [if_neg hs1s, if_neg hs1t]
    change lam.rowLen (s + 1) = rho.rowLen (s + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl]
    have hpos : 0 < lam.rowLen (s + 1) := by
      rw [← hspair]
      exact hsodd.pos
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

lemma isCMove₅_of_eq_doubleBoxDrop_sourcePair_targetPair {N : ℕ}
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
    (hsodd : Odd (lam.rowLen s)) (hspair : lam.rowLen s = lam.rowLen (s + 1))
    (htodd : Odd (lam.rowLen t)) (htpair : lam.rowLen t = lam.rowLen (t + 1))
    (hgap2 : lam.rowLen t + 2 ≤ lam.rowLen s)
    (hnu : nu =
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
        hsource₂ htarget₂ hgap₂) :
    IsCMove₅ lam nu := by
  subst nu
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  have hslt1 : s < t + 1 :=
    lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t))
  refine ⟨s, t, hst, hsodd, hspair, htodd, htpair, hgap2, ?_, ?_, ?_, ?_, ?_⟩
  · change lam.rowLen s =
      (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen s + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    rw [if_pos rfl]
    rw [show rho.rowLen s = lam.rowLen s by
      dsimp [rho]
      rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
      have hss1 : s ≠ s + 1 := by linarith
      have hst_ne : s ≠ t := by linarith
      rw [if_neg hss1, if_neg hst_ne]]
    have hpos : 0 < lam.rowLen s := hsodd.pos
    omega
  · change lam.rowLen (s + 1) =
      (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen (s + 1) + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have hs1s : s + 1 ≠ s := by linarith
    have hs1t1 : s + 1 ≠ t + 1 := by linarith
    rw [if_neg hs1s, if_neg hs1t1]
    change lam.rowLen (s + 1) = rho.rowLen (s + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    rw [if_pos rfl]
    have hpos : 0 < lam.rowLen (s + 1) := by
      rw [← hspair]
      exact hsodd.pos
    omega
  · change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen t =
      lam.rowLen t + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have hts : t ≠ s := by linarith
    have htt1 : t ≠ t + 1 := by linarith
    rw [if_neg hts, if_neg htt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [ne_of_gt hst]
  · change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen (t + 1) =
      lam.rowLen (t + 1) + 1
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    have ht1s : t + 1 ≠ s := by linarith
    rw [if_neg ht1s, if_pos rfl]
    change rho.rowLen (t + 1) + 1 = lam.rowLen (t + 1) + 1
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    have ht1s1 : t + 1 ≠ s + 1 := by linarith
    have ht1t : t + 1 ≠ t := by linarith
    rw [if_neg ht1s1, if_neg ht1t]
  · intro k hks hks1 hkt hkt1
    change (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).rowLen k =
      lam.rowLen k
    rw [rowLen_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
    rw [if_neg hks, if_neg hkt1]
    dsimp [rho]
    rw [rowLen_boxDropPartition lam hst hsource₁ htarget₁ hgap₁]
    simp [hks1, hkt]

lemma isCMove₁_of_eq_boxDropPartition_even_exact {N : ℕ}
    {lam nu : Nat.Partition N} {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hseven : Even (lam.rowLen s)) (hteven : Even (lam.rowLen t))
    (hexact : lam.rowLen s = lam.rowLen t + 2)
    (hnu : nu = boxDropPartition lam hst hsource htarget hgap) :
    IsCMove₁ lam nu := by
  subst nu
  refine ⟨s, t, hst, hseven, hteven, hexact, ?_, ?_, ?_⟩
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap, if_pos rfl]
    omega
  · rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [ne_of_gt hst]
  · intro k hks hkt
    rw [rowLen_boxDropPartition lam hst hsource htarget hgap]
    simp [hks, hkt]

lemma CPartition.isCMove_of_boxDrop_even_exact {n : ℕ} {mu lam : CPartition n}
    {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget : (lam : Nat.Partition (2 * n)).rowLen t < lam.val.rowLen (t - 1))
    (hgap : (lam : Nat.Partition (2 * n)).rowLen t + 1 < lam.val.rowLen s)
    (hmu_le_nu :
      (mu : Nat.Partition (2 * n)) ≤ boxDropPartition lam.val hst hsource htarget hgap)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hteven : Even ((lam : Nat.Partition (2 * n)).rowLen t))
    (hexact : (lam : Nat.Partition (2 * n)).rowLen s =
      (lam : Nat.Partition (2 * n)).rowLen t + 2) :
    IsCMove lam mu := by
  apply CPartition.isCMove_of_between_isCMove₁ h hmu_le_nu
  · exact boxDropPartition_le_original lam.val hst hsource htarget hgap
  · intro hEq
    have hlt := boxDropPartition_lt_original lam.val hst hsource htarget hgap
    exact hlt.ne hEq
  · exact isCMove₁_of_eq_boxDropPartition_even_exact hst hsource htarget hgap
      hseven hteven hexact rfl

lemma CPartition.isCMove_of_doubleBoxDrop_same {n : ℕ} {mu lam : CPartition n}
    {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource₁ : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget₁ : (lam : Nat.Partition (2 * n)).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition (2 * n)).rowLen t + 1 < lam.val.rowLen s)
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ t →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (hteven : Even ((lam : Nat.Partition (2 * n)).rowLen t))
    (hgap4 : (lam : Nat.Partition (2 * n)).rowLen t + 4 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    hst hsource₂ htarget₂ hgap₂
  apply CPartition.isCMove_of_between_isCMove₂ (nu := nu) h
  · exact le_doubleBoxDrop_same_of_prefix_surplus₂ hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle
  · exact doubleBoxDrop_same_le_original lam.val hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_same_ne_original lam.val hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂
  · exact isCMove₂_of_eq_doubleBoxDrop_same hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hseven hteven hgap4 rfl

lemma CPartition.isCMove_of_doubleBoxDrop_source_pairTarget {n : ℕ}
    {mu lam : CPartition n} {s t : ℕ} (h : mu ⋖ lam) (hst : s < t)
    (hsource₁ : (lam : Nat.Partition (2 * n)).rowLen (s + 1) < lam.val.rowLen s)
    (htarget₁ : (lam : Nat.Partition (2 * n)).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition (2 * n)).rowLen t + 1 < lam.val.rowLen s)
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hmiddle₂ : ∀ k : ℕ, s < k → k ≤ t →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle₁ : ∀ k : ℕ, t < k → k ≤ t + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hseven : Even ((lam : Nat.Partition (2 * n)).rowLen s))
    (htodd : Odd ((lam : Nat.Partition (2 * n)).rowLen t))
    (htpair : (lam : Nat.Partition (2 * n)).rowLen t = lam.val.rowLen (t + 1))
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen t + 3 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂
  apply CPartition.isCMove_of_between_isCMove₃ (nu := nu) h
  · exact le_doubleBoxDrop_source_pairTarget_of_prefix_surplus hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle₂ hmiddle₁
  · exact doubleBoxDrop_source_pairTarget_le_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_source_pairTarget_ne_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact isCMove₃_of_eq_doubleBoxDrop_source_pairTarget hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hseven htodd htpair hgap3 rfl

lemma CPartition.isCMove_of_doubleBoxDrop_sourcePair_target {n : ℕ}
    {mu lam : CPartition n} {s t : ℕ} (h : mu ⋖ lam) (hst : s + 1 < t)
    (hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen ((s + 1) + 1) < lam.val.rowLen (s + 1))
    (htarget₁ : (lam : Nat.Partition (2 * n)).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition (2 * n)).rowLen t + 1 < lam.val.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t - 1))
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hmiddle₁ : ∀ k : ℕ, s < k → k ≤ s + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle₂ : ∀ k : ℕ, s + 1 < k → k ≤ t →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hspair : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen (s + 1))
    (hteven : Even ((lam : Nat.Partition (2 * n)).rowLen t))
    (hgap3 : (lam : Nat.Partition (2 * n)).rowLen t + 3 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂
  apply CPartition.isCMove_of_between_isCMove₄ (nu := nu) h
  · exact le_doubleBoxDrop_sourcePair_target_of_prefix_surplus hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle₁ hmiddle₂
  · exact doubleBoxDrop_sourcePair_target_le_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_sourcePair_target_ne_original lam.val hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂
  · exact isCMove₄_of_eq_doubleBoxDrop_sourcePair_target hst hsource₁ htarget₁ hgap₁
      hsource₂ htarget₂ hgap₂ hsodd hspair hteven hgap3 rfl

lemma CPartition.isCMove_of_doubleBoxDrop_sourcePair_targetPair {n : ℕ}
    {mu lam : CPartition n} {s t : ℕ} (h : mu ⋖ lam) (hst : s + 1 < t)
    (hsource₁ :
      (lam : Nat.Partition (2 * n)).rowLen ((s + 1) + 1) < lam.val.rowLen (s + 1))
    (htarget₁ : (lam : Nat.Partition (2 * n)).rowLen t < lam.val.rowLen (t - 1))
    (hgap₁ : (lam : Nat.Partition (2 * n)).rowLen t + 1 < lam.val.rowLen (s + 1))
    (hsource₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (s + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (htarget₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen t)
    (hgap₂ :
      (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen (t + 1) + 1 <
        (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁).rowLen s)
    (hmu_le_lam : (mu : Nat.Partition (2 * n)) ≤ lam)
    (hmiddle_left : ∀ k : ℕ, s < k → k ≤ s + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hmiddle_two : ∀ k : ℕ, s + 1 < k → k ≤ t →
      (mu : Nat.Partition (2 * n)).prefixSum k + 2 ≤ lam.val.prefixSum k)
    (hmiddle_right : ∀ k : ℕ, t < k → k ≤ t + 1 →
      (mu : Nat.Partition (2 * n)).prefixSum k + 1 ≤ lam.val.prefixSum k)
    (hsodd : Odd ((lam : Nat.Partition (2 * n)).rowLen s))
    (hspair : (lam : Nat.Partition (2 * n)).rowLen s = lam.val.rowLen (s + 1))
    (htodd : Odd ((lam : Nat.Partition (2 * n)).rowLen t))
    (htpair : (lam : Nat.Partition (2 * n)).rowLen t = lam.val.rowLen (t + 1))
    (hgap2 : (lam : Nat.Partition (2 * n)).rowLen t + 2 ≤ lam.val.rowLen s) :
    IsCMove lam mu := by
  let nu := boxDropPartition (boxDropPartition lam.val hst hsource₁ htarget₁ hgap₁)
    (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
    hsource₂ htarget₂ hgap₂
  apply CPartition.isCMove_of_between_isCMove₅ (nu := nu) h
  · exact le_doubleBoxDrop_sourcePair_targetPair_of_prefix_surplus hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂ hmu_le_lam hmiddle_left
      hmiddle_two hmiddle_right
  · exact doubleBoxDrop_sourcePair_targetPair_le_original lam.val hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂
  · exact doubleBoxDrop_sourcePair_targetPair_ne_original lam.val hst hsource₁
      htarget₁ hgap₁ hsource₂ htarget₂ hgap₂
  · exact isCMove₅_of_eq_doubleBoxDrop_sourcePair_targetPair hst hsource₁ htarget₁
      hgap₁ hsource₂ htarget₂ hgap₂ hsodd hspair htodd htpair hgap2 rfl


end Nat.Partition

