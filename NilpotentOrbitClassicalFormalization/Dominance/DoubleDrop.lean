import NilpotentOrbitClassicalFormalization.Dominance.CoverA

/-!
# Shared double-drop constructions

This file contains the C/B/D-independent order facts for two successive one-box
drops. The classical-type files interpret these constructions as their own move
shapes.
-/

namespace Nat.Partition
lemma doubleBoxDrop_same_le_original {N : ℕ} (lam : Nat.Partition N)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      hst hsource₂ htarget₂ hgap₂ ≤ lam := by
  exact le_trans
    (boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      hst hsource₂ htarget₂ hgap₂)
    (boxDropPartition_le_original lam hst hsource₁ htarget₁ hgap₁)

lemma doubleBoxDrop_same_ne_original {N : ℕ} (lam : Nat.Partition N)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      hst hsource₂ htarget₂ hgap₂ ≠ lam := by
  have hle :
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        hst hsource₂ htarget₂ hgap₂ ≤
        boxDropPartition lam hst hsource₁ htarget₁ hgap₁ :=
    boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      hst hsource₂ htarget₂ hgap₂
  have hlt : boxDropPartition lam hst hsource₁ htarget₁ hgap₁ < lam :=
    boxDropPartition_lt_original lam hst hsource₁ htarget₁ hgap₁
  intro hEq
  apply hlt.2
  simpa [hEq] using hle

lemma le_doubleBoxDrop_same_of_prefix_surplus₂ {N : ℕ}
    {mu lam : Nat.Partition N} {s t : ℕ} (hst : s < t)
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
    (hmu_le_lam : mu ≤ lam)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ t → mu.prefixSum k + 2 ≤ lam.prefixSum k) :
    mu ≤ boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      hst hsource₂ htarget₂ hgap₂ := by
  intro k
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  change mu.prefixSum k ≤ (boxDropPartition rho hst hsource₂ htarget₂ hgap₂).prefixSum k
  rw [prefixSum_boxDropPartition rho hst hsource₂ htarget₂ hgap₂]
  by_cases hmid : s < k ∧ k ≤ t
  · rw [if_pos hmid]
    rw [show rho.prefixSum k = lam.prefixSum k - 1 by
      dsimp [rho]
      exact prefixSum_boxDropPartition_of_mid lam hst hsource₁ htarget₁ hgap₁ hmid]
    have hsurplus := hmiddle k hmid.1 hmid.2
    omega
  · rw [if_neg hmid]
    rw [show rho.prefixSum k = lam.prefixSum k by
      dsimp [rho]
      exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid]
    exact hmu_le_lam k

lemma doubleBoxDrop_source_pairTarget_le_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂ ≤ lam := by
  exact le_trans
    (boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂)
    (boxDropPartition_le_original lam hst hsource₁ htarget₁ hgap₁)

lemma doubleBoxDrop_source_pairTarget_ne_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂ ≠ lam := by
  have hle :
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂ ≤
        boxDropPartition lam hst hsource₁ htarget₁ hgap₁ :=
    boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂
  have hlt : boxDropPartition lam hst hsource₁ htarget₁ hgap₁ < lam :=
    boxDropPartition_lt_original lam hst hsource₁ htarget₁ hgap₁
  intro hEq
  apply hlt.2
  simpa [hEq] using hle

lemma le_doubleBoxDrop_source_pairTarget_of_prefix_surplus {N : ℕ}
    {mu lam : Nat.Partition N} {s t : ℕ} (hst : s < t)
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
    (hmu_le_lam : mu ≤ lam)
    (hmiddle₂ : ∀ k : ℕ, s < k → k ≤ t → mu.prefixSum k + 2 ≤ lam.prefixSum k)
    (hmiddle₁ :
      ∀ k : ℕ, t < k → k ≤ t + 1 → mu.prefixSum k + 1 ≤ lam.prefixSum k) :
    mu ≤ boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans hst (Nat.lt_succ_self t)) hsource₂ htarget₂ hgap₂ := by
  intro k
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  let hst1 : s < t + 1 := lt_trans hst (Nat.lt_succ_self t)
  change mu.prefixSum k ≤ (boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂).prefixSum k
  rw [prefixSum_boxDropPartition rho hst1 hsource₂ htarget₂ hgap₂]
  by_cases hmid₂ : s < k ∧ k ≤ t + 1
  · rw [if_pos hmid₂]
    by_cases hmid₁ : s < k ∧ k ≤ t
    · rw [show rho.prefixSum k = lam.prefixSum k - 1 by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      have hsurplus := hmiddle₂ k hmid₁.1 hmid₁.2
      omega
    · rw [show rho.prefixSum k = lam.prefixSum k by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      have htk : t < k := by omega
      have hsurplus := hmiddle₁ k htk hmid₂.2
      omega
  · rw [if_neg hmid₂]
    have hmid₁ : ¬(s < k ∧ k ≤ t) := by omega
    rw [show rho.prefixSum k = lam.prefixSum k by
      dsimp [rho]
      exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
    exact hmu_le_lam k

lemma doubleBoxDrop_sourcePair_target_le_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s + 1 < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂ ≤ lam := by
  exact le_trans
    (boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂)
    (boxDropPartition_le_original lam hst hsource₁ htarget₁ hgap₁)

lemma doubleBoxDrop_sourcePair_target_ne_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s + 1 < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂ ≠ lam := by
  have hle :
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂ ≤
        boxDropPartition lam hst hsource₁ htarget₁ hgap₁ :=
    boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂
  have hlt : boxDropPartition lam hst hsource₁ htarget₁ hgap₁ < lam :=
    boxDropPartition_lt_original lam hst hsource₁ htarget₁ hgap₁
  intro hEq
  apply hlt.2
  simpa [hEq] using hle

lemma le_doubleBoxDrop_sourcePair_target_of_prefix_surplus {N : ℕ}
    {mu lam : Nat.Partition N} {s t : ℕ} (hst : s + 1 < t)
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
    (hmu_le_lam : mu ≤ lam)
    (hmiddle₁ :
      ∀ k : ℕ, s < k → k ≤ s + 1 → mu.prefixSum k + 1 ≤ lam.prefixSum k)
    (hmiddle₂ : ∀ k : ℕ, s + 1 < k → k ≤ t →
      mu.prefixSum k + 2 ≤ lam.prefixSum k) :
    mu ≤ boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) hst) hsource₂ htarget₂ hgap₂ := by
  intro k
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  let hslt : s < t := lt_trans (Nat.lt_succ_self s) hst
  change mu.prefixSum k ≤ (boxDropPartition rho hslt hsource₂ htarget₂ hgap₂).prefixSum k
  rw [prefixSum_boxDropPartition rho hslt hsource₂ htarget₂ hgap₂]
  by_cases hmid₂ : s < k ∧ k ≤ t
  · rw [if_pos hmid₂]
    by_cases hmid₁ : s + 1 < k ∧ k ≤ t
    · rw [show rho.prefixSum k = lam.prefixSum k - 1 by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      have hsurplus := hmiddle₂ k hmid₁.1 hmid₁.2
      omega
    · rw [show rho.prefixSum k = lam.prefixSum k by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      have hks1 : k ≤ s + 1 := by omega
      have hsurplus := hmiddle₁ k hmid₂.1 hks1
      omega
  · rw [if_neg hmid₂]
    have hmid₁ : ¬(s + 1 < k ∧ k ≤ t) := by omega
    rw [show rho.prefixSum k = lam.prefixSum k by
      dsimp [rho]
      exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
    exact hmu_le_lam k

lemma doubleBoxDrop_sourcePair_targetPair_le_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s + 1 < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
      hsource₂ htarget₂ hgap₂ ≤ lam := by
  exact le_trans
    (boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
      hsource₂ htarget₂ hgap₂)
    (boxDropPartition_le_original lam hst hsource₁ htarget₁ hgap₁)

lemma doubleBoxDrop_sourcePair_targetPair_ne_original {N : ℕ}
    (lam : Nat.Partition N) {s t : ℕ} (hst : s + 1 < t)
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
        (boxDropPartition lam hst hsource₁ htarget₁ hgap₁).rowLen s) :
    boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
      hsource₂ htarget₂ hgap₂ ≠ lam := by
  have hle :
      boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
        (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
        hsource₂ htarget₂ hgap₂ ≤
        boxDropPartition lam hst hsource₁ htarget₁ hgap₁ :=
    boxDropPartition_le_original (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
      hsource₂ htarget₂ hgap₂
  have hlt : boxDropPartition lam hst hsource₁ htarget₁ hgap₁ < lam :=
    boxDropPartition_lt_original lam hst hsource₁ htarget₁ hgap₁
  intro hEq
  apply hlt.2
  simpa [hEq] using hle

lemma le_doubleBoxDrop_sourcePair_targetPair_of_prefix_surplus {N : ℕ}
    {mu lam : Nat.Partition N} {s t : ℕ} (hst : s + 1 < t)
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
    (hmu_le_lam : mu ≤ lam)
    (hmiddle_left :
      ∀ k : ℕ, s < k → k ≤ s + 1 → mu.prefixSum k + 1 ≤ lam.prefixSum k)
    (hmiddle_two :
      ∀ k : ℕ, s + 1 < k → k ≤ t → mu.prefixSum k + 2 ≤ lam.prefixSum k)
    (hmiddle_right :
      ∀ k : ℕ, t < k → k ≤ t + 1 → mu.prefixSum k + 1 ≤ lam.prefixSum k) :
    mu ≤ boxDropPartition (boxDropPartition lam hst hsource₁ htarget₁ hgap₁)
      (lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t)))
      hsource₂ htarget₂ hgap₂ := by
  intro k
  let rho := boxDropPartition lam hst hsource₁ htarget₁ hgap₁
  let hslt1 : s < t + 1 :=
    lt_trans (Nat.lt_succ_self s) (lt_trans hst (Nat.lt_succ_self t))
  change mu.prefixSum k ≤ (boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂).prefixSum k
  rw [prefixSum_boxDropPartition rho hslt1 hsource₂ htarget₂ hgap₂]
  by_cases hmid₂ : s < k ∧ k ≤ t + 1
  · rw [if_pos hmid₂]
    by_cases hmid₁ : s + 1 < k ∧ k ≤ t
    · rw [show rho.prefixSum k = lam.prefixSum k - 1 by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      have hsurplus := hmiddle_two k hmid₁.1 hmid₁.2
      omega
    · rw [show rho.prefixSum k = lam.prefixSum k by
        dsimp [rho]
        exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
      by_cases hkt : k ≤ s + 1
      · have hsurplus := hmiddle_left k hmid₂.1 hkt
        omega
      · have htk : t < k := by omega
        have hsurplus := hmiddle_right k htk hmid₂.2
        omega
  · rw [if_neg hmid₂]
    have hmid₁ : ¬(s + 1 < k ∧ k ≤ t) := by omega
    rw [show rho.prefixSum k = lam.prefixSum k by
      dsimp [rho]
      exact prefixSum_boxDropPartition_of_not_mid lam hst hsource₁ htarget₁ hgap₁ hmid₁]
    exact hmu_le_lam k

end Nat.Partition

