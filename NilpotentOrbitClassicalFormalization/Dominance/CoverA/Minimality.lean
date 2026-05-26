import NilpotentOrbitClassicalFormalization.Dominance.BoxDrop

/-!
# Minimality of A-type box drops

This file proves that the canonical one-box drops used in the A-type cover
characterization have no strict intermediate partition in dominance order.
-/

open Finset

namespace Nat.Partition

lemma prefixSum_eq_boxDropPartition_or_eq_original_of_between {n : ℕ}
    (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) {nu : Nat.Partition n}
    (hmu_le_nu : boxDropPartition lam hst hsource htarget hgap ≤ nu)
    (hnu_le_lam : nu ≤ lam) (k : ℕ) :
    nu.prefixSum k = (boxDropPartition lam hst hsource htarget hgap).prefixSum k ∨
      nu.prefixSum k = lam.prefixSum k := by
  have hnu_le := hnu_le_lam k
  have hmu_le := hmu_le_nu k
  rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_le ⊢
  by_cases hmid : s < k ∧ k ≤ t
  · rw [if_pos hmid] at hmu_le ⊢
    by_cases htop : nu.prefixSum k = lam.prefixSum k
    · exact Or.inr htop
    · left
      omega
  · rw [if_neg hmid] at hmu_le ⊢
    exact Or.inl (le_antisymm hnu_le hmu_le)

lemma eq_boxDropPartition_or_eq_original_of_between_adjacent {n : ℕ}
    (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hadj : t = s + 1) {nu : Nat.Partition n}
    (hmu_le_nu : boxDropPartition lam hst hsource htarget hgap ≤ nu)
    (hnu_le_lam : nu ≤ lam) :
    nu = boxDropPartition lam hst hsource htarget hgap ∨ nu = lam := by
  classical
  by_cases ht : nu.prefixSum t = lam.prefixSum t
  · right
    apply ext_of_rowLen_eq
    apply rowLen_eq_of_prefixSum_eq
    intro k
    have hnu_le := hnu_le_lam k
    have hmu_le := hmu_le_nu k
    rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_le
    by_cases hk : k = t
    · simpa [hk] using ht
    · have hmid_false : ¬(s < k ∧ k ≤ t) := by
        intro hmid
        have : k = t := by omega
        exact hk this
      rw [if_neg hmid_false] at hmu_le
      exact le_antisymm hnu_le hmu_le
  · left
    apply ext_of_rowLen_eq
    apply rowLen_eq_of_prefixSum_eq
    intro k
    have hnu_le := hnu_le_lam k
    have hmu_le := hmu_le_nu k
    rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
    by_cases hmid : s < k ∧ k ≤ t
    · have hk : k = t := by omega
      subst k
      rw [if_pos (by omega : s < t ∧ t ≤ t)]
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_le
      rw [if_pos (by omega : s < t ∧ t ≤ t)] at hmu_le
      omega
    · rw [if_neg hmid]
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_le
      rw [if_neg hmid] at hmu_le
      exact le_antisymm hnu_le hmu_le

lemma rowLen_eq_source_sub_one_of_exact {n : ℕ} (lam : Nat.Partition n) {s t r : ℕ}
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hexact : lam.rowLen t + 2 = lam.rowLen s)
    (hsr : s < r) (hrt : r < t) :
    lam.rowLen r + 1 = lam.rowLen s := by
  have hs1r : s + 1 ≤ r := Nat.succ_le_iff.mpr hsr
  have hupper : lam.rowLen r ≤ lam.rowLen (s + 1) :=
    (YoungDiagram.ofPartition lam).rowLen_anti (s + 1) r hs1r
  have hrpred : r ≤ t - 1 := Nat.le_sub_one_of_lt hrt
  have hlower : lam.rowLen (t - 1) ≤ lam.rowLen r :=
    (YoungDiagram.ofPartition lam).rowLen_anti r (t - 1) hrpred
  omega

lemma not_original_to_boxDrop_prefix_transition_of_exact {n : ℕ}
    (lam : Nat.Partition n) {s t r : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hexact : lam.rowLen t + 2 = lam.rowLen s) {nu : Nat.Partition n}
    (hmu_le_nu : boxDropPartition lam hst hsource htarget hgap ≤ nu)
    (hnu_le_lam : nu ≤ lam) (hsr : s < r) (hrt : r < t)
    (hr : nu.prefixSum r = lam.prefixSum r)
    (hrsucc :
      nu.prefixSum (r + 1) =
        (boxDropPartition lam hst hsource htarget hgap).prefixSum (r + 1)) :
    False := by
  have hanti : nu.rowLen (r + 1) ≤ nu.rowLen r :=
    (YoungDiagram.ofPartition nu).rowLen_anti r (r + 1) (Nat.le_succ r)
  have hrowr : nu.rowLen r = lam.rowLen r - 1 := by
    rw [rowLen_eq_prefixSum_succ_sub nu r, hrsucc, hr]
    rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
    have hmid : s < r + 1 ∧ r + 1 ≤ t := by omega
    rw [if_pos hmid]
    have hlamrow := rowLen_eq_prefixSum_succ_sub lam r
    omega
  have hrowr_lam : lam.rowLen r + 1 = lam.rowLen s :=
    rowLen_eq_source_sub_one_of_exact lam hsource htarget hexact hsr hrt
  have hrowrsucc_lower : lam.rowLen r ≤ nu.rowLen (r + 1) := by
    rw [rowLen_eq_prefixSum_succ_sub nu (r + 1)]
    by_cases hrsucc_t : r + 1 = t
    · have hnu_next_le := hnu_le_lam (r + 2)
      have hmu_next := hmu_le_nu (r + 2)
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_next
      have hnot_mid : ¬(s < r + 2 ∧ r + 2 ≤ t) := by omega
      rw [if_neg hnot_mid] at hmu_next
      have hnu_next : nu.prefixSum (r + 2) = lam.prefixSum (r + 2) :=
        le_antisymm hnu_next_le hmu_next
      rw [hnu_next, hrsucc]
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
      have hmid : s < r + 1 ∧ r + 1 ≤ t := by omega
      rw [if_pos hmid]
      have htarget_row : lam.rowLen (r + 1) + 2 = lam.rowLen s := by
        rw [hrsucc_t]
        exact hexact
      have hlamrow := rowLen_eq_prefixSum_succ_sub lam (r + 1)
      rw [show r + 1 + 1 = r + 2 by omega] at hlamrow
      have hpref_pos : 0 < lam.prefixSum (r + 1) :=
        prefixSum_pos_of_rowLen_pos lam (by omega : s < r + 1) (by omega)
      have hpred :
          lam.prefixSum (r + 1) - 1 + 1 = lam.prefixSum (r + 1) :=
        Nat.sub_one_add_one_eq_of_pos hpref_pos
      have hpref2 :
          lam.prefixSum (r + 2) = lam.prefixSum (r + 1) + lam.rowLen (r + 1) := by
        rw [show r + 2 = (r + 1) + 1 by omega, prefixSum_succ]
      have hcalc :
          lam.prefixSum (r + 2) - (lam.prefixSum (r + 1) - 1) =
            lam.rowLen (r + 1) + 1 := by
        rw [hpref2, ← hpred]
        omega
      rw [hcalc]
      omega
    · have hrt' : r + 1 < t := lt_of_le_of_ne (Nat.succ_le_iff.mpr hrt) hrsucc_t
      have hmu_next := hmu_le_nu (r + 2)
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_next
      have hmid_next : s < r + 2 ∧ r + 2 ≤ t := by omega
      rw [if_pos hmid_next] at hmu_next
      rw [hrsucc]
      rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
      have hmid : s < r + 1 ∧ r + 1 ≤ t := by omega
      rw [if_pos hmid]
      have hrowrsucc_lam : lam.rowLen (r + 1) + 1 = lam.rowLen s :=
        rowLen_eq_source_sub_one_of_exact lam hsource htarget hexact (by omega) hrt'
      have hlamrow := rowLen_eq_prefixSum_succ_sub lam (r + 1)
      rw [show r + 1 + 1 = r + 2 by omega] at hlamrow
      have hpref_pos : 0 < lam.prefixSum (r + 1) :=
        prefixSum_pos_of_rowLen_pos lam (by omega : s < r + 1) (by omega)
      have hpred :
          lam.prefixSum (r + 1) - 1 + 1 = lam.prefixSum (r + 1) :=
        Nat.sub_one_add_one_eq_of_pos hpref_pos
      have hpref2 :
          lam.prefixSum (r + 2) = lam.prefixSum (r + 1) + lam.rowLen (r + 1) := by
        rw [show r + 2 = (r + 1) + 1 by omega, prefixSum_succ]
      rw [hpref2, ← hpred] at hmu_next
      have hcalc_le :
          lam.rowLen (r + 1) ≤
            nu.prefixSum (r + 2) - (lam.prefixSum (r + 1) - 1) := by
        omega
      have hrow_lam_le : lam.rowLen r ≤ lam.rowLen (r + 1) := by omega
      exact le_trans hrow_lam_le hcalc_le
  omega

lemma not_boxDrop_to_original_prefix_transition_of_exact {n : ℕ}
    (lam : Nat.Partition n) {s t r : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hexact : lam.rowLen t + 2 = lam.rowLen s) {nu : Nat.Partition n}
    (hmu_le_nu : boxDropPartition lam hst hsource htarget hgap ≤ nu)
    (hnu_le_lam : nu ≤ lam) (hsr : s < r) (hrt : r < t)
    (hr :
      nu.prefixSum r =
        (boxDropPartition lam hst hsource htarget hgap).prefixSum r)
    (hrsucc : nu.prefixSum (r + 1) = lam.prefixSum (r + 1)) :
    False := by
  have hanti : nu.rowLen r ≤ nu.rowLen (r - 1) := by
    have hrpos : 0 < r := by omega
    have hpred_lt : r - 1 < r := Nat.sub_one_lt_of_lt hrpos
    exact (YoungDiagram.ofPartition nu).rowLen_anti (r - 1) r hpred_lt.le
  have hrowr : nu.rowLen r = lam.rowLen s := by
    rw [rowLen_eq_prefixSum_succ_sub nu r, hrsucc, hr]
    rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
    have hmid : s < r ∧ r ≤ t := by omega
    rw [if_pos hmid]
    have hrowr_lam : lam.rowLen r + 1 = lam.rowLen s :=
      rowLen_eq_source_sub_one_of_exact lam hsource htarget hexact hsr hrt
    have hpref_pos : 0 < lam.prefixSum r :=
      prefixSum_pos_of_rowLen_pos lam hsr (by omega)
    have hpred :
        lam.prefixSum r - 1 + 1 = lam.prefixSum r :=
      Nat.sub_one_add_one_eq_of_pos hpref_pos
    have hpref_succ : lam.prefixSum (r + 1) = lam.prefixSum r + lam.rowLen r := by
      rw [prefixSum_succ]
    rw [hpref_succ, ← hpred]
    omega
  have hrowpred_upper : nu.rowLen (r - 1) < lam.rowLen s := by
    by_cases hrsucc : r = s + 1
    · have hs_prefix : nu.prefixSum s = lam.prefixSum s := by
        have hnu_le := hnu_le_lam s
        have hmu_le := hmu_le_nu s
        rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hmu_le
        have hnot_mid : ¬(s < s ∧ s ≤ t) := by omega
        rw [if_neg hnot_mid] at hmu_le
        exact le_antisymm hnu_le hmu_le
      subst r
      have hrows : nu.rowLen s = lam.rowLen s - 1 := by
        rw [rowLen_eq_prefixSum_succ_sub nu s, hs_prefix]
        rw [hr]
        rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
        have hmid : s < s + 1 ∧ s + 1 ≤ t := by omega
        rw [if_pos hmid]
        have hlamrow := rowLen_eq_prefixSum_succ_sub lam s
        omega
      rw [show s + 1 - 1 = s by omega]
      omega
    · have hsrpred : s < r - 1 := by omega
      have hrpredt : r - 1 < t := by omega
      rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
          hsource htarget hgap hmu_le_nu hnu_le_lam (r - 1) with hpred_box | hpred_lam
      · have hrowpred : nu.rowLen (r - 1) = lam.rowLen (r - 1) := by
          rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hpred_box
          have hmid_pred : s < r - 1 ∧ r - 1 ≤ t := by omega
          rw [if_pos hmid_pred] at hpred_box
          rw [rowLen_eq_prefixSum_succ_sub nu (r - 1), hpred_box]
          have hpredsucc : r - 1 + 1 = r := by omega
          rw [hpredsucc, hr]
          rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
          have hmid_r : s < r ∧ r ≤ t := by omega
          rw [if_pos hmid_r]
          have hlamrow := rowLen_eq_prefixSum_succ_sub lam (r - 1)
          rw [hpredsucc] at hlamrow
          have hpref_pos : 0 < lam.prefixSum (r - 1) :=
            prefixSum_pos_of_rowLen_pos lam hsrpred (by omega)
          have hpred_add :
              lam.prefixSum (r - 1) - 1 + 1 = lam.prefixSum (r - 1) :=
            Nat.sub_one_add_one_eq_of_pos hpref_pos
          omega
        have hrowpred_lam : lam.rowLen (r - 1) + 1 = lam.rowLen s :=
          rowLen_eq_source_sub_one_of_exact lam hsource htarget hexact hsrpred hrpredt
        omega
      · have hrowpred : nu.rowLen (r - 1) = lam.rowLen (r - 1) - 1 := by
          rw [rowLen_eq_prefixSum_succ_sub nu (r - 1), hpred_lam]
          have hpredsucc : r - 1 + 1 = r := by omega
          rw [hpredsucc, hr]
          rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
          have hmid_r : s < r ∧ r ≤ t := by omega
          rw [if_pos hmid_r]
          have hlamrow := rowLen_eq_prefixSum_succ_sub lam (r - 1)
          rw [hpredsucc] at hlamrow
          omega
        have hrowpred_lam : lam.rowLen (r - 1) + 1 = lam.rowLen s :=
          rowLen_eq_source_sub_one_of_exact lam hsource htarget hexact hsrpred hrpredt
        omega
  omega

lemma eq_boxDropPartition_or_eq_original_of_between_exact {n : ℕ}
    (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hexact : lam.rowLen t + 2 = lam.rowLen s) {nu : Nat.Partition n}
    (hmu_le_nu : boxDropPartition lam hst hsource htarget hgap ≤ nu)
    (hnu_le_lam : nu ≤ lam) :
    nu = boxDropPartition lam hst hsource htarget hgap ∨ nu = lam := by
  classical
  by_cases hstart : nu.prefixSum (s + 1) = lam.prefixSum (s + 1)
  · right
    apply ext_of_rowLen_eq
    apply rowLen_eq_of_prefixSum_eq
    intro k
    rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
        hsource htarget hgap hmu_le_nu hnu_le_lam k with hk_box | hk_lam
    · rw [prefixSum_boxDropPartition lam hst hsource htarget hgap] at hk_box
      by_cases hmid : s < k ∧ k ≤ t
      · let P : ℕ → Prop := fun q =>
          s < q ∧ q ≤ t ∧
            nu.prefixSum q =
              (boxDropPartition lam hst hsource htarget hgap).prefixSum q
        rw [if_pos hmid] at hk_box
        have hPk : P k := by
          dsimp [P]
          rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
          rw [if_pos hmid]
          exact ⟨hmid.1, hmid.2, hk_box⟩
        let q := Nat.find ⟨k, hPk⟩
        have hq : P q := Nat.find_spec ⟨k, hPk⟩
        have hq_ne_start : q ≠ s + 1 := by
          intro hqstart
          have hq_box := hq.2.2
          rw [hqstart] at hq_box
          rw [hstart] at hq_box
          have hmid_start : s < s + 1 ∧ s + 1 ≤ t := by omega
          rw [prefixSum_boxDropPartition_of_mid lam hst hsource htarget hgap hmid_start]
            at hq_box
          rw [prefixSum_succ] at hq_box
          omega
        have hstart_le_q : s + 1 ≤ q := Nat.succ_le_iff.mpr hq.1
        have hstart_lt_q : s + 1 < q := lt_of_le_of_ne hstart_le_q hq_ne_start.symm
        have hqpred_mid : s < q - 1 ∧ q - 1 < t := by omega
        have hqpred_notP : ¬P (q - 1) := by
          intro hPpred
          exact Nat.find_min ⟨k, hPk⟩ (by omega : q - 1 < q) hPpred
        have hqpred_lam : nu.prefixSum (q - 1) = lam.prefixSum (q - 1) := by
          rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
              hsource htarget hgap hmu_le_nu hnu_le_lam (q - 1) with hbox | hlam
          · exfalso
            apply hqpred_notP
            exact ⟨hqpred_mid.1, le_of_lt hqpred_mid.2, hbox⟩
          · exact hlam
        exact False.elim <|
          not_original_to_boxDrop_prefix_transition_of_exact lam hst hsource htarget hgap
            hexact hmu_le_nu hnu_le_lam hqpred_mid.1 hqpred_mid.2 hqpred_lam
            (by simpa [show q - 1 + 1 = q by omega] using hq.2.2)
      · rw [if_neg hmid] at hk_box
        exact hk_box
    · exact hk_lam
  · left
    have hstart_box :
        nu.prefixSum (s + 1) =
          (boxDropPartition lam hst hsource htarget hgap).prefixSum (s + 1) := by
      rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
          hsource htarget hgap hmu_le_nu hnu_le_lam (s + 1) with hbox | hlam
      · exact hbox
      · exact False.elim (hstart hlam)
    apply ext_of_rowLen_eq
    apply rowLen_eq_of_prefixSum_eq
    intro k
    rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
        hsource htarget hgap hmu_le_nu hnu_le_lam k with hk_box | hk_lam
    · exact hk_box
    · by_cases hmid : s < k ∧ k ≤ t
      · let P : ℕ → Prop := fun q =>
          s < q ∧ q ≤ t ∧ nu.prefixSum q = lam.prefixSum q
        have hPk : P k := ⟨hmid.1, hmid.2, hk_lam⟩
        let q := Nat.find ⟨k, hPk⟩
        have hq : P q := Nat.find_spec ⟨k, hPk⟩
        have hq_ne_start : q ≠ s + 1 := by
          intro hqstart
          have hq_lam := hq.2.2
          rw [hqstart] at hq_lam
          exact hstart (by simpa using hq_lam)
        have hstart_le_q : s + 1 ≤ q := Nat.succ_le_iff.mpr hq.1
        have hstart_lt_q : s + 1 < q := lt_of_le_of_ne hstart_le_q hq_ne_start.symm
        have hqpred_mid : s < q - 1 ∧ q - 1 < t := by omega
        have hqpred_notP : ¬P (q - 1) := by
          intro hPpred
          exact Nat.find_min ⟨k, hPk⟩ (by omega : q - 1 < q) hPpred
        have hqpred_box :
            nu.prefixSum (q - 1) =
              (boxDropPartition lam hst hsource htarget hgap).prefixSum (q - 1) := by
          rcases prefixSum_eq_boxDropPartition_or_eq_original_of_between lam hst
              hsource htarget hgap hmu_le_nu hnu_le_lam (q - 1) with hbox | hlam
          · exact hbox
          · exfalso
            apply hqpred_notP
            exact ⟨hqpred_mid.1, le_of_lt hqpred_mid.2, hlam⟩
        exact False.elim <|
          not_boxDrop_to_original_prefix_transition_of_exact lam hst hsource htarget hgap
            hexact hmu_le_nu hnu_le_lam hqpred_mid.1 hqpred_mid.2 hqpred_box
            (by simpa [show q - 1 + 1 = q by omega] using hq.2.2)
      · rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
        rw [if_neg hmid]
        exact hk_lam


end Nat.Partition
