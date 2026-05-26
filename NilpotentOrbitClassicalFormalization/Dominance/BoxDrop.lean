import NilpotentOrbitClassicalFormalization.Dominance.Basic

/-!
# One-box drops for partitions

This file constructs the one-box Young-diagram move used in the A-type covering
relation and records its row-length and prefix-sum behavior.
-/

open Finset

namespace YoungDiagram

lemma rowLen_eq_of_mem_iff (μ : YoungDiagram) (i m : ℕ)
    (h : ∀ j : ℕ, (i, j) ∈ μ ↔ j < m) : μ.rowLen i = m := by
  apply le_antisymm
  · by_contra hle
    have hlt : m < μ.rowLen i := Nat.lt_of_not_ge hle
    have hm : (i, m) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 hlt
    exact (Nat.lt_irrefl m) ((h m).1 hm)
  · by_contra hle
    have hlt : μ.rowLen i < m := Nat.lt_of_not_ge hle
    have hm : (i, μ.rowLen i) ∈ μ := (h (μ.rowLen i)).2 hlt
    exact (Nat.lt_irrefl (μ.rowLen i)) (YoungDiagram.mem_iff_lt_rowLen.1 hm)

/--
Move the removable corner box in row `s` to the addable position at the end of row `t`.

The hypotheses are exactly the local Young-diagram checks needed by the qmd proof:
row `s` is the bottom of a constant-height block, row `t` is addable, and the target
is at least two columns to the left of the removed source corner.
-/
noncomputable def boxDrop (μ : YoungDiagram) (s t : ℕ) (_hst : s < t)
    (hsource : μ.rowLen (s + 1) < μ.rowLen s)
    (htarget : μ.rowLen t < μ.rowLen (t - 1))
    (hgap : μ.rowLen t + 1 < μ.rowLen s) : YoungDiagram where
  cells := insert (t, μ.rowLen t) (μ.cells.erase (s, μ.rowLen s - 1))
  isLowerSet := by
    rintro x y hle hcell
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    rcases hle with ⟨hc, hd⟩
    simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_diff,
      Set.mem_singleton_iff] at hcell ⊢
    rcases hcell with hab | ⟨hab, hab_ne⟩
    · rcases hab with ⟨rfl, rfl⟩
      by_cases htarget_cell : (c, d) = (t, μ.rowLen t)
      · exact Or.inl htarget_cell
      · refine Or.inr ⟨?_, ?_⟩
        · change (c, d) ∈ μ
          rw [YoungDiagram.mem_iff_lt_rowLen]
          by_cases hct : c = t
          · subst c
            have hdne : d ≠ μ.rowLen t := by
              intro hd_eq
              apply htarget_cell
              ext <;> simp [hd_eq]
            omega
          · have hclt : c < t := lt_of_le_of_ne hc hct
            have hc_le_pred : c ≤ t - 1 := Nat.le_sub_one_of_lt hclt
            exact lt_of_le_of_lt hd <|
              lt_of_lt_of_le htarget <| μ.rowLen_anti c (t - 1) hc_le_pred
        · intro hrem
          rcases hrem with ⟨rfl, _⟩
          have : μ.rowLen s - 1 ≤ μ.rowLen t := by omega
          omega
    · refine Or.inr ⟨?_, ?_⟩
      · change (c, d) ∈ μ
        exact μ.up_left_mem hc hd hab
      · intro hrem
        rcases hrem with ⟨rfl, rfl⟩
        have hb_lt : b < μ.rowLen a := YoungDiagram.mem_iff_lt_rowLen.1 hab
        have hd' : μ.rowLen s - 1 ≤ b := hd
        rcases lt_or_eq_of_le hc with hsc | hcs
        · have hs1a : s + 1 ≤ a := Nat.succ_le_iff.mpr hsc
          have hrow_le : μ.rowLen a ≤ μ.rowLen (s + 1) :=
            μ.rowLen_anti (s + 1) a hs1a
          omega
        · change s = a at hcs
          subst a
          have hb_eq : b = μ.rowLen s - 1 := by omega
          exact hab_ne (by ext <;> simp [hb_eq])

lemma rowLen_boxDrop_source (μ : YoungDiagram) {s t : ℕ} (hst : s < t)
    (hsource : μ.rowLen (s + 1) < μ.rowLen s)
    (htarget : μ.rowLen t < μ.rowLen (t - 1))
    (hgap : μ.rowLen t + 1 < μ.rowLen s) :
    (μ.boxDrop s t hst hsource htarget hgap).rowLen s = μ.rowLen s - 1 := by
  apply rowLen_eq_of_mem_iff
  intro j
  simp only [boxDrop, mem_mk, Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro h
    rcases h with hnew | ⟨hne, hold⟩
    · have : s = t := by simpa using congrArg Prod.fst hnew
      omega
    · have hjlt : j < μ.rowLen s := YoungDiagram.mem_iff_lt_rowLen.1 hold
      have hjne : j ≠ μ.rowLen s - 1 := by
        intro hj
        apply hne
        ext <;> simp [hj]
      omega
  · intro hj
    right
    constructor
    · intro hrem
      have hj_eq : j = μ.rowLen s - 1 := by simpa using congrArg Prod.snd hrem
      omega
    · change (s, j) ∈ μ
      rw [YoungDiagram.mem_iff_lt_rowLen]
      omega

lemma rowLen_boxDrop_target (μ : YoungDiagram) {s t : ℕ} (hst : s < t)
    (hsource : μ.rowLen (s + 1) < μ.rowLen s)
    (htarget : μ.rowLen t < μ.rowLen (t - 1))
    (hgap : μ.rowLen t + 1 < μ.rowLen s) :
    (μ.boxDrop s t hst hsource htarget hgap).rowLen t = μ.rowLen t + 1 := by
  apply rowLen_eq_of_mem_iff
  intro j
  simp only [boxDrop, mem_mk, Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro h
    rcases h with hnew | ⟨_, hold⟩
    · have : j = μ.rowLen t := by simpa using congrArg Prod.snd hnew
      omega
    · have hjlt : j < μ.rowLen t := YoungDiagram.mem_iff_lt_rowLen.1 hold
      omega
  · intro hj
    by_cases hjtop : j = μ.rowLen t
    · left
      ext <;> simp [hjtop]
    · right
      constructor
      · intro hrem
        have hst_eq : t = s := by simpa using congrArg Prod.fst hrem
        omega
      · change (t, j) ∈ μ
        rw [YoungDiagram.mem_iff_lt_rowLen]
        omega

lemma rowLen_boxDrop_of_ne (μ : YoungDiagram) {s t r : ℕ} (hst : s < t)
    (hsource : μ.rowLen (s + 1) < μ.rowLen s)
    (htarget : μ.rowLen t < μ.rowLen (t - 1))
    (hgap : μ.rowLen t + 1 < μ.rowLen s) (hrs : r ≠ s) (hrt : r ≠ t) :
    (μ.boxDrop s t hst hsource htarget hgap).rowLen r = μ.rowLen r := by
  apply rowLen_eq_of_mem_iff
  intro j
  simp only [boxDrop, mem_mk, Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro h
    rcases h with hnew | ⟨_, hold⟩
    · have : r = t := by simpa using congrArg Prod.fst hnew
      contradiction
    · exact YoungDiagram.mem_iff_lt_rowLen.1 hold
  · intro hj
    right
    constructor
    · intro hrem
      have : r = s := by simpa using congrArg Prod.fst hrem
      contradiction
    · change (r, j) ∈ μ
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hj

@[simp]
lemma card_boxDrop (μ : YoungDiagram) {s t : ℕ} (hst : s < t)
    (hsource : μ.rowLen (s + 1) < μ.rowLen s)
    (htarget : μ.rowLen t < μ.rowLen (t - 1))
    (hgap : μ.rowLen t + 1 < μ.rowLen s) :
    (μ.boxDrop s t hst hsource htarget hgap).card = μ.card := by
  rw [YoungDiagram.card]
  dsimp [boxDrop]
  rw [Finset.card_insert_of_notMem]
  · have hsource_mem : (s, μ.rowLen s - 1) ∈ μ.cells := by
      rw [mem_cells, YoungDiagram.mem_iff_lt_rowLen]
      exact Nat.sub_one_lt_of_lt hsource
    rw [Finset.card_erase_of_mem hsource_mem]
    · change #μ.cells - 1 + 1 = #μ.cells
      have hcard_pos : 0 < #μ.cells := Finset.card_pos.mpr ⟨_, hsource_mem⟩
      omega
  · rw [Finset.mem_erase]
    rintro ⟨_, hmem⟩
    rw [mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hmem
    exact (Nat.lt_irrefl (μ.rowLen t)) hmem

end YoungDiagram

namespace Nat.Partition

/-- The partition obtained from `lam` by moving one Young-diagram corner box downward. -/
noncomputable def boxDropPartition {n : ℕ} (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) : Nat.Partition n :=
  ((YoungDiagram.ofPartition lam).boxDrop s t hst hsource htarget hgap).toPartition (by simp)

lemma rowLen_boxDropPartition {n : ℕ} (lam : Nat.Partition n) {s t r : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) :
    (boxDropPartition lam hst hsource htarget hgap).rowLen r =
      if r = s then lam.rowLen r - 1 else if r = t then lam.rowLen r + 1 else lam.rowLen r := by
  by_cases hrs : r = s
  · subst r
    simp [boxDropPartition, Nat.Partition.rowLen, YoungDiagram.rowLen_boxDrop_source]
  · by_cases hrt : r = t
    · subst r
      simp [boxDropPartition, Nat.Partition.rowLen, YoungDiagram.rowLen_boxDrop_target, hrs]
    · simp [boxDropPartition, Nat.Partition.rowLen, YoungDiagram.rowLen_boxDrop_of_ne, hrs, hrt]

lemma boxDropPartition_le_original {n : ℕ} (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) :
    boxDropPartition lam hst hsource htarget hgap ≤ lam := by
  intro k
  simp only [prefixSum]
  calc
    (∑ x ∈ range k, (boxDropPartition lam hst hsource htarget hgap).rowLen x)
        = ∑ x ∈ range k,
            (if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) := by
          apply Finset.sum_congr rfl
          intro x _
          exact rowLen_boxDropPartition lam hst hsource htarget hgap
    _ ≤ ∑ x ∈ range k, lam.rowLen x := by
      by_cases htmem : t ∈ range k
      · have hsmem : s ∈ range k := by
          rw [mem_range] at htmem ⊢
          exact lt_trans hst htmem
        have htmem_erase : t ∈ (range k).erase s := by
          simp [htmem, ne_of_gt hst]
        rw [← Finset.add_sum_erase (range k)
          (fun x => if x = s then lam.rowLen x - 1
            else if x = t then lam.rowLen x + 1 else lam.rowLen x) hsmem]
        rw [← Finset.add_sum_erase ((range k).erase s)
          (fun x => if x = s then lam.rowLen x - 1
            else if x = t then lam.rowLen x + 1 else lam.rowLen x) htmem_erase]
        rw [← Finset.add_sum_erase (range k) (fun x => lam.rowLen x) hsmem]
        rw [← Finset.add_sum_erase ((range k).erase s) (fun x => lam.rowLen x) htmem_erase]
        have hrest :
            (∑ x ∈ ((range k).erase s).erase t,
              (if x = s then lam.rowLen x - 1
                else if x = t then lam.rowLen x + 1 else lam.rowLen x))
              = ∑ x ∈ ((range k).erase s).erase t, lam.rowLen x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxt : x ≠ t := (Finset.mem_erase.mp hx).1
          have hxerase : x ∈ (range k).erase s := (Finset.mem_erase.mp hx).2
          have hxs : x ≠ s := (Finset.mem_erase.mp hxerase).1
          simp [hxs, hxt]
        rw [hrest]
        simp [ne_of_gt hst]
        omega
      · by_cases hsmem : s ∈ range k
        · rw [← Finset.add_sum_erase (range k)
            (fun x => if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) hsmem]
          rw [← Finset.add_sum_erase (range k) (fun x => lam.rowLen x) hsmem]
          have hrest :
              (∑ x ∈ (range k).erase s,
                (if x = s then lam.rowLen x - 1
                  else if x = t then lam.rowLen x + 1 else lam.rowLen x))
                = ∑ x ∈ (range k).erase s, lam.rowLen x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
            have hxrange : x ∈ range k := (Finset.mem_erase.mp hx).2
            have hxt : x ≠ t := by
              intro hxt
              exact htmem (hxt ▸ hxrange)
            simp [hxs, hxt]
          rw [hrest]
          simp
        · apply le_of_eq
          apply Finset.sum_congr rfl
          intro x hx
          have hxs : x ≠ s := by
            intro hxs
            exact hsmem (hxs ▸ hx)
          have hxt : x ≠ t := by
            intro hxt
            exact htmem (hxt ▸ hx)
          simp [hxs, hxt]

lemma prefixSum_boxDropPartition {n : ℕ} (lam : Nat.Partition n) {s t : ℕ} (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) (k : ℕ) :
    (boxDropPartition lam hst hsource htarget hgap).prefixSum k =
      if s < k ∧ k ≤ t then lam.prefixSum k - 1 else lam.prefixSum k := by
  simp only [prefixSum]
  calc
    (∑ x ∈ range k, (boxDropPartition lam hst hsource htarget hgap).rowLen x)
        = ∑ x ∈ range k,
            (if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) := by
          apply Finset.sum_congr rfl
          intro x _
          exact rowLen_boxDropPartition lam hst hsource htarget hgap
    _ = if s < k ∧ k ≤ t then (∑ x ∈ range k, lam.rowLen x) - 1
        else ∑ x ∈ range k, lam.rowLen x := by
      by_cases hsmem : s ∈ range k
      · have hsk : s < k := by simpa using hsmem
        by_cases htmem : t ∈ range k
        · have htk : t < k := by simpa using htmem
          have htmem_erase : t ∈ (range k).erase s := by
            simp [htmem, ne_of_gt hst]
          rw [← Finset.add_sum_erase (range k)
            (fun x => if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) hsmem]
          rw [← Finset.add_sum_erase ((range k).erase s)
            (fun x => if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) htmem_erase]
          rw [← Finset.add_sum_erase (range k) (fun x => lam.rowLen x) hsmem]
          rw [← Finset.add_sum_erase ((range k).erase s) (fun x => lam.rowLen x)
            htmem_erase]
          have hrest :
              (∑ x ∈ ((range k).erase s).erase t,
                (if x = s then lam.rowLen x - 1
                  else if x = t then lam.rowLen x + 1 else lam.rowLen x))
                = ∑ x ∈ ((range k).erase s).erase t, lam.rowLen x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxt : x ≠ t := (Finset.mem_erase.mp hx).1
            have hxerase : x ∈ (range k).erase s := (Finset.mem_erase.mp hx).2
            have hxs : x ≠ s := (Finset.mem_erase.mp hxerase).1
            simp [hxs, hxt]
          rw [hrest]
          simp [ne_of_gt hst, hsk, Nat.not_le_of_gt htk]
          omega
        · have htlek : k ≤ t := Nat.le_of_not_gt (by simpa [mem_range] using htmem)
          rw [← Finset.add_sum_erase (range k)
            (fun x => if x = s then lam.rowLen x - 1
              else if x = t then lam.rowLen x + 1 else lam.rowLen x) hsmem]
          rw [← Finset.add_sum_erase (range k) (fun x => lam.rowLen x) hsmem]
          have hrest :
              (∑ x ∈ (range k).erase s,
                (if x = s then lam.rowLen x - 1
                  else if x = t then lam.rowLen x + 1 else lam.rowLen x))
                = ∑ x ∈ (range k).erase s, lam.rowLen x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
            have hxrange : x ∈ range k := (Finset.mem_erase.mp hx).2
            have hxt : x ≠ t := by
              intro hxt
              exact htmem (hxt ▸ hxrange)
            simp [hxs, hxt]
          rw [hrest]
          simp [hsk, htlek]
          omega
      · have hks : k ≤ s := Nat.le_of_not_gt (by simpa [mem_range] using hsmem)
        have htmem_false : t ∉ range k := by
          intro htmem
          have htk : t < k := by simpa using htmem
          omega
        have hnone :
            (∑ x ∈ range k,
              (if x = s then lam.rowLen x - 1
                else if x = t then lam.rowLen x + 1 else lam.rowLen x))
              = ∑ x ∈ range k, lam.rowLen x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxs : x ≠ s := by
            intro hxs
            exact hsmem (hxs ▸ hx)
          have hxt : x ≠ t := by
            intro hxt
            exact htmem_false (hxt ▸ hx)
          simp [hxs, hxt]
        rw [hnone]
        simp [hks]

lemma prefixSum_boxDropPartition_of_mid {n : ℕ} (lam : Nat.Partition n) {s t k : ℕ}
    (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) (hmid : s < k ∧ k ≤ t) :
    (boxDropPartition lam hst hsource htarget hgap).prefixSum k =
      lam.prefixSum k - 1 := by
  rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
  exact if_pos hmid

lemma prefixSum_boxDropPartition_of_not_mid {n : ℕ} (lam : Nat.Partition n) {s t k : ℕ}
    (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s) (hmid : ¬(s < k ∧ k ≤ t)) :
    (boxDropPartition lam hst hsource htarget hgap).prefixSum k =
      lam.prefixSum k := by
  rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
  exact if_neg hmid

lemma le_boxDropPartition_of_prefix_surplus {n : ℕ} {mu lam : Nat.Partition n} {s t : ℕ}
    (hst : s < t)
    (hsource : lam.rowLen (s + 1) < lam.rowLen s)
    (htarget : lam.rowLen t < lam.rowLen (t - 1))
    (hgap : lam.rowLen t + 1 < lam.rowLen s)
    (hmu_le_lam : mu ≤ lam)
    (hmiddle : ∀ k : ℕ, s < k → k ≤ t → mu.prefixSum k + 1 ≤ lam.prefixSum k) :
    mu ≤ boxDropPartition lam hst hsource htarget hgap := by
  intro k
  rw [prefixSum_boxDropPartition lam hst hsource htarget hgap]
  by_cases hmid : s < k ∧ k ≤ t
  · rw [if_pos hmid]
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le (hmiddle k hmid.1 hmid.2))
  · rw [if_neg hmid]
    exact hmu_le_lam k

end Nat.Partition
