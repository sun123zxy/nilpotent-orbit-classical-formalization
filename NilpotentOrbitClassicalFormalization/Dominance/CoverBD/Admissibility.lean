import NilpotentOrbitClassicalFormalization.Dominance.CoverBD.Surplus

/-!
# B/D-type move admissibility

This file records that each B/D move preserves B/D admissibility.
-/

namespace Nat.Partition

lemma isBDPartition_of_isBDMove₁ {N : ℕ} {lam mu : Nat.Partition N}
    (hlam : IsBDPartition lam) (h : IsBDMove₁ lam mu) :
    IsBDPartition mu := by
  intro m hm_even
  by_cases hmzero : m = 0
  · rw [hmzero, parts_count_zero]
    exact ⟨0, rfl⟩
  rw [parts_count_eq_rowLens_count]
  rcases h with
    ⟨s, t, hst, hs_odd, ht_odd, hexact, hs, ht, hrest⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hKmu : (YoungDiagram.ofPartition mu).colLen 0 ≤ K := le_max_left _ _
  have hKlam : (YoungDiagram.ofPartition lam).colLen 0 ≤ K := le_max_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hcount_mu := rowLens_count_eq_card_filter_range mu hKmu hmpos
  have hcount_lam := rowLens_count_eq_card_filter_range lam hKlam hmpos
  rw [hcount_mu]
  have heven_lam : Even ((Finset.range K).filter fun r => lam.rowLen r = m).card := by
    rw [← hcount_lam]
    exact rowLens_count_even_of_isBDPartition hlam hm_even
  by_cases hm : m = lam.rowLen t + 1
  · let base := (Finset.range K).filter fun r => lam.rowLen r = m
    have hsrow : mu.rowLen s = m := by linarith
    have htrow : mu.rowLen t = m := by linarith
    have hsK : s ∈ Finset.range K := by
      rw [Finset.mem_range]
      have hscol : s < (YoungDiagram.ofPartition mu).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < mu.rowLen s
        rw [hsrow]
        exact hmpos
      exact lt_of_lt_of_le hscol hKmu
    have htK : t ∈ Finset.range K := by
      rw [Finset.mem_range]
      have htcol : t < (YoungDiagram.ofPartition mu).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < mu.rowLen t
        rw [htrow]
        exact hmpos
      exact lt_of_lt_of_le htcol hKmu
    have hs_not_base : s ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      linarith
    have ht_not_base : t ∉ base := by
      simp [base, hm]
    have hts : t ≠ s := ne_of_gt hst
    have hst_ne : s ≠ t := ne_of_lt hst
    have hs_not_insert : s ∉ insert t base := by
      simp [hs_not_base, hst_ne]
    have hfilter :
        ((Finset.range K).filter fun r => mu.rowLen r = m) =
          insert s (insert t base) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro ⟨hrK, hr⟩
        by_cases hrs : r = s
        · exact Or.inl hrs
        · by_cases hrt : r = t
          · exact Or.inr (Or.inl hrt)
          · have hrlam := hrest r hrs hrt
            exact Or.inr (Or.inr (by
              exact Finset.mem_filter.mpr ⟨hrK, by linarith⟩))
      · rintro (rfl | rfl | hrbase)
        · exact ⟨hsK, hsrow⟩
        · exact ⟨htK, htrow⟩
        · change r ∈ (Finset.range K).filter (fun r => lam.rowLen r = m) at hrbase
          rcases Finset.mem_filter.mp hrbase with ⟨hrK, hrlam⟩
          by_cases hrs : r = s
          · subst r
            linarith
          · by_cases hrt : r = t
            · subst r
              linarith
            · have hrlam' := hrest r hrs hrt
              exact ⟨hrK, by linarith⟩
    rw [hfilter]
    rw [Finset.card_insert_of_notMem hs_not_insert]
    rw [Finset.card_insert_of_notMem ht_not_base]
    · rcases heven_lam with ⟨c, hc⟩
      refine ⟨c + 1, ?_⟩
      dsimp [base] at hc ⊢
      omega
  · have hfilter :
        ((Finset.range K).filter fun r => mu.rowLen r = m) =
          ((Finset.range K).filter fun r => lam.rowLen r = m) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          exact hm (by linarith)
        · by_cases hrt : r = t
          · subst r
            exfalso
            exact hm (by linarith)
          · have hrlam := hrest r hrs hrt
            linarith
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases hs_odd with ⟨b, hb⟩
          omega
        · by_cases hrt : r = t
          · subst r
            exfalso
            rcases hm_even with ⟨a, ha⟩
            rcases ht_odd with ⟨b, hb⟩
            omega
          · have hrlam := hrest r hrs hrt
            linarith
    rw [hfilter]
    exact heven_lam

lemma isBDPartition_of_isBDMove₂ {N : ℕ} {lam mu : Nat.Partition N}
    (hlam : IsBDPartition lam) (h : IsBDMove₂ lam mu) :
    IsBDPartition mu := by
  intro m hm_even
  by_cases hmzero : m = 0
  · rw [hmzero, parts_count_zero]
    exact ⟨0, rfl⟩
  rw [parts_count_eq_rowLens_count]
  rcases h with
    ⟨s, t, _hst, hs_odd, ht_odd, _hgap, hs, ht, hrest⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hKmu : (YoungDiagram.ofPartition mu).colLen 0 ≤ K := le_max_left _ _
  have hKlam : (YoungDiagram.ofPartition lam).colLen 0 ≤ K := le_max_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hcount_mu := rowLens_count_eq_card_filter_range mu hKmu hmpos
  have hcount_lam := rowLens_count_eq_card_filter_range lam hKlam hmpos
  rw [hcount_mu]
  have heven_lam : Even ((Finset.range K).filter fun r => lam.rowLen r = m).card := by
    rw [← hcount_lam]
    exact rowLens_count_even_of_isBDPartition hlam hm_even
  have hfilter :
      ((Finset.range K).filter fun r => mu.rowLen r = m) =
        ((Finset.range K).filter fun r => lam.rowLen r = m) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hrK, hr⟩
      refine ⟨hrK, ?_⟩
      by_cases hrs : r = s
      · subst r
        exfalso
        rcases hm_even with ⟨a, ha⟩
        rcases hs_odd with ⟨b, hb⟩
        omega
      · by_cases hrt : r = t
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases ht_odd with ⟨b, hb⟩
          omega
        · have hrlam := hrest r hrs hrt
          linarith
    · rintro ⟨hrK, hr⟩
      refine ⟨hrK, ?_⟩
      by_cases hrs : r = s
      · subst r
        exfalso
        rcases hm_even with ⟨a, ha⟩
        rcases hs_odd with ⟨b, hb⟩
        omega
      · by_cases hrt : r = t
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases ht_odd with ⟨b, hb⟩
          omega
        · have hrlam := hrest r hrs hrt
          linarith
  rw [hfilter]
  exact heven_lam

lemma isBDPartition_of_isBDMove₃ {N : ℕ} {lam mu : Nat.Partition N}
    (hlam : IsBDPartition lam) (h : IsBDMove₃ lam mu) :
    IsBDPartition mu := by
  intro m hm_even
  by_cases hmzero : m = 0
  · rw [hmzero, parts_count_zero]
    exact ⟨0, rfl⟩
  rw [parts_count_eq_rowLens_count]
  rcases h with
    ⟨s, t, hst, hs_odd, ht_even, ht_pair, _hgap, hs, ht, ht1, hrest⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hKmu : (YoungDiagram.ofPartition mu).colLen 0 ≤ K := le_max_left _ _
  have hKlam : (YoungDiagram.ofPartition lam).colLen 0 ≤ K := le_max_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hcount_mu := rowLens_count_eq_card_filter_range mu hKmu hmpos
  have hcount_lam := rowLens_count_eq_card_filter_range lam hKlam hmpos
  rw [hcount_mu]
  have heven_lam : Even ((Finset.range K).filter fun r => lam.rowLen r = m).card := by
    rw [← hcount_lam]
    exact rowLens_count_even_of_isBDPartition hlam hm_even
  by_cases hm : m = lam.rowLen t
  · let base := (Finset.range K).filter fun r => mu.rowLen r = m
    have htK : t ∈ Finset.range K := by
      rw [Finset.mem_range]
      have htcol : t < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen t
        rw [← hm]
        exact hmpos
      exact lt_of_lt_of_le htcol hKlam
    have ht1K : t + 1 ∈ Finset.range K := by
      rw [Finset.mem_range]
      have ht1col : t + 1 < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen (t + 1)
        rw [← ht_pair, ← hm]
        exact hmpos
      exact lt_of_lt_of_le ht1col hKlam
    have ht_not_base : t ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have ht1_not_base : t + 1 ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have htt1 : t ≠ t + 1 := by linarith
    have hfilter_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m) =
          insert t (insert (t + 1) base) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro ⟨hrK, hr⟩
        by_cases hrt : r = t
        · exact Or.inl hrt
        · by_cases hrt1 : r = t + 1
          · exact Or.inr (Or.inl hrt1)
          · by_cases hrs : r = s
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases hs_odd with ⟨b, hb⟩
              omega
            · have hrmu := hrest r hrs hrt hrt1
              exact Or.inr (Or.inr (by
                exact Finset.mem_filter.mpr ⟨hrK, by linarith⟩))
      · rintro (rfl | rfl | hrbase)
        · exact ⟨htK, hm.symm⟩
        · exact ⟨ht1K, by linarith⟩
        · change r ∈ (Finset.range K).filter (fun r => mu.rowLen r = m) at hrbase
          rcases Finset.mem_filter.mp hrbase with ⟨hrK, hrmu⟩
          by_cases hrs : r = s
          · subst r
            exfalso
            rcases hm_even with ⟨a, ha⟩
            rcases hs_odd with ⟨b, hb⟩
            omega
          · by_cases hrt : r = t
            · subst r
              omega
            · by_cases hrt1 : r = t + 1
              · subst r
                omega
              · have hrlam := hrest r hrs hrt hrt1
                exact ⟨hrK, by linarith⟩
    have hcard_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m).card =
          base.card + 2 := by
      rw [hfilter_lam]
      have ht_not_insert : t ∉ insert (t + 1) base := by
        simp [ht_not_base]
      rw [Finset.card_insert_of_notMem ht_not_insert]
      rw [Finset.card_insert_of_notMem ht1_not_base]
    have heven_base : Even base.card := by
      rw [hcard_lam] at heven_lam
      rcases heven_lam with ⟨c, hc⟩
      refine ⟨c - 1, ?_⟩
      dsimp [base] at hc ⊢
      omega
    exact heven_base
  · have hfilter :
        ((Finset.range K).filter fun r => mu.rowLen r = m) =
          ((Finset.range K).filter fun r => lam.rowLen r = m) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases hs_odd with ⟨b, hb⟩
          omega
        · by_cases hrt : r = t
          · subst r
            exfalso
            rcases hm_even with ⟨a, ha⟩
            rcases ht_even with ⟨b, hb⟩
            omega
          · by_cases hrt1 : r = t + 1
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases ht_even with ⟨b, hb⟩
              omega
            · have hrlam := hrest r hrs hrt hrt1
              linarith
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases hs_odd with ⟨b, hb⟩
          omega
        · by_cases hrt : r = t
          · subst r
            exfalso
            exact hm hr.symm
          · by_cases hrt1 : r = t + 1
            · subst r
              exfalso
              exact hm (by linarith)
            · have hrlam := hrest r hrs hrt hrt1
              linarith
    rw [hfilter]
    exact heven_lam

lemma isBDPartition_of_isBDMove₄ {N : ℕ} {lam mu : Nat.Partition N}
    (hlam : IsBDPartition lam) (h : IsBDMove₄ lam mu) :
    IsBDPartition mu := by
  intro m hm_even
  by_cases hmzero : m = 0
  · rw [hmzero, parts_count_zero]
    exact ⟨0, rfl⟩
  rw [parts_count_eq_rowLens_count]
  rcases h with
    ⟨s, t, hst, hs_even, hs_pair, ht_odd, _hgap, hs, hs1, ht, hrest⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hKmu : (YoungDiagram.ofPartition mu).colLen 0 ≤ K := le_max_left _ _
  have hKlam : (YoungDiagram.ofPartition lam).colLen 0 ≤ K := le_max_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hcount_mu := rowLens_count_eq_card_filter_range mu hKmu hmpos
  have hcount_lam := rowLens_count_eq_card_filter_range lam hKlam hmpos
  rw [hcount_mu]
  have heven_lam : Even ((Finset.range K).filter fun r => lam.rowLen r = m).card := by
    rw [← hcount_lam]
    exact rowLens_count_even_of_isBDPartition hlam hm_even
  by_cases hm : m = lam.rowLen s
  · let base := (Finset.range K).filter fun r => mu.rowLen r = m
    have hsK : s ∈ Finset.range K := by
      rw [Finset.mem_range]
      have hscol : s < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen s
        rw [← hm]
        exact hmpos
      exact lt_of_lt_of_le hscol hKlam
    have hs1K : s + 1 ∈ Finset.range K := by
      rw [Finset.mem_range]
      have hs1col : s + 1 < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen (s + 1)
        rw [← hs_pair, ← hm]
        exact hmpos
      exact lt_of_lt_of_le hs1col hKlam
    have hs_not_base : s ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have hs1_not_base : s + 1 ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have hss1 : s ≠ s + 1 := by linarith
    have hfilter_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m) =
          insert s (insert (s + 1) base) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro ⟨hrK, hr⟩
        by_cases hrs : r = s
        · exact Or.inl hrs
        · by_cases hrs1 : r = s + 1
          · exact Or.inr (Or.inl hrs1)
          · by_cases hrt : r = t
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases ht_odd with ⟨b, hb⟩
              omega
            · have hrmu := hrest r hrs hrs1 hrt
              exact Or.inr (Or.inr (by
                exact Finset.mem_filter.mpr ⟨hrK, by linarith⟩))
      · rintro (rfl | rfl | hrbase)
        · exact ⟨hsK, hm.symm⟩
        · exact ⟨hs1K, by linarith⟩
        · change r ∈ (Finset.range K).filter (fun r => mu.rowLen r = m) at hrbase
          rcases Finset.mem_filter.mp hrbase with ⟨hrK, hrmu⟩
          by_cases hrs : r = s
          · subst r
            omega
          · by_cases hrs1 : r = s + 1
            · subst r
              omega
            · by_cases hrt : r = t
              · subst r
                exfalso
                rcases hm_even with ⟨a, ha⟩
                rcases ht_odd with ⟨b, hb⟩
                omega
              · have hrlam := hrest r hrs hrs1 hrt
                exact ⟨hrK, by linarith⟩
    have hcard_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m).card =
          base.card + 2 := by
      rw [hfilter_lam]
      have hs_not_insert : s ∉ insert (s + 1) base := by
        simp [hs_not_base]
      rw [Finset.card_insert_of_notMem hs_not_insert]
      rw [Finset.card_insert_of_notMem hs1_not_base]
    have heven_base : Even base.card := by
      rw [hcard_lam] at heven_lam
      rcases heven_lam with ⟨c, hc⟩
      refine ⟨c - 1, ?_⟩
      dsimp [base] at hc ⊢
      omega
    exact heven_base
  · have hfilter :
        ((Finset.range K).filter fun r => mu.rowLen r = m) =
          ((Finset.range K).filter fun r => lam.rowLen r = m) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          rcases hm_even with ⟨a, ha⟩
          rcases hs_even with ⟨b, hb⟩
          omega
        · by_cases hrs1 : r = s + 1
          · subst r
            exfalso
            rcases hm_even with ⟨a, ha⟩
            rcases hs_even with ⟨b, hb⟩
            omega
          · by_cases hrt : r = t
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases ht_odd with ⟨b, hb⟩
              omega
            · have hrlam := hrest r hrs hrs1 hrt
              linarith
      · rintro ⟨hrK, hr⟩
        refine ⟨hrK, ?_⟩
        by_cases hrs : r = s
        · subst r
          exfalso
          exact hm hr.symm
        · by_cases hrs1 : r = s + 1
          · subst r
            exfalso
            exact hm (by linarith)
          · by_cases hrt : r = t
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases ht_odd with ⟨b, hb⟩
              omega
            · have hrlam := hrest r hrs hrs1 hrt
              linarith
    rw [hfilter]
    exact heven_lam

lemma isBDPartition_of_isBDMove₅ {N : ℕ} {lam mu : Nat.Partition N}
    (hlam : IsBDPartition lam) (h : IsBDMove₅ lam mu) :
    IsBDPartition mu := by
  intro m hm_even
  by_cases hmzero : m = 0
  · rw [hmzero, parts_count_zero]
    exact ⟨0, rfl⟩
  rw [parts_count_eq_rowLens_count]
  rcases h with
    ⟨s, t, hst, hs_even, hs_pair, ht_even, ht_pair, hgap, hs, hs1, ht, ht1, hrest⟩
  let K := max ((YoungDiagram.ofPartition mu).colLen 0)
    ((YoungDiagram.ofPartition lam).colLen 0)
  have hKmu : (YoungDiagram.ofPartition mu).colLen 0 ≤ K := le_max_left _ _
  have hKlam : (YoungDiagram.ofPartition lam).colLen 0 ≤ K := le_max_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
  have hcount_mu := rowLens_count_eq_card_filter_range mu hKmu hmpos
  have hcount_lam := rowLens_count_eq_card_filter_range lam hKlam hmpos
  rw [hcount_mu]
  have heven_lam : Even ((Finset.range K).filter fun r => lam.rowLen r = m).card := by
    rw [← hcount_lam]
    exact rowLens_count_even_of_isBDPartition hlam hm_even
  by_cases hms : m = lam.rowLen s
  · let base := (Finset.range K).filter fun r => mu.rowLen r = m
    have hsK : s ∈ Finset.range K := by
      rw [Finset.mem_range]
      have hscol : s < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen s
        rw [← hms]
        exact hmpos
      exact lt_of_lt_of_le hscol hKlam
    have hs1K : s + 1 ∈ Finset.range K := by
      rw [Finset.mem_range]
      have hs1col : s + 1 < (YoungDiagram.ofPartition lam).colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        change 0 < lam.rowLen (s + 1)
        rw [← hs_pair, ← hms]
        exact hmpos
      exact lt_of_lt_of_le hs1col hKlam
    have hs_not_base : s ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have hs1_not_base : s + 1 ∉ base := by
      intro hmem
      have hrow := (Finset.mem_filter.mp hmem).2
      omega
    have hss1 : s ≠ s + 1 := by linarith
    have hfilter_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m) =
          insert s (insert (s + 1) base) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro ⟨hrK, hr⟩
        by_cases hrs : r = s
        · exact Or.inl hrs
        · by_cases hrs1 : r = s + 1
          · exact Or.inr (Or.inl hrs1)
          · by_cases hrt : r = t
            · subst r
              exfalso
              omega
            · by_cases hrt1 : r = t + 1
              · subst r
                exfalso
                omega
              · have hrmu := hrest r hrs hrs1 hrt hrt1
                exact Or.inr (Or.inr (by
                  exact Finset.mem_filter.mpr ⟨hrK, by linarith⟩))
      · rintro (rfl | rfl | hrbase)
        · exact ⟨hsK, hms.symm⟩
        · exact ⟨hs1K, by linarith⟩
        · change r ∈ (Finset.range K).filter (fun r => mu.rowLen r = m) at hrbase
          rcases Finset.mem_filter.mp hrbase with ⟨hrK, hrmu⟩
          by_cases hrs : r = s
          · subst r
            omega
          · by_cases hrs1 : r = s + 1
            · subst r
              omega
            · by_cases hrt : r = t
              · subst r
                exfalso
                omega
              · by_cases hrt1 : r = t + 1
                · subst r
                  exfalso
                  omega
                · have hrlam := hrest r hrs hrs1 hrt hrt1
                  exact ⟨hrK, by linarith⟩
    have hcard_lam :
        ((Finset.range K).filter fun r => lam.rowLen r = m).card =
          base.card + 2 := by
      rw [hfilter_lam]
      have hs_not_insert : s ∉ insert (s + 1) base := by
        simp [hs_not_base]
      rw [Finset.card_insert_of_notMem hs_not_insert]
      rw [Finset.card_insert_of_notMem hs1_not_base]
    have heven_base : Even base.card := by
      rw [hcard_lam] at heven_lam
      rcases heven_lam with ⟨c, hc⟩
      refine ⟨c - 1, ?_⟩
      dsimp [base] at hc ⊢
      omega
    exact heven_base
  · by_cases hmt : m = lam.rowLen t
    · let base := (Finset.range K).filter fun r => mu.rowLen r = m
      have htK : t ∈ Finset.range K := by
        rw [Finset.mem_range]
        have htcol : t < (YoungDiagram.ofPartition lam).colLen 0 := by
          rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
          change 0 < lam.rowLen t
          rw [← hmt]
          exact hmpos
        exact lt_of_lt_of_le htcol hKlam
      have ht1K : t + 1 ∈ Finset.range K := by
        rw [Finset.mem_range]
        have ht1col : t + 1 < (YoungDiagram.ofPartition lam).colLen 0 := by
          rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
          change 0 < lam.rowLen (t + 1)
          rw [← ht_pair, ← hmt]
          exact hmpos
        exact lt_of_lt_of_le ht1col hKlam
      have ht_not_base : t ∉ base := by
        intro hmem
        have hrow := (Finset.mem_filter.mp hmem).2
        omega
      have ht1_not_base : t + 1 ∉ base := by
        intro hmem
        have hrow := (Finset.mem_filter.mp hmem).2
        omega
      have htt1 : t ≠ t + 1 := by linarith
      have hfilter_lam :
          ((Finset.range K).filter fun r => lam.rowLen r = m) =
            insert t (insert (t + 1) base) := by
        ext r
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert]
        constructor
        · rintro ⟨hrK, hr⟩
          by_cases hrt : r = t
          · exact Or.inl hrt
          · by_cases hrt1 : r = t + 1
            · exact Or.inr (Or.inl hrt1)
            · by_cases hrs : r = s
              · subst r
                exfalso
                omega
              · by_cases hrs1 : r = s + 1
                · subst r
                  exfalso
                  omega
                · have hrmu := hrest r hrs hrs1 hrt hrt1
                  exact Or.inr (Or.inr (by
                    exact Finset.mem_filter.mpr ⟨hrK, by linarith⟩))
        · rintro (rfl | rfl | hrbase)
          · exact ⟨htK, hmt.symm⟩
          · exact ⟨ht1K, by linarith⟩
          · change r ∈ (Finset.range K).filter (fun r => mu.rowLen r = m) at hrbase
            rcases Finset.mem_filter.mp hrbase with ⟨hrK, hrmu⟩
            by_cases hrs : r = s
            · subst r
              exfalso
              omega
            · by_cases hrs1 : r = s + 1
              · subst r
                exfalso
                omega
              · by_cases hrt : r = t
                · subst r
                  omega
                · by_cases hrt1 : r = t + 1
                  · subst r
                    omega
                  · have hrlam := hrest r hrs hrs1 hrt hrt1
                    exact ⟨hrK, by linarith⟩
      have hcard_lam :
          ((Finset.range K).filter fun r => lam.rowLen r = m).card =
            base.card + 2 := by
        rw [hfilter_lam]
        have ht_not_insert : t ∉ insert (t + 1) base := by
          simp [ht_not_base]
        rw [Finset.card_insert_of_notMem ht_not_insert]
        rw [Finset.card_insert_of_notMem ht1_not_base]
      have heven_base : Even base.card := by
        rw [hcard_lam] at heven_lam
        rcases heven_lam with ⟨c, hc⟩
        refine ⟨c - 1, ?_⟩
        dsimp [base] at hc ⊢
        omega
      exact heven_base
    · have hfilter :
          ((Finset.range K).filter fun r => mu.rowLen r = m) =
            ((Finset.range K).filter fun r => lam.rowLen r = m) := by
        ext r
        rw [Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro ⟨hrK, hr⟩
          refine ⟨hrK, ?_⟩
          by_cases hrs : r = s
          · subst r
            exfalso
            rcases hm_even with ⟨a, ha⟩
            rcases hs_even with ⟨b, hb⟩
            omega
          · by_cases hrs1 : r = s + 1
            · subst r
              exfalso
              rcases hm_even with ⟨a, ha⟩
              rcases hs_even with ⟨b, hb⟩
              omega
            · by_cases hrt : r = t
              · subst r
                exfalso
                rcases hm_even with ⟨a, ha⟩
                rcases ht_even with ⟨b, hb⟩
                omega
              · by_cases hrt1 : r = t + 1
                · subst r
                  exfalso
                  rcases hm_even with ⟨a, ha⟩
                  rcases ht_even with ⟨b, hb⟩
                  omega
                · have hrlam := hrest r hrs hrs1 hrt hrt1
                  linarith
        · rintro ⟨hrK, hr⟩
          refine ⟨hrK, ?_⟩
          by_cases hrs : r = s
          · subst r
            exfalso
            exact hms hr.symm
          · by_cases hrs1 : r = s + 1
            · subst r
              exfalso
              exact hms (by linarith)
            · by_cases hrt : r = t
              · subst r
                exfalso
                exact hmt hr.symm
              · by_cases hrt1 : r = t + 1
                · subst r
                  exfalso
                  exact hmt (by linarith)
                · have hrlam := hrest r hrs hrs1 hrt hrt1
                  linarith
      rw [hfilter]
      exact heven_lam

lemma BDPartition.isBDMove_of_between_val {N : ℕ} {mu lam nu : BDPartition N}
    (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ (nu : Nat.Partition N))
    (hnu_le_lam : (nu : Nat.Partition N) ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : (nu : Nat.Partition N) ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove lam nu) :
    IsBDMove lam mu := by
  exact BDPartition.isBDMove_of_between h hmu_le_nu hnu_le_lam
    (fun hEq => hnu_ne_lam (congrArg Subtype.val hEq)) hmove

lemma BDPartition.isBDMove_of_between_isBDMove₁ {N : ℕ} {mu lam : BDPartition N}
    {nu : Nat.Partition N} (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ nu)
    (hnu_le_lam : nu ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : nu ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove₁ (lam : Nat.Partition N) nu) :
    IsBDMove lam mu := by
  let nuC : BDPartition N := ⟨nu, isBDPartition_of_isBDMove₁ lam.property hmove⟩
  exact BDPartition.isBDMove_of_between_val (nu := nuC) h hmu_le_nu hnu_le_lam
    hnu_ne_lam (Or.inl hmove)

lemma BDPartition.isBDMove_of_between_isBDMove₂ {N : ℕ} {mu lam : BDPartition N}
    {nu : Nat.Partition N} (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ nu)
    (hnu_le_lam : nu ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : nu ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove₂ (lam : Nat.Partition N) nu) :
    IsBDMove lam mu := by
  let nuC : BDPartition N := ⟨nu, isBDPartition_of_isBDMove₂ lam.property hmove⟩
  exact BDPartition.isBDMove_of_between_val (nu := nuC) h hmu_le_nu hnu_le_lam
    hnu_ne_lam (Or.inr (Or.inl hmove))

lemma BDPartition.isBDMove_of_between_isBDMove₃ {N : ℕ} {mu lam : BDPartition N}
    {nu : Nat.Partition N} (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ nu)
    (hnu_le_lam : nu ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : nu ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove₃ (lam : Nat.Partition N) nu) :
    IsBDMove lam mu := by
  let nuC : BDPartition N := ⟨nu, isBDPartition_of_isBDMove₃ lam.property hmove⟩
  exact BDPartition.isBDMove_of_between_val (nu := nuC) h hmu_le_nu hnu_le_lam
    hnu_ne_lam (Or.inr (Or.inr (Or.inl hmove)))

lemma BDPartition.isBDMove_of_between_isBDMove₄ {N : ℕ} {mu lam : BDPartition N}
    {nu : Nat.Partition N} (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ nu)
    (hnu_le_lam : nu ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : nu ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove₄ (lam : Nat.Partition N) nu) :
    IsBDMove lam mu := by
  let nuC : BDPartition N := ⟨nu, isBDPartition_of_isBDMove₄ lam.property hmove⟩
  exact BDPartition.isBDMove_of_between_val (nu := nuC) h hmu_le_nu hnu_le_lam
    hnu_ne_lam (Or.inr (Or.inr (Or.inr (Or.inl hmove))))

lemma BDPartition.isBDMove_of_between_isBDMove₅ {N : ℕ} {mu lam : BDPartition N}
    {nu : Nat.Partition N} (h : mu ⋖ lam)
    (hmu_le_nu : (mu : Nat.Partition N) ≤ nu)
    (hnu_le_lam : nu ≤ (lam : Nat.Partition N))
    (hnu_ne_lam : nu ≠ (lam : Nat.Partition N))
    (hmove : IsBDMove₅ (lam : Nat.Partition N) nu) :
    IsBDMove lam mu := by
  let nuC : BDPartition N := ⟨nu, isBDPartition_of_isBDMove₅ lam.property hmove⟩
  exact BDPartition.isBDMove_of_between_val (nu := nuC) h hmu_le_nu hnu_le_lam
    hnu_ne_lam (Or.inr (Or.inr (Or.inr (Or.inr hmove))))


end Nat.Partition





