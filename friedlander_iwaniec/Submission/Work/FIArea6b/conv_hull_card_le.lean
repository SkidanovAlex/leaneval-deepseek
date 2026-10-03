import Mathlib
import Submission.Work.FIArea6b.Basic
import Submission.Work.FIArea6b.volume_regionBetween_interp
import Submission.Work.FIArea6b.trapezoid_geom_bound
import Submission.Work.FIArea6b.card_le_sum_span
import Submission.Work.FIArea6b.trapRegion_subset
import Submission.Work.FIArea6b.nxtOn_sum_eq

namespace Work.FIArea6b

open MeasureTheory Set

/-! ## Own helpers -/

noncomputable def trapRegionI (A : Finset (ℤ × ℤ)) (t t' : ℤ) : Set (ℝ × ℝ) :=
  regionBetween
    (fun x : ℝ => (((t' : ℝ) - x) * (loOf A t : ℝ) + (x - (t : ℝ)) * (loOf A t' : ℝ))
      / ((t' : ℝ) - (t : ℝ)))
    (fun x : ℝ => (((t' : ℝ) - x) * (hiOf A t : ℝ) + (x - (t : ℝ)) * (hiOf A t' : ℝ))
      / ((t' : ℝ) - (t : ℝ)))
    (Set.Ioo (t : ℝ) (t' : ℝ))

lemma trapRegionI_subset_trapRegion (A : Finset (ℤ × ℤ)) (t t' : ℤ) :
    trapRegionI A t t' ⊆ trapRegion A t t' := by
  intro p hp
  simp only [trapRegionI, trapRegion, regionBetween, mem_ofPred_eq, mem_Ioo, mem_Icc] at hp ⊢
  exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩

lemma nxtOn_eq (T : Finset ℤ) (t : ℤ) (h : (T.filter (fun s => t < s)).Nonempty) :
    nxtOn T t = (T.filter (fun s => t < s)).min' h := by
  rw [nxtOn, dif_pos h]

lemma nxtOn_mem (T : Finset ℤ) (t : ℤ) (h : (T.filter (fun s => t < s)).Nonempty) :
    nxtOn T t ∈ T := by
  rw [nxtOn_eq T t h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

lemma nxtOn_gt (T : Finset ℤ) (t : ℤ) (h : (T.filter (fun s => t < s)).Nonempty) :
    t < nxtOn T t := by
  rw [nxtOn_eq T t h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

lemma nxtOn_le (T : Finset ℤ) (t b : ℤ) (h : (T.filter (fun s => t < s)).Nonempty)
    (hb : b ∈ T) (htb : t < b) : nxtOn T t ≤ b := by
  rw [nxtOn_eq T t h]
  exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, htb⟩)

lemma nxtOn_filter_nonempty (T : Finset ℤ) (hT : T.Nonempty) (t : ℤ) (ht : t ∈ T)
    (hmax : t ≠ T.max' hT) : (T.filter (fun s => t < s)).Nonempty := by
  refine ⟨T.max' hT, Finset.mem_filter.mpr ⟨Finset.max'_mem _ _, ?_⟩⟩
  have : t ≤ T.max' hT := Finset.le_max' _ _ ht
  exact lt_of_le_of_ne this hmax

lemma ys_nonempty (A : Finset (ℤ × ℤ)) (t : ℤ) (ht : t ∈ cols A) : (ys A t).Nonempty := by
  obtain ⟨p, hpA, hpt⟩ := Finset.mem_image.mp ht
  exact ⟨p.2, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hpA, hpt⟩, rfl⟩⟩

lemma loOf_mem (A : Finset (ℤ × ℤ)) (t : ℤ) (ht : t ∈ cols A) : loOf A t ∈ ys A t := by
  rw [loOf, dif_pos (ys_nonempty A t ht)]
  exact Finset.min'_mem _ _

lemma hiOf_mem (A : Finset (ℤ × ℤ)) (t : ℤ) (ht : t ∈ cols A) : hiOf A t ∈ ys A t := by
  rw [hiOf, dif_pos (ys_nonempty A t ht)]
  exact Finset.max'_mem _ _

lemma loOf_le_hiOf' (A : Finset (ℤ × ℤ)) (t : ℤ) (ht : t ∈ cols A) : loOf A t ≤ hiOf A t := by
  rw [loOf, dif_pos (ys_nonempty A t ht), hiOf, dif_pos (ys_nonempty A t ht)]
  exact Finset.min'_le _ _ (Finset.max'_mem _ _)

lemma spanOf_nonneg (A : Finset (ℤ × ℤ)) (t : ℤ) (ht : t ∈ cols A) : 0 ≤ spanOf A t := by
  have h := loOf_le_hiOf' A t ht
  simp only [spanOf]
  have : (loOf A t : ℝ) ≤ (hiOf A t : ℝ) := by exact_mod_cast h
  linarith

lemma trapRegion_vol (A : Finset (ℤ × ℤ)) (t t' : ℤ) (ht : t ∈ cols A) (ht' : t' ∈ cols A)
    (htt' : t < t') :
    MeasureTheory.volume (trapRegion A t t')
      = ENNReal.ofReal (((t' : ℝ) - (t : ℝ)) * (spanOf A t + spanOf A t') / 2) := by
  have h1 : (loOf A t : ℝ) ≤ (hiOf A t : ℝ) := by exact_mod_cast (loOf_le_hiOf' A t ht)
  have h2 : (loOf A t' : ℝ) ≤ (hiOf A t' : ℝ) := by exact_mod_cast (loOf_le_hiOf' A t' ht')
  have hcast : (t : ℝ) < (t' : ℝ) := by exact_mod_cast htt'
  simp only [trapRegion]
  exact volume_regionBetween_interp (t : ℝ) (t' : ℝ) (loOf A t : ℝ) (loOf A t' : ℝ)
      (hiOf A t : ℝ) (hiOf A t' : ℝ) hcast h1 h2

lemma volume_singleton_prod (c : ℝ) :
    MeasureTheory.volume ({c} ×ˢ (Set.univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_singleton]
  simp

lemma volume_regionBetween_Ioo_eq_Icc (f g : ℝ → ℝ) (a b : ℝ) :
    MeasureTheory.volume (regionBetween f g (Set.Ioo a b))
      = MeasureTheory.volume (regionBetween f g (Set.Icc a b)) := by
  apply le_antisymm
  · exact measure_mono (fun p hp => ⟨Set.Ioo_subset_Icc_self hp.1, hp.2⟩)
  · calc MeasureTheory.volume (regionBetween f g (Set.Icc a b))
        ≤ MeasureTheory.volume (regionBetween f g (Set.Ioo a b)
            ∪ ({a} ×ˢ (Set.univ : Set ℝ) ∪ {b} ×ˢ (Set.univ : Set ℝ))) := by
          apply measure_mono
          intro p hp
          simp only [regionBetween, mem_ofPred_eq, mem_Icc, mem_Ioo, mem_union, mem_prod,
            mem_singleton, mem_univ] at hp ⊢
          obtain ⟨⟨h1, h2⟩, h3⟩ := hp
          rcases lt_or_eq_of_le h1 with h | h
          · rcases lt_or_eq_of_le h2 with h2' | h2'
            · exact Or.inl ⟨⟨h, h2'⟩, h3⟩
            · exact Or.inr (Or.inr ⟨h2', trivial⟩)
          · exact Or.inr (Or.inl ⟨h.symm, trivial⟩)
      _ ≤ MeasureTheory.volume (regionBetween f g (Set.Ioo a b))
            + MeasureTheory.volume ({a} ×ˢ (Set.univ : Set ℝ) ∪ {b} ×ˢ (Set.univ : Set ℝ)) :=
          measure_union_le _ _
      _ = MeasureTheory.volume (regionBetween f g (Set.Ioo a b)) + 0 := by
          congr 1
          refine le_antisymm ?_ bot_le
          calc MeasureTheory.volume ({a} ×ˢ (Set.univ : Set ℝ) ∪ {b} ×ˢ (Set.univ : Set ℝ))
              ≤ MeasureTheory.volume ({a} ×ˢ (Set.univ : Set ℝ))
                + MeasureTheory.volume ({b} ×ˢ (Set.univ : Set ℝ)) := measure_union_le _ _
            _ = 0 := by rw [volume_singleton_prod a, volume_singleton_prod b, add_zero]
      _ = MeasureTheory.volume (regionBetween f g (Set.Ioo a b)) := add_zero _

lemma trapRegionI_vol (A : Finset (ℤ × ℤ)) (t t' : ℤ) (ht : t ∈ cols A) (ht' : t' ∈ cols A)
    (htt' : t < t') :
    MeasureTheory.volume (trapRegionI A t t')
      = ENNReal.ofReal (((t' : ℝ) - (t : ℝ)) * (spanOf A t + spanOf A t') / 2) := by
  rw [← trapRegion_vol A t t' ht ht' htt']
  simp only [trapRegionI, trapRegion]
  exact volume_regionBetween_Ioo_eq_Icc _ _ _ _

lemma phi_ball (A : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (R : ℝ)
    (hball : ∀ x ∈ A, ((x.1 : ℝ) - c.1) ^ 2 + ((x.2 : ℝ) - c.2) ^ 2 ≤ R ^ 2)
    (t : ℤ) (ht : t ∈ cols A) (y : ℤ) (hy : y ∈ ys A t) :
    ((t : ℝ) - c.1) ^ 2 + ((y : ℝ) - c.2) ^ 2 ≤ R ^ 2 := by
  obtain ⟨q, hq, hqy⟩ := Finset.mem_image.mp hy
  have hq1 : q.1 = t := (Finset.mem_filter.mp hq).2
  have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
  have h := hball q hqA
  rw [hq1, hqy] at h
  exact h

lemma phi_strip (r s : ℤ) (W : ℝ) (A : Finset (ℤ × ℤ))
    (hstrip : ∀ x ∈ A, |(r : ℝ) * (x.2 : ℝ) - (s : ℝ) * (x.1 : ℝ)| ≤ W)
    (t : ℤ) (ht : t ∈ cols A) (y : ℤ) (hy : y ∈ ys A t) :
    |(r : ℝ) * (y : ℝ) - (s : ℝ) * (t : ℝ)| ≤ W := by
  obtain ⟨q, hq, hqy⟩ := Finset.mem_image.mp hy
  have hq1 : q.1 = t := (Finset.mem_filter.mp hq).2
  have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
  have h := hstrip q hqA
  rw [hq1, hqy] at h
  exact h


lemma sum_span_le_vol (A : Finset (ℤ × ℤ)) (hA : A.Nonempty)
    (hfin : MeasureTheory.volume (Kset A) ≠ ⊤) :
    ∑ t ∈ cols A, spanOf A t
      ≤ (MeasureTheory.volume (Kset A)).toReal
        + (spanOf A ((cols A).min' (hA.image (fun p => p.1)))
            + spanOf A ((cols A).max' (hA.image (fun p => p.1)))) / 2 := by
  have hT : (cols A).Nonempty := hA.image (fun p => p.1)
  have hkey : ∑ t ∈ cols A, spanOf A t
      = ∑ t ∈ (cols A).erase ((cols A).max' hT),
          (spanOf A t + spanOf A (nxtOn (cols A) t)) / 2
        + (spanOf A ((cols A).min' hT) + spanOf A ((cols A).max' hT)) / 2 := by
    have hA1 := Finset.sum_erase_add (cols A) (fun t => spanOf A t) (Finset.min'_mem (cols A) hT)
    have hA2 := Finset.sum_erase_add (cols A) (fun t => spanOf A t) (Finset.max'_mem (cols A) hT)
    have hB := nxtOn_sum_eq (cols A) hT (fun t => spanOf A t)
    have e1 : ∑ t ∈ (cols A).erase ((cols A).min' hT), spanOf A t
        = (∑ t ∈ cols A, spanOf A t) - spanOf A ((cols A).min' hT) := by linarith
    have e2 : ∑ t ∈ (cols A).erase ((cols A).max' hT), spanOf A t
        = (∑ t ∈ cols A, spanOf A t) - spanOf A ((cols A).max' hT) := by linarith
    have h2 : ∑ t ∈ (cols A).erase ((cols A).max' hT),
        (spanOf A t + spanOf A (nxtOn (cols A) t)) / 2
        = ((∑ t ∈ (cols A).erase ((cols A).max' hT), spanOf A t)
            + (∑ t ∈ (cols A).erase ((cols A).max' hT), spanOf A (nxtOn (cols A) t))) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [h2, hB, e1, e2]
    ring
  have hb : ∑ t ∈ (cols A).erase ((cols A).max' hT),
        (spanOf A t + spanOf A (nxtOn (cols A) t)) / 2
      ≤ (MeasureTheory.volume (Kset A)).toReal := by
    set f : ℤ → Set (ℝ × ℝ) := fun t => trapRegionI A t (nxtOn (cols A) t) with hfdef
    have hmemE : ∀ t ∈ (cols A).erase ((cols A).max' hT),
        t ∈ cols A ∧ t ≠ (cols A).max' hT := by
      intro t ht; exact ⟨(Finset.mem_erase.mp ht).2, (Finset.mem_erase.mp ht).1⟩
    have hne : ∀ t ∈ (cols A).erase ((cols A).max' hT),
        ((cols A).filter (fun s => t < s)).Nonempty := fun t ht =>
      nxtOn_filter_nonempty (cols A) hT t (hmemE t ht).1 (hmemE t ht).2
    have hmemN : ∀ t ∈ (cols A).erase ((cols A).max' hT), nxtOn (cols A) t ∈ cols A :=
      fun t ht => nxtOn_mem (cols A) t (hne t ht)
    have hgtN : ∀ t ∈ (cols A).erase ((cols A).max' hT), t < nxtOn (cols A) t :=
      fun t ht => nxtOn_gt (cols A) t (hne t ht)
    have hmeas : ∀ b ∈ (cols A).erase ((cols A).max' hT), MeasurableSet (f b) := by
      intro b hb
      rw [hfdef]
      exact measurableSet_regionBetween (by fun_prop) (by fun_prop) measurableSet_Ioo
    have htop : ∀ b ∈ (cols A).erase ((cols A).max' hT), MeasureTheory.volume (f b) ≠ ⊤ := by
      intro b hb
      refine ne_top_of_le_ne_top hfin (measure_mono ?_)
      rw [hfdef]
      exact fun p hp => trapRegion_subset A b (nxtOn (cols A) b) (hmemE b hb).1 (hmemN b hb)
        (hgtN b hb) (trapRegionI_subset_trapRegion A b (nxtOn (cols A) b) hp)
    have hdisj : ((cols A).erase ((cols A).max' hT) : Set ℤ).PairwiseDisjoint f := by
      intro a ha b hb hab
      show Disjoint (f a) (f b)
      rw [Set.disjoint_left]
      intro p hpa hpb
      rw [hfdef] at hpa hpb
      simp only [trapRegionI, regionBetween, mem_ofPred_eq, mem_Ioo] at hpa hpb
      rcases lt_or_gt_of_ne hab with hablt | habgt
      · have h1 : p.1 < (b : ℝ) := lt_of_lt_of_le hpa.1.2
          (by exact_mod_cast (nxtOn_le (cols A) a b (hne a ha) (hmemE b hb).1 hablt))
        exact absurd h1 (not_lt.mpr (le_of_lt hpb.1.1))
      · have h1 : p.1 < (a : ℝ) := lt_of_lt_of_le hpb.1.2
          (by exact_mod_cast (nxtOn_le (cols A) b a (hne b hb) (hmemE a ha).1 habgt))
        exact absurd h1 (not_lt.mpr (le_of_lt hpa.1.1))
    have hsub : (⋃ b ∈ (cols A).erase ((cols A).max' hT), f b) ⊆ Kset A := by
      intro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨b, hb⟩ := hp
      rw [Set.mem_iUnion] at hb
      obtain ⟨hbm, hpb⟩ := hb
      rw [hfdef] at hpb
      exact trapRegion_subset A b (nxtOn (cols A) b) (hmemE b hbm).1 (hmemN b hbm) (hgtN b hbm)
        (trapRegionI_subset_trapRegion A b (nxtOn (cols A) b) hpb)
    calc ∑ t ∈ (cols A).erase ((cols A).max' hT),
            (spanOf A t + spanOf A (nxtOn (cols A) t)) / 2
        ≤ ∑ t ∈ (cols A).erase ((cols A).max' hT), (MeasureTheory.volume (f t)).toReal := by
          apply Finset.sum_le_sum
          intro t ht
          have hsp1 : 0 ≤ spanOf A t := spanOf_nonneg A t (hmemE t ht).1
          have hsp2 : 0 ≤ spanOf A (nxtOn (cols A) t) := spanOf_nonneg A _ (hmemN t ht)
          have hX : 0 ≤ spanOf A t + spanOf A (nxtOn (cols A) t) := by linarith
          have hd : (1 : ℝ) ≤ (nxtOn (cols A) t : ℝ) - (t : ℝ) := by
            have h' : t + 1 ≤ nxtOn (cols A) t := by
              have := hgtN t ht; omega
            have : ((t : ℤ) + 1 : ℝ) ≤ ((nxtOn (cols A) t : ℤ) : ℝ) := by exact_mod_cast h'
            push_cast at this
            linarith
          have harg : 0 ≤ ((nxtOn (cols A) t : ℝ) - (t : ℝ))
              * (spanOf A t + spanOf A (nxtOn (cols A) t)) / 2 := by
            apply div_nonneg _ (by norm_num)
            exact mul_nonneg (by linarith) hX
          have hvol := trapRegionI_vol A t (nxtOn (cols A) t) (hmemE t ht).1 (hmemN t ht) (hgtN t ht)
          rw [hfdef, hvol, ENNReal.toReal_ofReal harg]
          nlinarith [hX, hd]
      _ = (∑ t ∈ (cols A).erase ((cols A).max' hT), MeasureTheory.volume (f t)).toReal :=
          (ENNReal.toReal_sum htop).symm
      _ = (MeasureTheory.volume (⋃ b ∈ (cols A).erase ((cols A).max' hT), f b)).toReal := by
          rw [measure_biUnion_finset hdisj hmeas]
      _ ≤ (MeasureTheory.volume (Kset A)).toReal := measureReal_mono hsub hfin
  linarith [hkey, hb]

theorem conv_hull_card_le (r s : ℤ) (hne : r ≠ 0 ∨ s ≠ 0) (R W : ℝ) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (c : ℝ × ℝ) (A : Finset (ℤ × ℤ))
    (hball : ∀ x ∈ A, ((x.1 : ℝ) - c.1) ^ 2 + ((x.2 : ℝ) - c.2) ^ 2 ≤ R ^ 2)
    (hstrip : ∀ x ∈ A, |(r : ℝ) * (x.2 : ℝ) - (s : ℝ) * (x.1 : ℝ)| ≤ W) :
    (A.card : ℝ) ≤ (MeasureTheory.volume
        (convexHull ℝ ((A.image (fun x : ℤ × ℤ => ((x.1 : ℝ), (x.2 : ℝ)))) : Set (ℝ × ℝ)))).toReal
      + 2 * R + 2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) + 1 := by
  rcases eq_or_ne A ∅ with hAe | hAne
  · rw [hAe]
    have hsp : 0 ≤ 2 * W / Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) :=
      div_nonneg (by linarith) (Real.sqrt_nonneg _)
    simp only [Finset.card_empty, Nat.cast_zero, Finset.image_empty, Finset.coe_empty,
      convexHull_empty, MeasureTheory.measure_empty, ENNReal.toReal_zero]
    linarith
  · have hA : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAne
    have hfin : MeasureTheory.volume (Kset A) ≠ ⊤ := by
      have hboxfin : MeasureTheory.volume
          (Set.Icc (c.1 - R) (c.1 + R) ×ˢ Set.Icc (c.2 - R) (c.2 + R)) ≠ ⊤ := by
        rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      refine ne_top_of_le_ne_top hboxfin (measure_mono ?_)
      rw [Kset]
      refine convexHull_min ?_ (Convex.prod (convex_Icc (c.1 - R) (c.1 + R)) (convex_Icc (c.2 - R) (c.2 + R)))
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_image] at hp
      obtain ⟨x, hxA, rfl⟩ := hp
      simp only [phi, mem_prod, mem_Icc]
      have h := hball x hxA
      constructor
      · have hx : ((x.1 : ℝ) - c.1) ^ 2 ≤ R ^ 2 := by linarith [sq_nonneg ((x.2 : ℝ) - c.2)]
        have h2 := sq_le_sq.mp hx
        rw [abs_of_nonneg hR, abs_le] at h2
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      · have hx : ((x.2 : ℝ) - c.2) ^ 2 ≤ R ^ 2 := by linarith [sq_nonneg ((x.1 : ℝ) - c.1)]
        have h2 := sq_le_sq.mp hx
        rw [abs_of_nonneg hR, abs_le] at h2
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hsum := sum_span_le_vol A hA hfin
    have hcard := card_le_sum_span A
    have hsplit : ∑ t ∈ cols A, (spanOf A t + 1)
        = (∑ t ∈ cols A, spanOf A t) + ((cols A).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hT : (cols A).Nonempty := hA.image (fun p => p.1)
    have hcolscard : ((cols A).card : ℝ)
        ≤ ((cols A).max' hT : ℝ) - ((cols A).min' hT : ℝ) + 1 := by
      have hle : (cols A).card
          ≤ (Finset.Icc ((cols A).min' hT) ((cols A).max' hT)).card :=
        Finset.card_le_card (fun t ht =>
          Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ ht, Finset.le_max' _ _ ht⟩)
      rw [Int.card_Icc] at hle
      have hnn : 0 ≤ ((cols A).max' hT + 1 - (cols A).min' hT : ℤ) := by
        have := Finset.min'_le _ _ (Finset.max'_mem _ hT); omega
      calc ((cols A).card : ℝ)
            ≤ ((((cols A).max' hT + 1 - (cols A).min' hT : ℤ)).toNat : ℝ) := by exact_mod_cast hle
        _ ≤ ((((cols A).max' hT + 1 - (cols A).min' hT : ℤ)) : ℝ) := by
            have h4 : ((((cols A).max' hT + 1 - (cols A).min' hT : ℤ)).toNat : ℤ)
                ≤ ((cols A).max' hT + 1 - (cols A).min' hT : ℤ) := by
              rw [Int.toNat_of_nonneg hnn]
            exact_mod_cast h4
        _ = ((cols A).max' hT : ℝ) - ((cols A).min' hT : ℝ) + 1 := by push_cast; ring
    set ρ : ℝ := Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef, Real.sqrt_pos]
      rcases hne with h | h
      · have hr : (r : ℝ) ≠ 0 := by exact_mod_cast h
        nlinarith [sq_pos_of_ne_zero hr, sq_nonneg ((s : ℝ))]
      · have hs : (s : ℝ) ≠ 0 := by exact_mod_cast h
        nlinarith [sq_pos_of_ne_zero hs, sq_nonneg ((r : ℝ))]
    set w : ℝ := 2 * W / ρ with hwdef
    have hw0 : 0 ≤ w := by rw [hwdef]; exact div_nonneg (by linarith) (le_of_lt hρpos)
    set nvec : ℝ × ℝ := ((-(s : ℝ)) / ρ, (r : ℝ) / ρ) with hnvecdef
    have hn : nvec.1 ^ 2 + nvec.2 ^ 2 = 1 := by
      rw [hnvecdef]
      have hρ2 : ρ ^ 2 = (r : ℝ) ^ 2 + (s : ℝ) ^ 2 := by rw [hρdef, Real.sq_sqrt (by positivity)]
      have hρne : ρ ≠ 0 := ne_of_gt hρpos
      field_simp
      rw [hρ2]; ring
    have hgeom : (spanOf A ((cols A).min' hT) + spanOf A ((cols A).max' hT)) / 2
        + (((cols A).max' hT : ℝ) - ((cols A).min' hT : ℝ)) ≤ 2 * R + 2 * W / ρ := by
      have hnstrip : ∀ t ∈ cols A, ∀ y ∈ ys A t,
          |nvec.1 * (t : ℝ) + nvec.2 * (y : ℝ) - 0| ≤ w / 2 := by
        intro t ht y hy
        have h := phi_strip r s W A hstrip t ht y hy
        rw [hnvecdef, hwdef]
        rw [show ((-(s : ℝ)) / ρ * (t : ℝ) + (r : ℝ) / ρ * (y : ℝ) - 0)
            = ((r : ℝ) * (y : ℝ) - (s : ℝ) * (t : ℝ)) / ρ from by ring]
        rw [abs_div, abs_of_pos hρpos, show (2 * W / ρ) / 2 = W / ρ from by ring]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hρpos))
      have hkey := trapezoid_geom_bound R w hR hw0 nvec 0
        ((cols A).min' hT : ℝ) ((cols A).max' hT : ℝ)
        (loOf A ((cols A).min' hT) : ℝ) (loOf A ((cols A).max' hT) : ℝ)
        (hiOf A ((cols A).min' hT) : ℝ) (hiOf A ((cols A).max' hT) : ℝ) c
        (by exact_mod_cast Finset.min'_le _ _ (Finset.max'_mem _ hT))
        (by exact_mod_cast loOf_le_hiOf' A _ (Finset.min'_mem (cols A) hT))
        (by exact_mod_cast loOf_le_hiOf' A _ (Finset.max'_mem (cols A) hT))
        hn
        (by
          intro p hp
          rcases hp with hp | hp | hp | hp
          · rw [hp]
            exact phi_ball A c R hball _ (Finset.min'_mem (cols A) hT) _
              (loOf_mem A _ (Finset.min'_mem (cols A) hT))
          · rw [hp]
            exact phi_ball A c R hball _ (Finset.max'_mem (cols A) hT) _
              (loOf_mem A _ (Finset.max'_mem (cols A) hT))
          · rw [hp]
            exact phi_ball A c R hball _ (Finset.max'_mem (cols A) hT) _
              (hiOf_mem A _ (Finset.max'_mem (cols A) hT))
          · rw [hp]
            exact phi_ball A c R hball _ (Finset.min'_mem (cols A) hT) _
              (hiOf_mem A _ (Finset.min'_mem (cols A) hT)))
        (by
          intro p hp
          rcases hp with hp | hp | hp | hp
          · rw [hp]; exact hnstrip _ (Finset.min'_mem (cols A) hT) _
              (loOf_mem A _ (Finset.min'_mem (cols A) hT))
          · rw [hp]; exact hnstrip _ (Finset.max'_mem (cols A) hT) _
              (loOf_mem A _ (Finset.max'_mem (cols A) hT))
          · rw [hp]; exact hnstrip _ (Finset.max'_mem (cols A) hT) _
              (hiOf_mem A _ (Finset.max'_mem (cols A) hT))
          · rw [hp]; exact hnstrip _ (Finset.min'_mem (cols A) hT) _
              (hiOf_mem A _ (Finset.min'_mem (cols A) hT)))
      rw [hwdef] at hkey
      have h1 : (spanOf A ((cols A).min' hT) + spanOf A ((cols A).max' hT)) / 2
          + (((cols A).max' hT : ℝ) - ((cols A).min' hT : ℝ))
          = ((hiOf A ((cols A).min' hT) : ℝ) - (loOf A ((cols A).min' hT) : ℝ)) / 2
            + ((hiOf A ((cols A).max' hT) : ℝ) - (loOf A ((cols A).max' hT) : ℝ)) / 2
            + (((cols A).max' hT : ℝ) - ((cols A).min' hT : ℝ)) := by
        simp only [spanOf]; ring
      rw [h1]
      exact hkey
    have hmain : (A.card : ℝ)
        ≤ (MeasureTheory.volume (Kset A)).toReal + 2 * R + 2 * W / ρ + 1 := by
      have h1 := hcard
      rw [hsplit] at h1
      linarith [h1, hsum, hcolscard, hgeom]
    rw [hρdef] at hmain
    exact hmain

end Work.FIArea6b
