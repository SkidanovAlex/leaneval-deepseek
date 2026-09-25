import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Calculus

open MeasureTheory Set intervalIntegral

/-- Layer-cake identity: for `0 ≤ s ≤ c`, the integral against the indicator of `Iio s`
of the constant function `1` on `(0, c]` equals `s`. -/
theorem integral_indicator_Iio_one {c s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ c) :
    ∫ u in (0 : ℝ)..c, (if u < s then (1 : ℝ) else 0) = s := by
  have h0c : (0 : ℝ) ≤ c := hs0.trans hsc
  have hfun : (fun u : ℝ => (if u < s then (1 : ℝ) else 0))
      = (Set.Iio s).indicator (fun _ => (1 : ℝ)) := by
    funext u; by_cases h : u < s <;> simp [Set.indicator, h]
  rw [intervalIntegral.integral_of_le h0c, hfun, setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc (0 : ℝ) c ∩ Set.Iio s = Set.Ioo (0 : ℝ) s := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Iio]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (le_of_lt h.2).trans hsc⟩, h.2⟩⟩
  rw [hset, setIntegral_const]
  simp [Real.volume_real_Ioo_of_le hs0]

/-- If `D` is a "half open upper interval inside `[a,b]` ending at `b`", i.e.
`Ioc c b ⊆ D ⊆ Icc c b` with `c ∈ [a,b]`, then integrating the indicator of `D` against `h`
over `a..b` is the same as integrating `h` over `c..b`. -/
theorem intervalIntegral_indicator_eq_intervalIntegral {a b c : ℝ} (hab : a ≤ b)
    (hc : c ∈ Set.Icc a b) {D : Set ℝ} (hlo : Set.Ioc c b ⊆ D) (hhi : D ⊆ Set.Icc c b)
    (h : ℝ → ℝ) :
    ∫ t in a..b, D.indicator h t = ∫ t in c..b, h t := by
  have hcb : c ≤ b := hc.2
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcb]
  have hkey : ∫ t in Set.Ioc a b, D.indicator h t
      = ∫ t in Set.Ioc a b, (Set.Ioc c b).indicator h t := by
    apply setIntegral_congr_ae measurableSet_Ioc
    have hcompl : ∀ᵐ x ∂volume, x ∉ ({c} : Set ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hcompl] with x hx _
    by_cases hxD : x ∈ D
    · have hmem : x ∈ Set.Ioc c b :=
        ⟨lt_of_le_of_ne (hhi hxD).1 (fun hcx => hx hcx.symm), (hhi hxD).2⟩
      simp [Set.indicator_of_mem hxD, Set.indicator_of_mem hmem]
    · have hmem : x ∉ Set.Ioc c b := fun hh => hxD (hlo hh)
      simp [Set.indicator_of_notMem hxD, Set.indicator_of_notMem hmem]
  have hset : Set.Ioc a b ∩ Set.Ioc c b = Set.Ioc c b := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc]
    exact ⟨fun h => h.2, fun h => ⟨⟨lt_of_le_of_lt hc.1 h.1, h.2⟩, h⟩⟩
  rw [hkey, setIntegral_indicator measurableSet_Ioc, hset]

/-- Second mean value theorem (Bonnet) bound: if `g` is monotone and nonnegative on `[a,b]`,
`h` is continuous there, and all tail-integrals `∫_x^b h` are bounded by `M` in absolute
value, then `|∫_a^b g h| ≤ g b * M`. -/
theorem monotone_weight_integral_bound {a b : ℝ} (hab : a ≤ b) {g h : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc a b)) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hh : ContinuousOn h (Set.Icc a b)) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc a b, |∫ t in x..b, h t| ≤ M) :
    |∫ t in a..b, g t * h t| ≤ g b * M := by
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ha)
  have hgb0 : 0 ≤ g b := hg0 b hb
  set F : ℝ → ℝ → ℝ := fun u t => (if u < g t then (1 : ℝ) else 0) * h t with hF
  have hinner : ∀ u ∈ Set.Icc (0 : ℝ) (g b), |∫ t in a..b, F u t| ≤ M := by
    intro u hu
    set D : Set ℝ := Set.Icc a b ∩ {t | u < g t} with hD
    have hFeq : ∫ t in a..b, F u t = ∫ t in a..b, D.indicator h t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have hiff : t ∈ D ↔ u < g t := by
        simp only [hD, Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
      show (if u < g t then (1 : ℝ) else 0) * h t = D.indicator h t
      by_cases hlt : u < g t
      · rw [if_pos hlt, one_mul]
        exact (Set.indicator_of_mem (hiff.mpr hlt) h).symm
      · rw [if_neg hlt, zero_mul]
        exact (Set.indicator_of_notMem (fun hh => hlt (hiff.mp hh)) h).symm
    rw [hFeq]
    by_cases hne : D.Nonempty
    · have hltb : u < g b := by
        obtain ⟨t0, ht0⟩ := hne
        exact lt_of_lt_of_le ht0.2 (hg ht0.1 hb ht0.1.2)
      have hbD : b ∈ D := ⟨hb, hltb⟩
      set c : ℝ := sInf D with hcdef
      have hbdd : BddBelow D := ⟨a, fun y hy => hy.1.1⟩
      have hc_le_b : c ≤ b := by rw [hcdef]; exact csInf_le hbdd hbD
      have ha_le_c : a ≤ c := by rw [hcdef]; exact le_csInf hne (fun y hy => hy.1.1)
      have hc_mem : c ∈ Set.Icc a b := ⟨ha_le_c, hc_le_b⟩
      have hlo : Set.Ioc c b ⊆ D := by
        intro t ht
        obtain ⟨s, hsD, hst⟩ := exists_lt_of_csInf_lt hne (by rw [← hcdef]; exact ht.1)
        refine ⟨⟨hsD.1.1.trans hst.le, ht.2⟩, ?_⟩
        exact lt_of_lt_of_le hsD.2 (hg hsD.1 ⟨hsD.1.1.trans hst.le, ht.2⟩ hst.le)
      have hhi : D ⊆ Set.Icc c b := by
        intro t ht
        exact ⟨by rw [hcdef]; exact csInf_le hbdd ht, ht.1.2⟩
      rw [intervalIntegral_indicator_eq_intervalIntegral hab hc_mem hlo hhi h]
      exact hM c hc_mem
    · have hDempty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hzero : ∫ t in a..b, D.indicator h t = 0 := by
        have : D.indicator h = (fun _ => (0 : ℝ)) := by funext t; simp [hDempty]
        rw [this, intervalIntegral.integral_zero]
      rw [hzero, abs_zero]
      exact hM0
  have hgaem : AEMeasurable g (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioc (hg.mono Ioc_subset_Icc_self)
  have hhaem : AEMeasurable h (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (hh.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hint : IntegrableOn (Function.uncurry F) (Set.uIoc 0 (g b) ×ˢ Set.uIoc a b)
      volume := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
    refine IntegrableOn.of_bound ?hs ?hmeas (max C 0) ?hbd
    · have hfin : volume (Set.uIcc (0 : ℝ) (g b) ×ˢ Set.uIcc a b) < ⊤ :=
        (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
      exact lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)) hfin
    · have hψ : Measurable (fun q : ℝ × ℝ => if q.1 < q.2 then (1 : ℝ) else 0) := by
        have hs : MeasurableSet {q : ℝ × ℝ | q.1 < q.2} :=
          measurableSet_lt measurable_fst measurable_snd
        have h2 : Measurable (({q : ℝ × ℝ | q.1 < q.2}).indicator (fun _ => (1 : ℝ))) :=
          measurable_const.indicator hs
        convert h2 using 1
        ext q; by_cases h : q.1 < q.2 <;> simp [Set.indicator, h]
      have hφ : AEMeasurable (fun p : ℝ × ℝ => (p.1, g p.2))
          ((volume.restrict (Set.uIoc 0 (g b))).prod (volume.restrict (Set.uIoc a b))) :=
        measurable_fst.aemeasurable.prodMk hgaem.comp_snd
      have hmain : AEMeasurable (Function.uncurry F)
          ((volume.restrict (Set.uIoc 0 (g b))).prod (volume.restrict (Set.uIoc a b))) := by
        have hcomp : AEMeasurable (fun p : ℝ × ℝ => (if p.1 < g p.2 then (1 : ℝ) else 0))
            ((volume.restrict (Set.uIoc 0 (g b))).prod (volume.restrict (Set.uIoc a b))) :=
          hψ.comp_aemeasurable hφ
        have hmul := hcomp.mul (hhaem.comp_snd)
        convert hmul using 1
        ext p; simp only [Function.uncurry, hF, Pi.mul_apply]
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      rw [← Measure.prod_restrict]
      exact hmain.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem
          (measurableSet_uIoc.prod measurableSet_uIoc)] with x hx
      have hx2 : x.2 ∈ Set.Icc a b := by
        have hx2' : x.2 ∈ Set.uIoc a b := (Set.mem_prod.mp hx).2
        rw [Set.uIoc_of_le hab] at hx2'
        exact ⟨hx2'.1.le, hx2'.2⟩
      have habs : ‖(if x.1 < g x.2 then (1 : ℝ) else 0)‖ ≤ 1 := by
        split <;> simp
      calc ‖Function.uncurry F x‖ = ‖(if x.1 < g x.2 then (1 : ℝ) else 0)‖ * ‖h x.2‖ := by
            simp only [Function.uncurry, hF, norm_mul]
        _ ≤ 1 * ‖h x.2‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖h x.2‖ := one_mul _
        _ ≤ C := hC x.2 hx2
        _ ≤ max C 0 := le_max_left _ _
  have hswap := intervalIntegral_intervalIntegral_swap (F := F) (a := 0) (b := g b)
    (c := a) (d := b) hint
  have hcongr : ∫ t in a..b, (∫ u in (0 : ℝ)..(g b), F u t) = ∫ t in a..b, g t * h t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    show (∫ u in (0 : ℝ)..(g b), (if u < g t then (1 : ℝ) else 0) * h t) = g t * h t
    rw [intervalIntegral.integral_mul_const (h t) (fun u : ℝ => (if u < g t then (1 : ℝ) else 0))]
    rw [integral_indicator_Iio_one (hg0 t ht) (hg ht hb ht.2)]
  have hbound : |∫ u in (0 : ℝ)..(g b), (∫ t in a..b, F u t)| ≤ M * g b := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u => ∫ t in a..b, F u t) (a := 0) (b := g b) (C := M)
      (fun x hx => by
        rw [Set.uIoc_of_le hgb0] at hx
        exact hinner x ⟨hx.1.le, hx.2⟩)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hgb0] at hle
  calc |∫ t in a..b, g t * h t|
      = |∫ t in a..b, (∫ u in (0 : ℝ)..(g b), F u t)| := by rw [← hcongr]
    _ = |∫ u in (0 : ℝ)..(g b), (∫ t in a..b, F u t)| := by rw [hswap]
    _ ≤ M * g b := hbound
    _ = g b * M := by ring

end Commons.Analysis.Calculus