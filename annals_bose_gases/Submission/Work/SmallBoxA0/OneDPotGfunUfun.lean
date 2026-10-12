import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.SmallBoxA0.OneDPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Set

/-- The `1/s`-weighted radial source `s ↦ (s ^ 2 * p s) / s`, the integrand of `qfun p`. -/
noncomputable def divsq (p : ℝ → ℝ) : ℝ → ℝ := fun s => (s ^ 2 * p s) / s

/-- The product-space integrand `(t,s) ↦ 1_{0<t<ρ} 1_{t<s} γ s` used for the
"min-kernel" Fubini formula `∫_{t∈(0,ρ)} ∫_{s>t} γ = ∫_{s>0} min ρ s · γ s`. -/
noncomputable def triKernel (γ : ℝ → ℝ) (ρ : ℝ) : ℝ × ℝ → ℝ :=
  fun z => if z.1 ∈ Set.Ioo (0 : ℝ) ρ ∧ z.1 < z.2 then γ z.2 else 0

/-- If `s ↦ s ^ 2 * p s` is integrable on `(0,R)` and `p` vanishes for `s ≥ R`, then
`s ↦ s ^ 2 * p s` is integrable on `(0,∞)`. -/
lemma integrableOn_sq_mul_Ioi {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * p s) (Set.Ioi 0) := by
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * p s) (Set.Ici R) := by
    refine (MeasureTheory.integrableOn_zero (s := Set.Ici R) (μ := volume)).congr_fun ?_
      measurableSet_Ici
    intro s hs
    simp only [Set.mem_Ici] at hs
    simp [hp0 s hs]
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) R ∪ Set.Ici R := by
    ext s; constructor
    · intro hs
      simp only [Set.mem_Ioi] at hs
      rcases lt_or_ge s R with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr h
    · intro hs
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici] at hs
      rcases hs with ⟨h1, _⟩ | h1
      · exact h1
      · exact lt_of_lt_of_le hR h1
  rw [hunion]
  exact hp.union h2

/-- `divsq p` is a.e. strongly measurable on `(0,∞)`. -/
lemma aestronglyMeasurable_divsq {p : ℝ → ℝ}
    (hP1 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * p s) (Set.Ioi 0)) :
    AEStronglyMeasurable (divsq p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * p s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hP1.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    measurable_inv.aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * p s * s⁻¹)
      (volume.restrict (Set.Ioi (0 : ℝ))) := h1.mul h2
  have h4 : divsq p = fun s : ℝ => s ^ 2 * p s * s⁻¹ := by
    funext s; simp [divsq, div_eq_mul_inv]
  rw [h4]; exact h3

/-- For `r > 0` the function `s ↦ min r s · divsq p s` is integrable on `(0,∞)`. -/
lemma integrable_min_mul_divsq {p : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hP1 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * p s) (Set.Ioi 0)) :
    Integrable (fun s : ℝ => min r s * divsq p s) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hγ : AEStronglyMeasurable (divsq p) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aestronglyMeasurable_divsq hP1
  refine Integrable.mono hP1 ?_ ?_
  · exact (continuous_const.min continuous_id).aestronglyMeasurable.mul hγ
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [Set.mem_Ioi] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min hr.le hs.le),
        divsq, abs_div, abs_of_pos hs]
    calc min r s * (|s ^ 2 * p s| / s) ≤ s * (|s ^ 2 * p s| / s) := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = |s ^ 2 * p s| := by field_simp

theorem OneDPotGfunUfun {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    {r : ℝ} (hr : 0 < r) :
    Gfun p r = Ufun p r / r := by
  have hP1 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * p s) (Set.Ioi 0) :=
    integrableOn_sq_mul_Ioi hR p hp hp0
  have hγ : AEStronglyMeasurable (divsq p) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aestronglyMeasurable_divsq hP1
  have hIntmin : Integrable (fun s : ℝ => min r s * divsq p s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := integrable_min_mul_divsq hr hP1
  -- The product-space integrand.
  have hT : MeasurableSet {z : ℝ × ℝ | z.1 ∈ Set.Ioo (0 : ℝ) r ∧ z.1 < z.2} := by
    measurability
  have hΦmeas : AEStronglyMeasurable (triKernel (divsq p) r)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => divsq p z.2)
        (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := hγ.comp_snd
    have heq : triKernel (divsq p) r
        = {z : ℝ × ℝ | z.1 ∈ Set.Ioo (0 : ℝ) r ∧ z.1 < z.2}.indicator
            (fun z => divsq p z.2) := by
      funext z
      simp only [triKernel, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [heq]; exact h1.indicator hT
  -- Integrability in the `t`-variable for a.e. `s`.
  have hInt1 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun t => triKernel (divsq p) r (t, s)) volume := by
    apply Filter.Eventually.of_forall
    intro s
    have hS : MeasurableSet (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) :=
      measurableSet_Ioo.inter measurableSet_Iio
    have hfin : volume (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_left)
    have hfun : (fun t => triKernel (divsq p) r (t, s))
        = (Set.Ioo (0 : ℝ) r ∩ Set.Iio s).indicator (fun _ => divsq p s) := by
      funext t
      by_cases h : t ∈ Set.Ioo (0 : ℝ) r ∧ t < s
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from ⟨h.1, h.2⟩),
            show triKernel (divsq p) r (t, s) = divsq p s from by
              simp only [triKernel]; exact if_pos h]
      · rw [Set.indicator_of_notMem
              (show t ∉ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from fun hh => h ⟨hh.1, hh.2⟩),
            show triKernel (divsq p) r (t, s) = 0 from by
              simp only [triKernel]; exact if_neg h]
    rw [hfun, integrable_indicator_iff hS]
    exact integrableOn_const hfin
  -- Integrability of the `t`-norm integral over `s`.
  have hInt2 : Integrable (fun s => ∫ t, ‖triKernel (divsq p) r (t, s)‖ ∂volume)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine hIntmin.norm.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [Set.mem_Ioi] at hs
    have hS : MeasurableSet (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) :=
      measurableSet_Ioo.inter measurableSet_Iio
    have hSreal : volume.real (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) = max (min r s) 0 := by
      rw [show Set.Ioo (0 : ℝ) r ∩ Set.Iio s = Set.Ioo 0 (min r s) from by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_min h2 h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩,
            lt_of_lt_of_le h2 (min_le_right _ _)⟩]
      rw [Real.volume_real_Ioo, sub_zero]
    have hnorm : (fun t => ‖triKernel (divsq p) r (t, s)‖)
        = (Set.Ioo (0 : ℝ) r ∩ Set.Iio s).indicator (fun _ => ‖divsq p s‖) := by
      funext t
      rw [show triKernel (divsq p) r (t, s)
            = (Set.Ioo (0 : ℝ) r ∩ Set.Iio s).indicator (fun _ => divsq p s) t from by
          by_cases h : t ∈ Set.Ioo (0 : ℝ) r ∧ t < s
          · rw [Set.indicator_of_mem (show t ∈ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from ⟨h.1, h.2⟩),
                show triKernel (divsq p) r (t, s) = divsq p s from by
                  simp only [triKernel]; exact if_pos h]
          · rw [Set.indicator_of_notMem
                  (show t ∉ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from fun hh => h ⟨hh.1, hh.2⟩),
                show triKernel (divsq p) r (t, s) = 0 from by
                  simp only [triKernel]; exact if_neg h]]
      rw [norm_indicator_eq_indicator_norm]
    rw [hnorm, MeasureTheory.integral_indicator_const ‖divsq p s‖ hS, smul_eq_mul,
        hSreal, max_eq_left (le_min hr.le hs.le)]
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (le_min hr.le hs.le)]
  have hΦ : Integrable (triKernel (divsq p) r)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    (integrable_prod_iff' hΦmeas).2 ⟨hInt1, hInt2⟩
  -- Fubini.
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun t s => triKernel (divsq p) r (t, s)) hΦ
  -- Identify the two iterated integrals.
  have hL : (∫ t, ∫ s in Set.Ioi (0 : ℝ), triKernel (divsq p) r (t, s)) = Ufun p r := by
    have hpt : ∀ t, (∫ s in Set.Ioi (0 : ℝ), triKernel (divsq p) r (t, s))
        = (Set.Ioo (0 : ℝ) r).indicator (qfun p) t := by
      intro t
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) r
      · rw [Set.indicator_of_mem ht]
        have ht0 : 0 < t := ht.1
        have hfun : ∀ s ∈ Set.Ioi (0 : ℝ),
            triKernel (divsq p) r (t, s) = (Set.Ioi t).indicator (divsq p) s := by
          intro s hs
          simp only [Set.mem_Ioi] at hs
          by_cases hts : t < s
          · rw [show triKernel (divsq p) r (t, s) = divsq p s from by
                  simp only [triKernel]; exact if_pos ⟨ht, hts⟩,
                Set.indicator_of_mem (show s ∈ Set.Ioi t from hts)]
          · rw [show triKernel (divsq p) r (t, s) = 0 from by
                  simp only [triKernel]; exact if_neg (fun h => hts h.2),
                Set.indicator_of_notMem (show s ∉ Set.Ioi t from fun h => hts h)]
        rw [setIntegral_congr_fun measurableSet_Ioi hfun,
            MeasureTheory.setIntegral_indicator measurableSet_Ioi,
            show Set.Ioi (0 : ℝ) ∩ Set.Ioi t = Set.Ioi t from by
              ext s; simp only [Set.mem_inter_iff, Set.mem_Ioi]
              exact ⟨fun h => h.2, fun h => ⟨lt_trans ht0 h, h⟩⟩]
        simp only [qfun, divsq]
      · rw [Set.indicator_of_notMem ht]
        rw [show (fun s => triKernel (divsq p) r (t, s)) = fun _ => (0 : ℝ) from by
              funext s; simp only [triKernel]; exact if_neg (fun h => ht h.1)]
        simp
    calc (∫ t, ∫ s in Set.Ioi (0 : ℝ), triKernel (divsq p) r (t, s))
        = ∫ t, (Set.Ioo (0 : ℝ) r).indicator (qfun p) t := by
          simp_rw [hpt]
      _ = Ufun p r := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioo]
          simp only [Ufun]
  have hR : (∫ s in Set.Ioi (0 : ℝ), ∫ t, triKernel (divsq p) r (t, s))
      = ∫ s in Set.Ioi (0 : ℝ), min r s * divsq p s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only [Set.mem_Ioi] at hs
    change (∫ t, triKernel (divsq p) r (t, s)) = min r s * divsq p s
    have hS : MeasurableSet (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) :=
      measurableSet_Ioo.inter measurableSet_Iio
    have hfun : (fun t => triKernel (divsq p) r (t, s))
        = (Set.Ioo (0 : ℝ) r ∩ Set.Iio s).indicator (fun _ => divsq p s) := by
      funext t
      by_cases h : t ∈ Set.Ioo (0 : ℝ) r ∧ t < s
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from ⟨h.1, h.2⟩),
            show triKernel (divsq p) r (t, s) = divsq p s from by
              simp only [triKernel]; exact if_pos h]
      · rw [Set.indicator_of_notMem
              (show t ∉ Set.Ioo (0 : ℝ) r ∩ Set.Iio s from fun hh => h ⟨hh.1, hh.2⟩),
            show triKernel (divsq p) r (t, s) = 0 from by
              simp only [triKernel]; exact if_neg h]
    rw [hfun, MeasureTheory.integral_indicator_const (divsq p s) hS, smul_eq_mul]
    have hSreal : volume.real (Set.Ioo (0 : ℝ) r ∩ Set.Iio s) = max (min r s) 0 := by
      rw [show Set.Ioo (0 : ℝ) r ∩ Set.Iio s = Set.Ioo 0 (min r s) from by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_min h2 h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩,
            lt_of_lt_of_le h2 (min_le_right _ _)⟩]
      rw [Real.volume_real_Ioo, sub_zero]
    rw [hSreal, max_eq_left (le_min hr.le hs.le)]
  have hEq : Ufun p r = ∫ s in Set.Ioi (0 : ℝ), min r s * divsq p s := by
    rw [← hL, hswap, hR]
  -- Final assembly: `min r s / r = 1 / max r s`.
  have step1 : (∫ s in Set.Ioi (0 : ℝ), min r s * divsq p s) / r
      = ∫ s in Set.Ioi (0 : ℝ), (min r s * divsq p s) / r := by
    rw [← MeasureTheory.integral_div r]
  calc Gfun p r = ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s := rfl
    _ = ∫ s in Set.Ioi (0 : ℝ), (min r s * divsq p s) / r := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro s hs
          have hs0 : 0 < s := hs
          simp only [divsq]
          rw [min_def, max_def]
          split_ifs with h <;> field_simp
    _ = (∫ s in Set.Ioi (0 : ℝ), min r s * divsq p s) / r := step1.symm
    _ = Ufun p r / r := by rw [hEq]

end Work.SmallBoxA0
