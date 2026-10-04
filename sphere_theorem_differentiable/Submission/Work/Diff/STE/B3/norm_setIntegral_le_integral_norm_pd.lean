import Mathlib
import Submission.Work.Diff.STE.cube_fubini

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The mean of a function vanishing on a hyperplane is controlled by its derivative

For a `C¹` function `P : (ι → ℝ) → ℂ` which vanishes on the hyperplane `{z | z i = 1/2}` we
prove

`‖∫_{unitCube} P‖ ^ 2 ≤ ∫_{unitCube} ‖∂ᵢ P‖ ^ 2`,

where `unitCube = (0,1]^ι` and `∂ᵢ P = pd i P` is the partial derivative in the `i`-th
coordinate.

## Route

* `nsipd_norm_le_integral_norm_of_hasDerivAt`: the one dimensional fundamental theorem bound.  For
  `f : ℝ → ℂ` with derivative `f'` and `f (1/2) = 0`, the pointwise bound
  `‖f t‖ ≤ ∫_{s ∈ (0,1]} ‖f' s‖` for `t ∈ (0,1]` (the subinterval between `t` and `1/2` lies in
  `(0,1]`, and the integrand is nonnegative).
* `nsipd_slice_integral_norm_le`: applying this to the slice `t ↦ P (insertAt i t y)` gives, for
  every fixed `y`, `∫_{(0,1]} ‖P (insertAt i · y)‖ ≤ ∫_{(0,1]} ‖pd i P (insertAt i · y)‖`.
* `nsipd_setIntegral_unitCube_eq_integral_prod`: Fubini for the unit cube (`cube_fubini` with `ℂ`
  replaced by `ℝ`): the integral over the cube is the iterated integral over the remaining
  coordinates and the `i`-th one.
* `nsipd_integrable_comp_insertAt` together with `Integrable.integral_norm_prod_left` gives the
  integrability of the slice integrals, so that the pointwise slice inequality can be integrated.
* `nsipd_integral_le_sqrt_integral_sq`: Cauchy–Schwarz on the unit cube, which has volume `1`:
  `∫ F ≤ √(∫ F²)` for `F ≥ 0`.

Combining `‖∫ P‖ ≤ ∫ ‖P‖ ≤ ∫ ‖∂ᵢ P‖ ≤ √(∫ ‖∂ᵢ P‖²)` with `Real.sq_sqrt` gives the claim.
-/

noncomputable section

open MeasureTheory BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary measure facts for the unit cube -/

lemma nsipd_measSet_unitCube : MeasurableSet (unitCube (ι := ι)) := by
  rw [unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

lemma nsipd_cube_subset_closedCube :
    unitCube (ι := ι) ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
  exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩

lemma nsipd_vol_unitCube : (volume : Measure (ι → ℝ)) (unitCube (ι := ι)) = 1 := by
  rw [unitCube, Real.volume_pi_Ioc]
  simp

/-- A continuous real valued function is integrable on the (bounded) unit cube. -/
lemma nsipd_integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (unitCube (ι := ι))) :=
  (hF.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    nsipd_cube_subset_closedCube

/-! ## Cauchy–Schwarz on the unit cube -/

/-- **Cauchy–Schwarz on the unit cube.** Since `unitCube` has volume `1`, the mean of a
nonnegative continuous function is at most the square root of the mean of its square. -/
lemma nsipd_integral_le_sqrt_integral_sq (F : (ι → ℝ) → ℝ) (hF : Continuous F)
    (hFnn : ∀ x, 0 ≤ F x) :
    ∫ x in unitCube (ι := ι), F x
      ≤ Real.sqrt (∫ x in unitCube (ι := ι), F x ^ 2) := by
  have hvol := nsipd_vol_unitCube (ι := ι)
  haveI : IsFiniteMeasure (volume.restrict (unitCube (ι := ι))) :=
    isFiniteMeasure_restrict.2 (by rw [hvol]; exact ENNReal.one_ne_top)
  have hInt2 : Integrable (fun x : ι → ℝ => F x ^ 2)
      (volume.restrict (unitCube (ι := ι))) := by
    have h : Integrable (fun x : ι → ℝ => ‖F x‖ ^ 2)
        (volume.restrict (unitCube (ι := ι))) :=
      (hF.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_univ_pi fun _ => isCompact_Icc) |>.mono_set nsipd_cube_subset_closedCube
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖F x‖ ^ 2 = F x ^ 2
    rw [Real.norm_of_nonneg (hFnn x)]
  have hLpF : MemLp F 2 (volume.restrict (unitCube (ι := ι))) :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable.restrict).mpr hInt2
  have hLp1 : MemLp (fun _ : ι → ℝ => (1 : ℝ)) 2
      (volume.restrict (unitCube (ι := ι))) := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (unitCube (ι := ι)))
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hFnn) (Filter.Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hLpF) (by simpa using hLp1)
  have hone : (∫ x : ι → ℝ, (1 : ℝ) ^ (2 : ℝ)
      ∂(volume.restrict (unitCube (ι := ι)))) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => Real.one_rpow (2 : ℝ))]
    rw [integral_const, Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_one,
      one_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => mul_one (F x)), hone,
    Real.one_rpow, mul_one] at h
  simp only [Real.rpow_two] at h
  rwa [← Real.sqrt_eq_rpow] at h

/-! ## The one dimensional fundamental theorem bound -/

/-- **Fundamental theorem bound.** If `f` has derivative `f'` everywhere and `f (1/2) = 0`, then
for `t ∈ (0,1]` the value `‖f t‖` is bounded by the integral of `‖f'‖` over `(0,1]`. -/
lemma nsipd_norm_le_integral_norm_of_hasDerivAt {f f' : ℝ → ℂ}
    (hderiv : ∀ s, HasDerivAt f (f' s) s) (hcont : Continuous f')
    {t : ℝ} (ht : t ∈ Set.Ioc (0:ℝ) 1) (hz : f (1/2) = 0) :
    ‖f t‖ ≤ ∫ s in Set.Ioc (0:ℝ) 1, ‖f' s‖ := by
  have hIntOn : IntegrableOn (fun s => ‖f' s‖) (Set.Ioc (0:ℝ) 1) volume :=
    (hcont.norm.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] (fun s => ‖f' s‖) :=
    Filter.Eventually.of_forall fun s => norm_nonneg _
  rcases le_total t (1/2) with h | h
  · have hFTC : ∫ s in t..(1/2), f' s = f (1/2) - f t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
        (hcont.intervalIntegrable t (1/2))
    have h1 : ‖f t‖ ≤ ∫ s in t..(1/2), ‖f' s‖ := by
      have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f')
        (a := t) (b := (1/2:ℝ)) h
      rwa [hFTC, hz, zero_sub, norm_neg] at h2
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le h]
    refine setIntegral_mono_set hIntOn hnn ?_
    refine Filter.Eventually.of_forall fun s hs => ?_
    exact ⟨lt_trans (Set.mem_Ioc.mp ht).1 hs.1, le_trans hs.2 (by norm_num)⟩
  · have hFTC : ∫ s in (1/2)..t, f' s = f t - f (1/2) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
        (hcont.intervalIntegrable (1/2) t)
    have h1 : ‖f t‖ ≤ ∫ s in (1/2)..t, ‖f' s‖ := by
      have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f')
        (a := (1/2:ℝ)) (b := t) h
      rwa [hFTC, hz, sub_zero] at h2
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le h]
    refine setIntegral_mono_set hIntOn hnn ?_
    refine Filter.Eventually.of_forall fun s hs => ?_
    exact ⟨lt_trans (by norm_num : (0:ℝ) < 1/2) hs.1, le_trans hs.2 (Set.mem_Ioc.mp ht).2⟩

/-! ## The slice bound -/

/-- **Slice bound.** For every fixed complement `y` of the `i`-th coordinate, the integral of
`‖P‖` over the `i`-th coordinate is bounded by that of `‖∂ᵢ P‖`. -/
lemma nsipd_slice_integral_norm_le (i : ι) {P : (ι → ℝ) → ℂ} (hP : ContDiff ℝ 1 P)
    (hzero : ∀ z : ι → ℝ, z i = (1 / 2 : ℝ) → P z = 0)
    (y : {j : ι // j ≠ i} → ℝ) :
    ∫ t in Set.Ioc (0:ℝ) 1, ‖P (insertAt i t y)‖
      ≤ ∫ t in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i t y)‖ := by
  have hcont : Continuous (fun s : ℝ => pd i P (insertAt i s y)) := by
    have hc : Continuous (pd i P) := by
      change Continuous (fun x : ι → ℝ => fderiv ℝ P x (Pi.single i 1))
      exact (hP.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hi : Continuous (fun s : ℝ => insertAt i s y) := by
      have he : (fun s : ℝ => insertAt i s y)
          = fun s : ℝ => insertAt i 0 y + s • (Pi.single i 1 : ι → ℝ) := by
        funext s; simpa using insertAt_add i 0 s y
      rw [he]
      exact (continuous_id.smul continuous_const).const_add _
    exact hc.comp hi
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => P (insertAt i s y))
      (pd i P (insertAt i s y)) s := by
    intro s
    have hdiff : Differentiable ℝ P := hP.differentiable (by norm_num)
    have h1 := (hdiff (insertAt i s y)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt s (hasDerivAt_insertAt i y s)
    have h3 : HasDerivAt (fun s : ℝ => P (insertAt i s y))
        ((fderiv ℝ P (insertAt i s y)) (Pi.single i 1)) s := h2
    simpa [pd] using h3
  have huniv : unitIoc Set.univ = 1 := by
    rw [unitIoc, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hfin : IsFiniteMeasure unitIoc := ⟨by rw [huniv]; exact ENNReal.one_lt_top⟩
  have hae : (fun t : ℝ => ‖P (insertAt i t y)‖)
      ≤ᵐ[unitIoc] (fun _ : ℝ => ∫ s in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i s y)‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact nsipd_norm_le_integral_norm_of_hasDerivAt hderiv hcont ht
      (hzero _ (insertAt_self i (1/2) y))
  have hIntc : Integrable (fun _ : ℝ => ∫ s in Set.Ioc (0:ℝ) 1,
      ‖pd i P (insertAt i s y)‖) unitIoc :=
    (integrable_const_iff (c := ∫ s in Set.Ioc (0:ℝ) 1,
      ‖pd i P (insertAt i s y)‖)).mpr (Or.inr hfin)
  have hmain := integral_mono_of_nonneg (μ := unitIoc)
      (Filter.Eventually.of_forall fun t => norm_nonneg _) hIntc hae
  have hconst : ∫ _t : ℝ, (∫ s in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i s y)‖) ∂unitIoc
      = ∫ s in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i s y)‖ := by
    rw [integral_const, Measure.real, huniv, ENNReal.toReal_one, one_smul]
  calc ∫ t in Set.Ioc (0:ℝ) 1, ‖P (insertAt i t y)‖
      = ∫ t, ‖P (insertAt i t y)‖ ∂unitIoc := rfl
    _ ≤ ∫ t, (∫ s in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i s y)‖) ∂unitIoc := hmain
    _ = ∫ s in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i s y)‖ := hconst
    _ = ∫ t in Set.Ioc (0:ℝ) 1, ‖pd i P (insertAt i t y)‖ := rfl

/-! ## Fubini for the unit cube, real valued -/

/-- **Fubini for the unit cube.** The integral over `(0,1]^ι` is the iterated integral over the
remaining coordinates and the `i`-th one. -/
lemma nsipd_setIntegral_unitCube_eq_integral_prod (i : ι) (F : (ι → ℝ) → ℝ)
    (hF : Continuous F) :
    ∫ x in unitCube (ι := ι), F x
      = ∫ y : {j : ι // j ≠ i} → ℝ,
          ∫ t : ℝ, F (insertAt i t y) ∂unitIoc
        ∂(Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc) := by
  have hIntμ : Integrable F (Measure.pi fun _ : ι => unitIoc) := by
    have h1 : Integrable F (volume.restrict (unitCube (ι := ι))) :=
      nsipd_integrableOn_unitCube_of_continuous_real hF
    rwa [restrict_unitCube_measure] at h1
  have hIntΦ : Integrable (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => F (insertAt i p.2 p.1))
      (Measure.prod (Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc) unitIoc) :=
    (measurePreserving_insertAt i).integrable_comp_of_integrable hIntμ
  have hL : (∫ x in unitCube (ι := ι), F x)
      = ∫ x, F x ∂(Measure.pi fun _ : ι => unitIoc) := by
    rw [restrict_unitCube_measure]
  rw [hL, ← (measurePreserving_insertAt i).map_eq,
    integral_map (measurable_insertAt_pair i).aemeasurable hF.aestronglyMeasurable,
    integral_prod _ hIntΦ]

/-- **Integrability of the composed integrand.** For a continuous `F`, the function
`(y,t) ↦ F (insertAt i t y)` is integrable for the product of the measures on the complement of
the `i`-th coordinate and on the `i`-th coordinate. -/
lemma nsipd_integrable_comp_insertAt (i : ι) {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable (fun p : ({j : ι // j ≠ i} → ℝ) × ℝ => F (insertAt i p.2 p.1))
      (Measure.prod (Measure.pi fun _ : {j : ι // j ≠ i} => unitIoc) unitIoc) := by
  have h1 : Integrable F (volume.restrict (unitCube (ι := ι))) :=
    nsipd_integrableOn_unitCube_of_continuous_real hF
  rw [restrict_unitCube_measure] at h1
  exact (measurePreserving_insertAt i).integrable_comp_of_integrable h1

/-! ## The target theorem -/

theorem norm_setIntegral_le_integral_norm_pd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {P : (ι → ℝ) → ℂ} (hP : ContDiff ℝ 1 P)
    (hzero : ∀ z : ι → ℝ, z i = (1 / 2 : ℝ) → P z = 0) :
    ‖∫ x in Work.Diff.STE.unitCube (ι := ι), P x‖ ^ 2
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2 := by
  have hPc : Continuous P := (hP.differentiable (by norm_num)).continuous
  have hPdc : Continuous (Work.Diff.STE.pd i P) := by
    change Continuous (fun x : ι → ℝ => fderiv ℝ P x (Pi.single i 1))
    exact (hP.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- the norm of the integral is bounded by the integral of the norm
  have hstep1 : ‖∫ x in Work.Diff.STE.unitCube (ι := ι), P x‖
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖P x‖ :=
    norm_integral_le_integral_norm
      (μ := (volume : Measure (ι → ℝ)).restrict (Work.Diff.STE.unitCube (ι := ι))) P
  -- integrability of the slice integrals
  have hintP : Integrable (fun y : {j : ι // j ≠ i} → ℝ =>
      ∫ t : ℝ, ‖P (Work.Diff.STE.insertAt i t y)‖ ∂Work.Diff.STE.unitIoc)
      (Measure.pi fun _ : {j : ι // j ≠ i} => Work.Diff.STE.unitIoc) :=
    ((nsipd_integrable_comp_insertAt i hPc.norm).integral_norm_prod_left).congr
      (Filter.Eventually.of_forall fun y => integral_congr_ae
        (Filter.Eventually.of_forall fun t => Real.norm_of_nonneg (norm_nonneg _)))
  have hintD : Integrable (fun y : {j : ι // j ≠ i} → ℝ =>
      ∫ t : ℝ, ‖Work.Diff.STE.pd i P (Work.Diff.STE.insertAt i t y)‖ ∂Work.Diff.STE.unitIoc)
      (Measure.pi fun _ : {j : ι // j ≠ i} => Work.Diff.STE.unitIoc) :=
    ((nsipd_integrable_comp_insertAt i hPdc.norm).integral_norm_prod_left).congr
      (Filter.Eventually.of_forall fun y => integral_congr_ae
        (Filter.Eventually.of_forall fun t => Real.norm_of_nonneg (norm_nonneg _)))
  -- Fubini and the slice bound
  have hstep2 : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖P x‖
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ := by
    have hleft := nsipd_setIntegral_unitCube_eq_integral_prod i (fun x => ‖P x‖) hPc.norm
    have hright := nsipd_setIntegral_unitCube_eq_integral_prod i
      (fun x => ‖Work.Diff.STE.pd i P x‖) hPdc.norm
    have hmono : (∫ y : {j : ι // j ≠ i} → ℝ,
          ∫ t : ℝ, ‖P (Work.Diff.STE.insertAt i t y)‖ ∂Work.Diff.STE.unitIoc
        ∂(Measure.pi fun _ : {j : ι // j ≠ i} => Work.Diff.STE.unitIoc))
        ≤ (∫ y : {j : ι // j ≠ i} → ℝ,
          ∫ t : ℝ, ‖Work.Diff.STE.pd i P (Work.Diff.STE.insertAt i t y)‖
            ∂Work.Diff.STE.unitIoc
        ∂(Measure.pi fun _ : {j : ι // j ≠ i} => Work.Diff.STE.unitIoc)) :=
      integral_mono hintP hintD (fun y => nsipd_slice_integral_norm_le i hP hzero y)
    calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖P x‖
        = ∫ y : {j : ι // j ≠ i} → ℝ,
              ∫ t : ℝ, ‖P (Work.Diff.STE.insertAt i t y)‖ ∂Work.Diff.STE.unitIoc
            ∂(Measure.pi fun _ : {j : ι // j ≠ i} => Work.Diff.STE.unitIoc) := hleft
      _ ≤ _ := hmono
      _ = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ := hright.symm
  -- Cauchy–Schwarz
  have hstep3 : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖
      ≤ Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2) :=
    nsipd_integral_le_sqrt_integral_sq (fun x => ‖Work.Diff.STE.pd i P x‖) hPdc.norm
      (fun x => norm_nonneg _)
  have hfinal : ‖∫ x in Work.Diff.STE.unitCube (ι := ι), P x‖
      ≤ Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2) :=
    hstep1.trans (hstep2.trans hstep3)
  have hsq : (Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pd i P x‖ ^ 2)) ^ 2
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2 :=
    Real.sq_sqrt (integral_nonneg fun x => by positivity)
  calc ‖∫ x in Work.Diff.STE.unitCube (ι := ι), P x‖ ^ 2
      ≤ (Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pd i P x‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hfinal 2
    _ = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i P x‖ ^ 2 := hsq

end Work.Diff.STE.B3
