/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slice bound: `∫_θ |g θ| sinθcos²θ dθ` is controlled by the endpoint data and the
weighted `L²`-energy of `g''`.

For `g` of class `C²` on the open interval `(0, π/2)` whose second derivative satisfies
`∫_θ (g'')² · sin(2θ)^{-η} < ∞`, the weighted `L¹`-norm of `g` against the angular profile
`sinθcos²θ` is finite and bounded by an affine function of the endpoint data
`g(π/4), g'(π/4)` and of that energy.

## Proof

Taylor's formula with integral remainder at `a = π/4`,

  `g θ = g a + (θ - a) g'(a) + ∫_a^θ (θ - t) g''(t) dt`,

together with the elementary bounds `|θ - t| ≤ π/2` and `2|x| ≤ x² + 1`, gives the pointwise
estimate

  `|g θ| ≤ |g a| + (π/2)|g'(a)| + (π/2) · (E/2 + π/4)`,

where `E = ∫_θ (g'')² sin(2θ)^{-η}`.  Integrating against `sinθcos²θ`, whose total mass on
`[0, π/2]` is at most `π/2`, yields the claim.

This file is self-contained: it depends only on `Mathlib` and the two basic definition
modules of the project.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- The angular energy of `g`: `E = ∫_θ (g'')² · sin(2θ)^{-η}`. -/
def SliceEnergy (g : ℝ → ℝ) : ℝ :=
  ∫ θ in Iθ, (deriv (deriv g) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `0 ≤ sin(2θ)` on `Iθ`. -/
theorem sin_two_nonneg' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `0 ≤ sinθ cos²θ` on `Iθ`. -/
theorem sg_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  show 0 ≤ Real.sin θ * Real.cos θ ^ 2
  exact mul_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)

/-- `sinθ cos²θ ≤ 1` on `Iθ`. -/
theorem sg_le_one {θ : ℝ} (hθ : θ ∈ Iθ) : sg θ ≤ 1 := by
  show Real.sin θ * Real.cos θ ^ 2 ≤ 1
  have hs := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul hs hc (sq_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- **Taylor's formula with integral remainder** at a point `a ∈ (0,π/2)`. -/
theorem sliceTaylor {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    {a θ : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    g θ - g a - (θ - a) * deriv g a
      = ∫ t in a..θ, (θ - t) * deriv (deriv g) t := by
  have hsub : Set.uIcc a θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rcases le_total a θ with h | h
    · rw [Set.uIcc_of_le h]
      rintro x hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    · rw [Set.uIcc_of_ge h]
      rintro x hx
      exact ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 ha.2⟩
  have hd1 := hg.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)
  have hd2 := hd1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (fun t => (θ - t) * deriv (deriv g) t) (Set.uIcc a θ) :=
    ((continuousOn_const.sub continuousOn_id).mul (hd2.continuousOn.mono hsub))
  have hderiv : ∀ t ∈ Set.uIcc a θ,
      HasDerivAt (fun t => g t + (θ - t) * deriv g t) ((θ - t) * deriv (deriv g) t) t := by
    intro t ht
    have htI := hsub ht
    have h1 : HasDerivAt g (deriv g t) t :=
      (hg.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds htI.1 htI.2)
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) t) t :=
      (hd1.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds htI.1 htI.2)
    have h3 : HasDerivAt (fun t : ℝ => θ - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub θ
    have h4 : HasDerivAt (fun t => (θ - t) * deriv g t)
        (-1 * deriv g t + (θ - t) * deriv (deriv g) t) t := h3.mul h2
    have h5 := h1.add h4
    convert h5 using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hfin : (fun t : ℝ => g t + (θ - t) * deriv g t) θ
        - (fun t : ℝ => g t + (θ - t) * deriv g t) a
      = g θ - g a - (θ - a) * deriv g a := by
    show g θ + (θ - θ) * deriv g θ - (g a + (θ - a) * deriv g a)
        = g θ - g a - (θ - a) * deriv g a
    ring
  rw [hfin] at h
  exact h.symm

/-- The second derivative of a `C²` function on `(0,π/2)` is continuous there. -/
theorem sliceContDiff2 {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
  ((hg.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).deriv_of_isOpen (m := 0) isOpen_Ioo
    (by norm_num)).continuousOn

/-- On a subinterval `(u,v]` of the open quadrant the weight `sin(2θ)^{-η}` is at least `1`. -/
theorem one_le_rpow_sin {u v t : ℝ} (hu : 0 < u) (hv : v < Real.pi / 2)
    (ht : t ∈ Set.Ioc u v) : 1 ≤ (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
  have h1 : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu, ht.1]) (by linarith [ht.2, hv, Real.pi_pos])
  have h2 : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
  have h3 := Real.rpow_le_rpow_of_nonpos h1 h2
    (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at h3

/-- **Energy monotonicity.**  On a subinterval `(u,v] ⊆ (0,π/2)`, the unweighted energy
`∫_u^v (g'')²` is at most the weighted energy `SliceEnergy g` over all of `Iθ`. -/
theorem sliceEnergy_mono {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.pi / 2) :
    ∫ t in u..v, (deriv (deriv g) t) ^ 2 ≤ SliceEnergy g := by
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Icc u v) :=
    (sliceContDiff2 hg).mono fun t ht =>
      ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
  have hsinpos : ∀ t ∈ Set.Icc u v, 0 < Real.sin (2 * t) := fun t ht =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu, ht.1]) (by linarith [ht.2, hv, Real.pi_pos])
  have hcontw : ContinuousOn (fun t => (deriv (deriv g) t) ^ 2
      * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) (Set.Icc u v) :=
    (hcont2.pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun t ht => Or.inl (ne_of_gt (hsinpos t ht))))
  have huniv : IntegrableOn (fun t => (deriv (deriv g) t) ^ 2) (Set.Ioc u v) :=
    ((hcont2.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hweighted : IntegrableOn (fun t => (deriv (deriv g) t) ^ 2
      * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) (Set.Ioc u v) :=
    (hcontw.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le huv]
  calc ∫ t in Set.Ioc u v, (deriv (deriv g) t) ^ 2
      ≤ ∫ t in Set.Ioc u v, (deriv (deriv g) t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_mono_ae huniv hweighted ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
        have h1 := one_le_rpow_sin hu hv ht
        nlinarith [sq_nonneg (deriv (deriv g) t)]
    _ ≤ ∫ t in Iθ, (deriv (deriv g) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' ht) _)
        · exact Filter.Eventually.of_forall fun t ht =>
            ⟨le_of_lt (lt_trans hu ht.1), le_of_lt (lt_of_le_of_lt ht.2 hv)⟩

/-- **The `L¹`-bound for the second derivative on a subinterval.** -/
theorem sliceAbsDeriv_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.pi / 2) :
    ∫ t in u..v, |deriv (deriv g) t| ≤ SliceEnergy g / 2 + Real.pi / 4 := by
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Icc u v) :=
    (sliceContDiff2 hg).mono fun t ht =>
      ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
  have hcu : ContinuousOn (deriv (deriv g)) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]; exact hcont2
  have hI1 : IntervalIntegrable (fun t => |deriv (deriv g) t|) volume u v :=
    hcu.abs.intervalIntegrable
  have hI2 : IntervalIntegrable (fun t => (1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2) volume u v :=
    (hcu.pow 2).const_mul (1 / 2) |>.add continuousOn_const |>.intervalIntegrable
  have h1 : ∫ t in u..v, |deriv (deriv g) t|
      ≤ ∫ t in u..v, ((1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2) := by
    refine intervalIntegral.integral_mono_on huv hI1 hI2 fun t ht => ?_
    have h2 : 2 * |deriv (deriv g) t| ≤ (deriv (deriv g) t) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|deriv (deriv g) t| - 1), sq_abs (deriv (deriv g) t)]
    linarith
  have hI2a : IntervalIntegrable (fun t => (1 / 2) * (deriv (deriv g) t) ^ 2) volume u v :=
    (hcu.pow 2).const_mul (1 / 2) |>.intervalIntegrable
  have hI2b : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume u v :=
    continuousOn_const.intervalIntegrable
  have h2 : ∫ t in u..v, ((1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2)
      = (1 / 2) * (∫ t in u..v, (deriv (deriv g) t) ^ 2) + (1 / 2) * (v - u) := by
    rw [intervalIntegral.integral_add hI2a hI2b, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    ring
  have h3 : ∫ t in u..v, (deriv (deriv g) t) ^ 2 ≤ SliceEnergy g :=
    sliceEnergy_mono hg hE hu huv hv
  have h4 : v - u ≤ Real.pi / 2 := by linarith [hu, hv]
  rw [h2] at h1
  have h5 : (1 / 2) * (∫ t in u..v, (deriv (deriv g) t) ^ 2) + (1 / 2) * (v - u)
      ≤ SliceEnergy g / 2 + Real.pi / 4 := by
    have h6 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 1 / 2)
    have h7 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith
  linarith [h1, h5]

/-- The remainder estimate: the integral defining the Taylor remainder is bounded by
`(π/2) (E/2 + π/4)` in either order. -/
theorem sliceRemainder_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {a θ : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |∫ t in a..θ, (θ - t) * deriv (deriv g) t|
      ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
  have hstep : ∀ u v : ℝ, 0 < u → u ≤ v → v < Real.pi / 2 →
      ∫ t in Set.Ioc u v, |(θ - t) * deriv (deriv g) t|
        ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
    intro u v hu huv hv
    have hcu : ContinuousOn (deriv (deriv g)) (Set.uIcc u v) := by
      rw [Set.uIcc_of_le huv]
      exact (sliceContDiff2 hg).mono fun t ht =>
        ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
    calc ∫ t in Set.Ioc u v, |(θ - t) * deriv (deriv g) t|
        = ∫ t in Set.Ioc u v, |θ - t| * |deriv (deriv g) t| := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
          rw [abs_mul]
      _ = ∫ t in u..v, |θ - t| * |deriv (deriv g) t| :=
          (intervalIntegral.integral_of_le huv).symm
      _ ≤ ∫ t in u..v, (Real.pi / 2) * |deriv (deriv g) t| := by
          refine intervalIntegral.integral_mono_on huv ?_ ?_ fun t ht => ?_
          · exact (((continuousOn_const.sub continuousOn_id).abs).mul hcu.abs).intervalIntegrable
          · exact (continuousOn_const.mul hcu.abs).intervalIntegrable
          · have ht' : t ∈ Set.Icc 0 (Real.pi / 2) :=
              ⟨by linarith [hu, ht.1], by linarith [ht.2, hv, Real.pi_pos]⟩
            have hb : |θ - t| ≤ Real.pi / 2 := by
              rw [abs_sub_le_iff]
              exact ⟨by linarith [ht'.1, hθ.2, Real.pi_pos],
                by linarith [ht'.2, hθ.1, Real.pi_pos]⟩
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = Real.pi / 2 * ∫ t in u..v, |deriv (deriv g) t| :=
          intervalIntegral.integral_const_mul (Real.pi / 2) _
      _ ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) :=
          mul_le_mul_of_nonneg_left (sliceAbsDeriv_le hg hE hu huv hv)
            (by linarith [Real.pi_pos])
  rcases le_total a θ with h | h
  · rw [intervalIntegral.integral_of_le h]
    refine le_trans ?_ (hstep a θ ha.1 h hθ.2)
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a θ))
        (f := fun t => (θ - t) * deriv (deriv g) t))
  · rw [intervalIntegral.integral_of_ge h]
    have h1 : |∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t|
        ≤ ∫ t in Set.Ioc θ a, |(θ - t) * deriv (deriv g) t| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc θ a))
          (f := fun t => (θ - t) * deriv (deriv g) t))
    calc |-(∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t)|
        = |∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t| := by rw [abs_neg]
      _ ≤ ∫ t in Set.Ioc θ a, |(θ - t) * deriv (deriv g) t| := h1
      _ ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := hstep θ a hθ.1 h ha.2

/-- **The pointwise slice estimate.** -/
theorem sliceAbs_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |g θ| ≤ |g (Real.pi / 4)| + Real.pi / 2 * |deriv g (Real.pi / 4)|
      + Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
  have ha : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hT := sliceTaylor hg ha hθ
  have hT' : g θ = g (Real.pi / 4) + (θ - Real.pi / 4) * deriv g (Real.pi / 4)
      + ∫ t in Real.pi / 4..θ, (θ - t) * deriv (deriv g) t := by linarith [hT]
  have h1 : |g θ| ≤ |g (Real.pi / 4)| + |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
      + |∫ t in Real.pi / 4..θ, (θ - t) * deriv (deriv g) t| := by
    rw [hT']
    exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  have h2 : |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
      ≤ Real.pi / 2 * |deriv g (Real.pi / 4)| := by
    rw [abs_mul]
    have hb : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      have hb' : |θ - Real.pi / 4| < Real.pi / 4 := by
        rw [abs_lt]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      linarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have h3 := sliceRemainder_le hg hE ha hθ
  linarith [h1, h2, h3]

/-- The energy is nonnegative under the integrability hypothesis. -/
theorem SliceEnergy_nonneg {g : ℝ → ℝ}
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) : 0 ≤ SliceEnergy g := by
  rw [SliceEnergy]
  exact integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)))

/-- **The `θ`-slice bound.**  For `g` of class `C²` on `(0,π/2)` with finite weighted energy,
`θ ↦ g θ · sinθcos²θ` is integrable on `Iθ`, and
`∫_θ |g θ| sinθcos²θ dθ ≤ 4 + 4|g(π/4)| + 4|g'(π/4)| + 2 E` with
`E = ∫_θ (g'')² sin(2θ)^{-η}`. -/
theorem sliceMomentLinear {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) :
    IntegrableOn (fun θ => g θ * sg θ) Iθ ∧
      ∫ θ in Iθ, |g θ| * sg θ ≤ 4 + 4 * |g (Real.pi / 4)| + 4 * |deriv g (Real.pi / 4)|
        + 2 * SliceEnergy g := by
  have hσcont : Continuous sg := by unfold Work.Elliptic.sinCos2; fun_prop
  have hσint : IntegrableOn sg Iθ :=
    hσcont.continuousOn.integrableOn_compact isCompact_Icc
  -- the `θ`-mass of `Iθ` is `π/2`
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : ∫ θ in Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    simp
  have hσmass : ∫ θ in Iθ, sg θ ≤ Real.pi / 2 := by
    rw [← hvol]
    exact MeasureTheory.integral_mono_ae hσint hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => sg_le_one hθ))
  -- almost everywhere interior on `Iθ`
  have hae : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      rw [Set.mem_setOf_eq] at hθ
      push_neg at hθ
      obtain ⟨hmem, hnot⟩ := hθ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases h0 : θ = 0
      · exact Or.inl h0
      · refine Or.inr ?_
        by_contra hpi
        exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hpi⟩
    · have hset : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      rw [hset]
      exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton _)
  set E := SliceEnergy g with hEdef
  set A := |g (Real.pi / 4)| with hAdef
  set B := |deriv g (Real.pi / 4)| with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hB0 : 0 ≤ B := by rw [hBdef]; exact abs_nonneg _
  have hE0 : 0 ≤ E := SliceEnergy_nonneg hE
  -- the pointwise estimate, and its `sg`-weighted version
  have hbound : ∀ᵐ θ ∂(volume.restrict Iθ),
      |g θ| ≤ A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4) := by
    filter_upwards [hae] with θ hθ
    simpa only [hAdef, hBdef, hEdef] using sliceAbs_le hg hE hθ
  have hbounded : ∀ᵐ θ ∂(volume.restrict Iθ),
      ‖g θ * sg θ‖ ≤ (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ := by
    filter_upwards [hbound, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
      with θ hb hm
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sg_nonneg hm)]
    exact mul_le_mul_of_nonneg_right hb (sg_nonneg hm)
  have hC : IntegrableOn
      (fun θ : ℝ => (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ) Iθ :=
    hσint.const_mul _
  have hmeas : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      ((MeasureTheory.Ioo_ae_eq_Icc' (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton _)).symm)
  have haesm : AEStronglyMeasurable (fun θ => g θ * sg θ) (volume.restrict Iθ) := by
    rw [hmeas]
    exact (hg.continuousOn.mul hσcont.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hsl : IntegrableOn (fun θ => g θ * sg θ) Iθ :=
    Integrable.mono' hC haesm hbounded
  refine ⟨hsl, ?_⟩
  have hsl' : Integrable (fun θ => |g θ| * sg θ) (volume.restrict Iθ) :=
    hsl.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hm => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sg_nonneg hm)]))
  have hmono : ∫ θ in Iθ, |g θ| * sg θ
      ≤ ∫ θ in Iθ, (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ :=
    MeasureTheory.integral_mono_ae hsl' hC
      (by filter_upwards [hbound, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
            with θ hb hm
          exact mul_le_mul_of_nonneg_right hb (sg_nonneg hm))
  rw [MeasureTheory.integral_const_mul] at hmono
  have hC0 : 0 ≤ A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4) := by positivity
  have hmm : (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (∫ θ in Iθ, sg θ)
      ≤ (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left hσmass hC0
  have hexp : (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (Real.pi / 2)
      = (Real.pi / 2) * A + (Real.pi ^ 2 / 4) * B + (Real.pi ^ 2 / 8) * E + Real.pi ^ 3 / 16 := by
    ring
  have h1 : (Real.pi / 2) * A ≤ 4 * A := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    linarith [Real.pi_lt_four]
  have h2 : (Real.pi ^ 2 / 4) * B ≤ 4 * B := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h3 : (Real.pi ^ 2 / 8) * E ≤ 2 * E := by
    refine mul_le_mul_of_nonneg_right ?_ hE0
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h4 : Real.pi ^ 3 / 16 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  rw [hexp] at hmm
  rw [hAdef, hBdef, hEdef]
  linarith [hmono, hmm, h1, h2, h3, h4]

end Work.FTS.EllipticEst.H2W
