import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow
import Submission.Work.FTS.EllipticEst.remov.integral_sub_rpow_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The substitution `h = u' - tan θ · u`

Everything below is proved from scratch; the only inputs are `ContDiffOn` of `u` and the three
`L²` statements among the target theorem's hypotheses. -/

/-- The substitution `h θ = deriv u θ - tan θ · u θ` of the endpoint analysis: `h` is the
first-order quantity made `L²` by `Lzero1`. -/
def hslice (u : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv u θ - Real.tan θ * u θ

/-- `hsliceDeriv u = -(Lzero1 u) - 6 u` is the derivative of `hslice u`:
`h' = u'' - (tan θ · u)'` and `Lzero1 u = -u'' + (tan θ · u)' - 6u`. -/
def hsliceDeriv (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(Work.FTS.EllipticEst.Lzero1 u θ) - 6 * u θ

/-- `hslice u` is `C¹` on the strip and its derivative is `hsliceDeriv u`. -/
theorem hslice_deriv_eq {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (hslice u) (Set.Ioo 0 (Real.pi / 2)) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (hslice u) θ = hsliceDeriv u θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, hpi], hx.2⟩)
  have hdu : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have htan : ContDiffOn ℝ 1 Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hx)]
    exact Real.contDiffAt_tan.2 (hcos x hx)
  constructor
  · show ContDiffOn ℝ 1 (fun t => deriv u t - Real.tan t * u t) (Set.Ioo 0 (Real.pi / 2))
    exact hdu.sub (htan.mul (hu.of_le (by norm_num)))
  · intro θ hθ
    have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hdu' : DifferentiableAt ℝ (deriv u) θ :=
      (hdu.differentiableOn (by norm_num)).differentiableAt hnhds
    have hu' : DifferentiableAt ℝ u θ :=
      (hu.differentiableOn (by norm_num)).differentiableAt hnhds
    have htan' : DifferentiableAt ℝ Real.tan θ :=
      (Real.hasDerivAt_tan (hcos θ hθ)).differentiableAt
    have h1 : deriv (fun t => deriv u t - Real.tan t * u t) θ
        = deriv (fun t => deriv u t) θ - deriv (fun t => Real.tan t * u t) θ :=
      deriv_sub hdu' (htan'.mul hu')
    have h2 : hsliceDeriv u θ
        = deriv (fun t => deriv u t) θ - deriv (fun t => Real.tan t * u t) θ := by
      simp only [hsliceDeriv, Work.FTS.EllipticEst.Lzero1]
      ring
    exact h1.trans h2.symm

/-- Near `π/2` the tangent dominates `1 / (2 (π/2 - θ))`: `cos θ = sin (π/2 - θ) ≤ π/2 - θ`
and `sin θ ≥ 1/2` for `θ ≥ π/4`. -/
theorem inv_two_mul_pi_div_two_sub_le_tan {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    1 / (2 * (Real.pi / 2 - θ)) ≤ Real.tan θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
  have hsin : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθle
    have h2 : (1 : ℝ) / 2 ≤ 2 / Real.pi * θ := by
      have h3 : 2 / Real.pi * (Real.pi / 4) ≤ 2 / Real.pi * θ :=
        mul_le_mul_of_nonneg_left hθ.1.le (by positivity)
      have h4 : 2 / Real.pi * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith
    linarith
  have hcos_le : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h : Real.sin (Real.pi / 2 - θ) < Real.pi / 2 - θ :=
      Real.sin_lt (by linarith [hθ.2])
    rw [Real.sin_pi_div_two_sub] at h
    exact le_of_lt h
  have h1 : 1 / (2 * (Real.pi / 2 - θ)) ≤ 1 / (2 * Real.cos θ) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith
  have h2 : 1 / (2 * Real.cos θ) ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ (by positivity) hcos]
    nlinarith [hsin, hcos]
  linarith

/-- The antiderivative of `θ ↦ (π/2 - θ)⁻²` is `θ ↦ (π/2 - θ)⁻¹`. -/
theorem integral_pi_div_two_sub_inv_sq (a b : ℝ) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ θ in a..b, ((Real.pi / 2 - θ)⁻¹) ^ 2 = (Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹ := by
  have hcongr : Set.EqOn (fun θ : ℝ => ((Real.pi / 2 - θ)⁻¹) ^ 2)
      (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-2 : ℝ)) (Set.uIcc a b) := by
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    have hθb : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hb
    have hle : 0 ≤ Real.pi / 2 - θ := by linarith
    change ((Real.pi / 2 - θ)⁻¹) ^ 2 = (Real.pi / 2 - θ) ^ (-2 : ℝ)
    have h2 : (Real.pi / 2 - θ) ^ (-2 : ℝ) = ((Real.pi / 2 - θ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hle (2 : ℝ), Real.rpow_two]
    rw [h2, inv_pow]
  rw [intervalIntegral.integral_congr hcongr,
    Work.FTS.EllipticEst.remov.integral_sub_rpow_neg (b := Real.pi / 2) (p := 2) (t := b) (θ := a)
      hab hb (by norm_num : (1 : ℝ) < 2)]
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, div_one]
  simp only [Real.rpow_neg_one]

/-- A non-zero limit at `π/2` from the left keeps `|u|` away from `0` on a left neighbourhood. -/
theorem abs_lower_of_tendsto_nhdsWithin {u : ℝ → ℝ} {ν : ℝ} (hν : ν ≠ 0)
    (hlim : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ν)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |ν| / 2 ≤ |u θ| := by
  have hνpos : 0 < |ν| := abs_pos.mpr hν
  have hε : 0 < |ν| / 2 := by linarith
  have h1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |u θ - ν| < |ν| / 2 := by
    have h2 := Metric.tendsto_nhds.mp hlim (|ν| / 2) hε
    filter_upwards [h2] with θ hθ
    rwa [Real.dist_eq] at hθ
  rw [eventually_nhdsWithin_iff] at h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδpos, hδ⟩ := h1
  refine ⟨δ, hδpos, fun θ hθ => ?_⟩
  have hdist : dist θ (Real.pi / 2) < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith [hθ.2])]
    linarith [hθ.1]
  have hlt : |u θ - ν| < |ν| / 2 := hδ hdist hθ.2
  have h2 : |ν| ≤ |u θ| + |ν - u θ| := by
    calc |ν| = |u θ + (ν - u θ)| := by ring_nf
      _ ≤ |u θ| + |ν - u θ| := abs_add_le _ _
  rw [abs_sub_comm] at h2
  linarith

/-- `hslice u` is bounded on a left neighbourhood of `π/2`.  The derivative
`hsliceDeriv u = -(Lzero1 u) - 6u` is square-integrable on `Iθ` by hypothesis, so it is
integrable, and the fundamental theorem of calculus together with `|z| ≤ (1 + z²)/2` bounds the
increment of `hslice u` uniformly. -/
theorem hslice_bdd_near_pi_div_two {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) Work.Spaces.Iθ) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ δ < Real.pi / 2 ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |hslice u θ| ≤ M := by
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨hHC1, hHeq⟩ := hslice_deriv_eq hu
  -- the dominating function
  set G : ℝ → ℝ := fun t => 7 / 2 + (1 / 2) * (Work.FTS.EllipticEst.Lzero1 u t) ^ 2
    + 3 * (u t) ^ 2 with hGdef
  have hGnn : ∀ t : ℝ, 0 ≤ G t := by
    intro t
    rw [hGdef]
    have h1 : 0 ≤ (Work.FTS.EllipticEst.Lzero1 u t) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (u t) ^ 2 := sq_nonneg _
    linarith
  have hIθfin : (volume : MeasureTheory.Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iθ := by
    rw [hGdef]
    exact ((MeasureTheory.integrableOn_const hIθfin).add (hg.const_mul (1 / 2))).add
      (hu0.const_mul 3)
  have hdom : ∀ t : ℝ, |hsliceDeriv u t| ≤ G t := by
    intro t
    have h1 : |Work.FTS.EllipticEst.Lzero1 u t|
        ≤ (1 + (Work.FTS.EllipticEst.Lzero1 u t) ^ 2) / 2 := by
      nlinarith [abs_nonneg (Work.FTS.EllipticEst.Lzero1 u t),
        sq_abs (Work.FTS.EllipticEst.Lzero1 u t),
        sq_nonneg (|Work.FTS.EllipticEst.Lzero1 u t| - 1)]
    have h2 : |u t| ≤ (1 + (u t) ^ 2) / 2 := by
      nlinarith [abs_nonneg (u t), sq_abs (u t), sq_nonneg (|u t| - 1)]
    have h3 : |-(Work.FTS.EllipticEst.Lzero1 u t) - 6 * u t|
        ≤ |Work.FTS.EllipticEst.Lzero1 u t| + 6 * |u t| := by
      have h6 : |(6 : ℝ) * u t| = 6 * |u t| := by rw [abs_mul]; norm_num
      have h := abs_add_le (-(Work.FTS.EllipticEst.Lzero1 u t)) (-(6 * u t))
      rw [abs_neg, abs_neg, h6] at h
      exact h
    rw [hGdef]
    simp only [hsliceDeriv]
    linarith
  set K : ℝ := ∫ t in Work.Spaces.Iθ, G t with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact MeasureTheory.integral_nonneg hGnn
  set θ₀ : ℝ := 3 * Real.pi / 8 with hθ₀def
  have hθ₀mem : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hθ₀def]
    exact ⟨by linarith [hpi], by linarith [hpi]⟩
  have hderivH : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (hslice u) (hsliceDeriv u x) x := by
    intro x hx
    have hd : DifferentiableAt ℝ (hslice u) x :=
      (hHC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)
    have h1 : HasDerivAt (hslice u) (deriv (hslice u) x) x := hd.hasDerivAt
    rw [hHeq x hx] at h1
    exact h1
  refine ⟨|hslice u θ₀| + K + 1, Real.pi / 8, ?_, ?_, ?_, ?_⟩
  · have := abs_nonneg (hslice u θ₀); linarith
  · positivity
  · linarith [hpi]
  · intro θ hθ
    have hπ8 : Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 := by ring
    have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hπ8, hpi], hθ.2⟩
    have hle : θ₀ ≤ θ := by
      rw [hθ₀def]
      linarith [hθ.1, hπ8]
    have hsub : Set.Ioc θ₀ θ ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_trans hθ₀mem.1.le hx.1.le, le_trans hx.2 hθmem.2.le⟩
    have hsub' : Set.Ioc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_trans hθ₀mem.1 hx.1, lt_of_le_of_lt hx.2 hθmem.2⟩
    have hsub'' : Set.Ioo θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₀mem.1 hx.1.le, lt_of_le_of_lt hx.2.le hθmem.2⟩
    have hGsub : MeasureTheory.IntegrableOn G (Set.Ioc θ₀ θ) := hGint.mono_set hsub
    have haesm : MeasureTheory.AEStronglyMeasurable (hsliceDeriv u)
        (volume.restrict (Set.Ioc θ₀ θ)) := by
      refine (aestronglyMeasurable_deriv (hslice u) volume).restrict.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
      exact (hderivH x (hsub' hx)).deriv
    have hInt' : MeasureTheory.IntegrableOn (hsliceDeriv u) (Set.Ioc θ₀ θ) :=
      MeasureTheory.Integrable.mono' hGsub haesm
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]
          exact hdom x))
    have hInt : IntervalIntegrable (hsliceDeriv u) volume θ₀ θ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr hInt'
    have hcont : ContinuousOn (hslice u) (Set.Icc θ₀ θ) :=
      hHC1.continuousOn.mono (fun x hx =>
        ⟨lt_of_lt_of_le hθ₀mem.1 hx.1, lt_of_le_of_lt hx.2 hθmem.2⟩)
    have hftc : ∫ x in θ₀..θ, hsliceDeriv u x = hslice u θ - hslice u θ₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
        (fun x hx => hderivH x (hsub'' hx)) hInt
    have e1 : hslice u θ = hslice u θ₀ + ∫ x in θ₀..θ, hsliceDeriv u x := by
      rw [hftc]; ring
    have e2 : |∫ x in θ₀..θ, hsliceDeriv u x| ≤ ∫ x in θ₀..θ, |hsliceDeriv u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have e3 : (∫ x in θ₀..θ, |hsliceDeriv u x|)
        = ∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x| := intervalIntegral.integral_of_le hle
    have e4 : (∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x|) ≤ ∫ x in Set.Ioc θ₀ θ, G x :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => abs_nonneg (hsliceDeriv u x)))
        hGsub (Filter.Eventually.of_forall hdom)
    have e5 : (∫ x in Set.Ioc θ₀ θ, G x) ≤ K := by
      rw [hKdef]
      exact MeasureTheory.setIntegral_mono_set hGint
        (Filter.Eventually.of_forall hGnn)
        (Filter.Eventually.of_forall (fun x hx => hsub hx))
    calc |hslice u θ| = |hslice u θ₀ + ∫ x in θ₀..θ, hsliceDeriv u x| := by rw [e1]
      _ ≤ |hslice u θ₀| + |∫ x in θ₀..θ, hsliceDeriv u x| := abs_add_le _ _
      _ ≤ |hslice u θ₀| + ∫ x in θ₀..θ, |hsliceDeriv u x| := by linarith [e2]
      _ = |hslice u θ₀| + ∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x| := by rw [e3]
      _ ≤ |hslice u θ₀| + ∫ x in Set.Ioc θ₀ θ, G x := by linarith [e4]
      _ ≤ |hslice u θ₀| + K + 1 := by linarith [e5]

/-! ## The endpoint limit -/

/-! Note the hypothesis `hg`: `u ≡ 1` is NOT admissible, since `Lzero1 1 = 1/cos²θ - 6` is not
square-integrable near `π/2`.  Route: `h := u' - tan θ · u` satisfies `h' = -(Lzero1 u) - 6u`, so
`h' ∈ L²` and `h` is bounded near `π/2`; hence `∫ (tan θ)²u² ≤ 2∫(u')² + 2∫h² < ∞` on
`(π/2 - δ, π/2)`.  If `ν ≠ 0` then `|u| ≥ |ν|/2` near `π/2` and `(tan θ)² ≥ c/(π/2 - θ)²` there,
contradicting `¬IntegrableOn (fun z => c / z ^ 2) (Ioi 0)`
(`Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow`, after `z = π/2 - θ`). -/
theorem slice_limit_at_right_eq_zero {u : ℝ → ℝ} {ν : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hu1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ν)) :
    ν = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  by_contra hν
  have hνne : ν ≠ 0 := hν
  have hν2 : 0 < ν ^ 2 := sq_pos_of_ne_zero hνne
  obtain ⟨M, δ₁, hMpos, hδ₁pos, _hδ₁lt, hbdd⟩ := hslice_bdd_near_pi_div_two hu hu0 hg
  obtain ⟨δ₂, hδ₂pos, hlow⟩ := abs_lower_of_tendsto_nhdsWithin hνne hlim
  set δ : ℝ := min δ₁ (min δ₂ (Real.pi / 8)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (lt_min hδ₂pos (by linarith [hpi]))
  have hδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ₂ : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδπ : δ ≤ Real.pi / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.integral_nonneg (fun θ => sq_nonneg (deriv u θ))
  set K : ℝ := 2 * B + 2 * M ^ 2 * δ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 * B := by linarith
    have h2 : 0 ≤ 2 * M ^ 2 * δ := by positivity
    linarith
  set C : ℝ := 16 * K / ν ^ 2 + 2 / δ with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 ≤ 16 * K / ν ^ 2 := div_nonneg (by linarith) hν2.le
    have h2 : 0 < 2 / δ := div_pos (by norm_num) hδpos
    linarith
  set ε : ℝ := 1 / C with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact div_pos one_pos hCpos
  have h2δ : 0 < 2 / δ := div_pos (by norm_num) hδpos
  have h2δC : 2 / δ ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ 16 * K / ν ^ 2 := div_nonneg (by linarith) hν2.le
    linarith
  have hεle : ε ≤ δ / 2 := by
    rw [hεdef]
    have h1 : (2 / δ)⁻¹ = δ / 2 := by rw [inv_div]
    simpa only [one_div, h1] using one_div_le_one_div_of_le h2δ h2δC
  have hεltδ : ε < δ := by linarith [hεle, hδpos]
  set a : ℝ := Real.pi / 2 - δ with hadef
  set b : ℝ := Real.pi / 2 - ε with hbdef
  have hle_ab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha0 : 0 ≤ a := by rw [hadef]; linarith [hδπ, hpi]
  have hbpi : b < Real.pi / 2 := by rw [hbdef]; linarith [hεpos]
  have hbaeq : b - a = δ - ε := by rw [hadef, hbdef]; ring
  have hsubIθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha0 hx.1.le, le_trans hx.2 hbpi.le⟩
  -- the pointwise comparison on `(a,b)`
  have hpt : ∀ x ∈ Set.Ioo a b,
      (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := by
    intro x hx
    have hxδ : Real.pi / 2 - δ < x := by simpa [hadef] using hx.1
    have hxε : x < Real.pi / 2 - ε := by simpa [hbdef] using hx.2
    have hxπ : x < Real.pi / 2 := by linarith [hxε, hεpos]
    have hx4 : Real.pi / 4 < x := by linarith [hxδ, hδπ, hpi]
    have hxne : Real.pi / 2 - x ≠ 0 := by linarith
    have htan_low : 1 / (2 * (Real.pi / 2 - x)) ≤ Real.tan x :=
      inv_two_mul_pi_div_two_sub_le_tan ⟨hx4, hxπ⟩
    have htan_sq : (1 / (2 * (Real.pi / 2 - x))) ^ 2 ≤ (Real.tan x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) htan_low 2
    have hbddmem : x ∈ Set.Ioo (Real.pi / 2 - δ₁) (Real.pi / 2) :=
      ⟨by linarith [hxδ, hδ₁], hxπ⟩
    have hhlow : |deriv u x - Real.tan x * u x| ≤ M := by
      have h := hbdd x hbddmem
      simpa only [hslice] using h
    have hl2mem : x ∈ Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2) :=
      ⟨by linarith [hxδ, hδ₂], hxπ⟩
    have hulow : |ν| / 2 ≤ |u x| := hlow x hl2mem
    have hu2 : (|ν| / 2) ^ 2 ≤ (u x) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |ν| / 2) hulow 2
      rwa [sq_abs] at h
    have step1 : (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ (u x) ^ 2 * (Real.tan x) ^ 2 := by
      have hsq : (|ν| / 2) ^ 2 = ν ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
      have h2sq : (1 / (2 * (Real.pi / 2 - x))) ^ 2 = 1 / (4 * (Real.pi / 2 - x) ^ 2) := by
        rw [div_pow]; ring
      have heq : (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
          = (|ν| / 2) ^ 2 * (1 / (2 * (Real.pi / 2 - x))) ^ 2 := by
        rw [hsq, h2sq, inv_pow]
        field_simp
        ring
      rw [heq]
      exact mul_le_mul hu2 htan_sq (by positivity) (by positivity)
    have step2 : (Real.tan x * u x) ^ 2 ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := by
      have hsplit : Real.tan x * u x = deriv u x - (deriv u x - Real.tan x * u x) := by ring
      rw [hsplit]
      have hz2 : (deriv u x - Real.tan x * u x) ^ 2 ≤ M ^ 2 := by
        nlinarith [hhlow, abs_nonneg (deriv u x - Real.tan x * u x),
          sq_abs (deriv u x - Real.tan x * u x), abs_nonneg M, sq_abs M, hMpos.le]
      nlinarith [sq_nonneg (deriv u x + (deriv u x - Real.tan x * u x)), hz2,
        sq_nonneg (deriv u x)]
    calc (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ (u x) ^ 2 * (Real.tan x) ^ 2 := step1
      _ = (Real.tan x * u x) ^ 2 := by ring
      _ ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := step2
  -- integrability on the interval
  have hIntf1 : IntervalIntegrable
      (fun x : ℝ => (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2) volume a b := by
    have hcont_inv : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x)⁻¹) (Set.Icc a b) := by
      refine ContinuousOn.inv₀ (continuous_const.sub continuous_id).continuousOn ?_
      intro x hx
      exact sub_ne_zero.mpr (by linarith [hx.2, hbpi])
    have hc : ContinuousOn (fun x : ℝ => ((Real.pi / 2 - x)⁻¹) ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hle_ab]
      exact hcont_inv.pow 2
    exact (hc.const_mul (ν ^ 2 / 16)).intervalIntegrable
  have hInt2 : IntervalIntegrable (fun x : ℝ => 2 * (deriv u x) ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle_ab]
    exact (hu1.mono_set hsubIθ).const_mul 2
  have hIntc : IntervalIntegrable (fun _ : ℝ => 2 * M ^ 2) volume a b :=
    intervalIntegrable_const
  have hIntf2 : IntervalIntegrable (fun x : ℝ => 2 * (deriv u x) ^ 2 + 2 * M ^ 2)
      volume a b := hInt2.add hIntc
  have hmono : (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2)
      ≤ ∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hle_ab hIntf1 hIntf2 hpt
  have hLHS : (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2)
      = (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_pi_div_two_sub_inv_sq a b hle_ab hbpi]
  have hRHS : (∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2))
      = 2 * (∫ x in a..b, (deriv u x) ^ 2) + 2 * M ^ 2 * (b - a) := by
    rw [intervalIntegral.integral_add hInt2 hIntc, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsubint : (∫ x in a..b, (deriv u x) ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le hle_ab, hBdef]
    exact MeasureTheory.setIntegral_mono_set hu1
      (Filter.Eventually.of_forall (fun x => sq_nonneg (deriv u x)))
      (Filter.Eventually.of_forall (fun x hx => hsubIθ hx))
  have hkey : (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹)
      ≤ 2 * B + 2 * M ^ 2 * δ := by
    calc (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹)
        = (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2) := hLHS.symm
      _ ≤ ∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2) := hmono
      _ = 2 * (∫ x in a..b, (deriv u x) ^ 2) + 2 * M ^ 2 * (b - a) := hRHS
      _ ≤ 2 * B + 2 * M ^ 2 * δ := by
          have h1 : 2 * (∫ x in a..b, (deriv u x) ^ 2) ≤ 2 * B :=
            mul_le_mul_of_nonneg_left hsubint (by norm_num)
          have h2 : 2 * M ^ 2 * (b - a) ≤ 2 * M ^ 2 * δ := by
            have h3 : 0 ≤ 2 * M ^ 2 := by positivity
            rw [hbaeq]
            exact mul_le_mul_of_nonneg_left (by linarith) h3
          linarith
  have hb_inv : (Real.pi / 2 - b)⁻¹ = C := by
    have h1 : Real.pi / 2 - b = ε := by rw [hbdef]; ring
    rw [h1, hεdef]
    simp
  have ha_inv : (Real.pi / 2 - a)⁻¹ = δ⁻¹ := by
    have h1 : Real.pi / 2 - a = δ := by rw [hadef]; ring
    rw [h1]
  rw [hb_inv, ha_inv] at hkey
  have hval : (ν ^ 2 / 16) * (C - δ⁻¹) = K + ν ^ 2 / (16 * δ) := by
    rw [hCdef, hKdef]
    field_simp
    ring
  rw [hval] at hkey
  rw [hKdef] at hkey
  have hpos : 0 < ν ^ 2 / (16 * δ) := div_pos hν2 (by positivity)
  linarith

end

end Work.FTS.EllipticEst.remov.coerc
