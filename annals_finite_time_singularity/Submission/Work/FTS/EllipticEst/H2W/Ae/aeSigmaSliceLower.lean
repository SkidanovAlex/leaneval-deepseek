/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.Ae.aeSigmaSliceLower` — the `σ`-weighted self-form lower bound for `AeData` slices

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate of
Elgindi's `prop:H2`, and for almost every `z > 0`, the `σ`-weighted angular self-form of the slice
`θ ↦ u z θ` is bounded below,

`-K ∫_θ (u z θ)² σ θ ≤ ∫_θ (Lzero1 (u z ·) θ) · (u z θ) · σ θ`,   `σ θ = sin(2θ)^{-η}`,

with a constant `K > 0` depending only on `η = 99/100` (in fact `K = η + 6`), uniformly in `α`,
`u`, `G`.

## The route

The engine is the honest slicewise coercivity `Honest.HonSliceSigmaLower η hη0 hη1`: for a slice
`f` which is `C²` on the *open* interval `(0, π/2)`, `C¹` on the *closed* interval `[0, π/2]`,
with `f 0 = f (π/2) = 0` and the four weighted integrands honest, it gives

`((1 - η)/(1 + η)) ∫ (f')² σ ≤ ∫ (Lzero1 f) f σ + K ∫ f² σ`;

dropping the nonnegative left-hand side yields the desired lower bound.  Two things must be
produced from the `AeData` hypotheses.

* **`C¹` up to the endpoints.**  `AeData` gives `u` smooth on the *open* quadrant and the
  Dirichlet data only as *values*.  For almost every `z` the left trace of the slice vanishes —
  here we use `H2W.AeLeftClean.sliceLeftTendstoClean`, a self-contained re-proof of the a.e. left
  limit whose import cone avoids the `EllHyp`-rescoping casualties — while the right trace
  vanishes for *every* `z > 0` (`H2W.Ae.AeSliceRightTendsto`).  The one-sided limits of
  `deriv (u z ·)` at the two endpoints exist because `(∂_θθu(z,·))²σ` is integrable
  (`Honest.HkMemSliceSqSigma` and `AeData.memAng2`): the second derivative is then `L¹`, and
  `exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` /
  `exists_tendsto_nhdsLT_of_integrableOn_deriv` apply.  With these,
  `Honest.PthCore.contDiffOnOneExtension` produces a `C¹` extension `g` of the slice to
  `[0, π/2]` with `g 0 = g (π/2) = 0`; since the *values* `u z 0 = u z (π/2) = 0` are fields of
  `AeData`, `g` agrees with the slice on all of `[0, π/2]`, so the slice itself is `C¹` on
  `[0, π/2]` and `C²` on `(0, π/2)`.
* **The four honesty conditions.**  `(f')²σ` and `f²σ` on `(0, π/2)` come from
  `WeakMoment.SliceSqBoundsOpen`; `(f'')²σ` from `Honest.HkMemSliceSqSigma`; and
  `(Lzero1 f) · f · σ` on `Iθ` is proved in this file (`slice_lzero_sigma_integrable`) by
  combining the pointwise identity `Lzero1 f · f = -f'' f + (f/cos θ)² + tan θ · f' f - 6 f²`
  with the endpoint bounds of `AngAWeak.angSliceBoundsWeak` and the integrability of `σ`
  (`remov.ws_sEta_integrableOn`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen
import Submission.Work.FTS.EllipticEst.AngAWeak.angSliceBoundsWeak
import Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "σ" => Work.FTS.EllipticEst.sEta

/-! ## Elementary facts -/

/-- The angular weight `σ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem sigma_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ σ θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- `|a b| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  rw [abs_mul, ← sq_abs a, ← sq_abs b]
  nlinarith [h]

/-! ## The one-sided limits of `deriv` of a weighted-`H²` slice -/

/-- For a slice which is `C²` on `(0, π/2)` and whose `σ`-weighted second derivative is
integrable, `deriv` has finite one-sided limits at `0⁺` and at `(π/2)⁻`. -/
theorem slice_deriv_limits {f : ℝ → ℝ}
    (h2 : ContDiffOn ℝ 2 f Iθo)
    (hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ) :
    (∃ L : ℝ, Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L)) ∧
      (∃ L : ℝ, Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds L)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hdd
  have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
  have hmem : AEStronglyMeasurable (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (volume.restrict Iθo) := (measurable_deriv (deriv f)).aestronglyMeasurable
  have hint : IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ) Iθo := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff hmem).mp ?_
    rw [MeasureTheory.IntegrableOn] at habs
    simpa [Real.norm_eq_abs] using habs
  have hder1 : ∀ x ∈ Iθo, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((h2.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hder2 : ∀ x ∈ Iθo, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    intro x hx
    exact (((h2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  exact ⟨Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (f := deriv f) (f' := fun θ => deriv (fun t : ℝ => deriv f t) θ) hπ hder2 hint,
    Work.FTS.EllipticEst.H2W.exists_tendsto_nhdsLT_of_integrableOn_deriv
      (f := deriv f) (f' := fun θ => deriv (fun t : ℝ => deriv f t) θ)
      (a := (0 : ℝ)) (b := Real.pi / 2) hπ hder2 hint⟩

/-! ## The `σ`-weighted self-form integrand of a slice -/

/-- **The `σ`-weighted `Lzero1`-self-form integrand of a slice is integrable on `Iθ`.**

For `f` which is `C²` on `(0, π/2)` with `(f'')²σ` and `f²σ` integrable on `Iθ`, and with the
endpoint bounds `|f θ| ≤ C (π/2 - θ)`, `|f' θ| ≤ C` (`C > 0`), the integrand `Lzero1 f · f · σ`
is integrable on `Iθ`. -/
theorem slice_lzero_sigma_integrable {f : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hsm2 : ContDiffOn ℝ 2 f Iθo)
    (hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hu2 : IntegrableOn (fun θ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) Work.Spaces.Iθ := by
  -- the pointwise identity on the open interval
  have hpoint : ∀ θ ∈ Iθo, Work.FTS.EllipticEst.Lzero1 f θ * f θ
      = -(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
        + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2 := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
    have hd1 : DifferentiableAt ℝ f θ :=
      (hsm2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
    have hderiv_tan : deriv (fun t : ℝ => Real.tan t * f t) θ
        = f θ / Real.cos θ ^ 2 + Real.tan θ * deriv f θ := by
      have h := deriv_mul hd2 hd1
      rw [Real.deriv_tan, one_div, inv_mul_eq_div] at h
      exact h
    simp only [Work.FTS.EllipticEst.Lzero1, hderiv_tan]
    ring
  -- continuity of the explicit form on the open interval
  have hcos_ne : ∀ θ ∈ Iθo, Real.cos θ ≠ 0 := fun θ hθ => ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hcd1 : ContinuousOn (deriv f) Iθo :=
    hsm2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcd2 : ContinuousOn (fun θ => deriv (fun t : ℝ => deriv f t) θ) Iθo :=
    (hsm2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)
  have htan : ContinuousOn Real.tan Iθo := Real.continuousOn_tan.mono (fun θ hθ => hcos_ne θ hθ)
  have hcont_expl : ContinuousOn (fun θ : ℝ => -(deriv (fun t => deriv f t) θ) * f θ
      + (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2) Iθo := by
    have h1 : ContinuousOn (fun θ : ℝ => -(deriv (fun t => deriv f t) θ) * f θ) Iθo :=
      hcd2.neg.mul hsm2.continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => (f θ / Real.cos θ) ^ 2) Iθo :=
      (hsm2.continuousOn.div Real.continuous_cos.continuousOn
        (fun θ hθ => hcos_ne θ hθ)).pow 2
    have h3 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv f θ * f θ) Iθo :=
      (htan.mul hcd1).mul hsm2.continuousOn
    have h4 : ContinuousOn (fun θ : ℝ => 6 * (f θ) ^ 2) Iθo :=
      (hsm2.continuousOn.pow 2).const_mul 6
    exact ((h1.add h2).add h3).sub h4
  have hcont_lz : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 f θ * f θ) Iθo :=
    hcont_expl.congr (fun θ hθ => (hpoint θ hθ))
  have hσcont : ContinuousOn σ Iθo := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo
    exact h1.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2]))))
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) (volume.restrict Iθo) :=
    (hcont_lz.mul hσcont).aestronglyMeasurable measurableSet_Ioo
  -- the integrable majorant
  have hmaj : IntegrableOn (fun θ : ℝ => (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
      + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ) Iθo :=
    (((hdd.mono_set Ioo_subset_Icc_self).const_mul (1 / 2)).add
      ((hu2.mono_set Ioo_subset_Icc_self).const_mul (13 / 2 : ℝ))).add
      ((Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.mono_set
        Ioo_subset_Icc_self).const_mul _)
  -- the pointwise bound
  have hbound : ∀ θ ∈ Iθo, ‖Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ‖
      ≤ (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
        + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
        + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hσnn : 0 ≤ σ θ := Real.rpow_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))) _
    -- `π/2 - θ ≤ (π/2) cos θ`
    have hδle : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
      have hδ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have hmul : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
        have h := Real.mul_le_sin (x := Real.pi / 2 - θ) hδ0.le
          (by linarith [Real.pi_pos, hθ.1])
        rwa [Real.sin_pi_div_two_sub] at h
      have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by
        have h2 : (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ := (inv_div Real.pi 2).symm
        rw [h2, mul_inv_cancel₀ (by positivity : (Real.pi / 2) ≠ 0)]
      have h1 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      rwa [← mul_assoc, hpi, one_mul] at h1
    have hδdiv : (Real.pi / 2 - θ) / Real.cos θ ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hcos]
      exact hδle
    -- `|f θ| / cos θ ≤ C (π/2)`
    have hfcos : |f θ / Real.cos θ| ≤ C * (Real.pi / 2) := by
      rw [abs_div, abs_of_pos hcos]
      calc |f θ| / Real.cos θ ≤ (C * (Real.pi / 2 - θ)) / Real.cos θ :=
            div_le_div_of_nonneg_right (hb2 θ hθ) hcos.le
        _ = C * ((Real.pi / 2 - θ) / Real.cos θ) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hδdiv hC.le
    have htan_le : |Real.tan θ| ≤ 1 / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one θ) hcos.le
    -- the four pieces of the explicit form
    have h1 : |-(deriv (fun t => deriv f t) θ) * f θ|
        ≤ ((-(deriv (fun t => deriv f t) θ)) ^ 2 + (f θ) ^ 2) / 2 :=
      abs_mul_le_half_sq _ _
    have h2 : |(f θ / Real.cos θ) ^ 2| ≤ (C * (Real.pi / 2)) ^ 2 := by
      rw [abs_sq]
      have h := pow_le_pow_left₀ (abs_nonneg (f θ / Real.cos θ)) hfcos 2
      rwa [sq_abs] at h
    have h3 : |Real.tan θ * deriv f θ * f θ| ≤ (Real.pi / 2) * C ^ 2 := by
      rw [abs_mul, abs_mul]
      calc |Real.tan θ| * |deriv f θ| * |f θ|
          ≤ (1 / Real.cos θ) * C * (C * (Real.pi / 2 - θ)) := by
            refine mul_le_mul (mul_le_mul htan_le (hb3 θ hθ) (abs_nonneg _)
              (by positivity)) (hb2 θ hθ) (abs_nonneg _) (by positivity)
        _ = C ^ 2 * ((Real.pi / 2 - θ) / Real.cos θ) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ C ^ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hδdiv (sq_nonneg C)
        _ = (Real.pi / 2) * C ^ 2 := by ring
    have h4 : |6 * (f θ) ^ 2| = 6 * (f θ) ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
    have hkey : |Work.FTS.EllipticEst.Lzero1 f θ * f θ|
        ≤ (1 / 2) * (deriv (fun t => deriv f t) θ) ^ 2 + (13 / 2 : ℝ) * (f θ) ^ 2
          + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) := by
      rw [hpoint θ hθ]
      have htri : |-(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
            + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2|
          ≤ |-(deriv (fun t => deriv f t) θ) * f θ| + |(f θ / Real.cos θ) ^ 2|
            + |Real.tan θ * deriv f θ * f θ| + |6 * (f θ) ^ 2| := by
        have hA := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ
            + (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ)
          (-(6 * (f θ) ^ 2))
        rw [abs_neg] at hA
        have hB := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ
            + (f θ / Real.cos θ) ^ 2) (Real.tan θ * deriv f θ * f θ)
        have hC' := abs_add_le (-(deriv (fun t => deriv f t) θ) * f θ)
          ((f θ / Real.cos θ) ^ 2)
        have hsplit : -(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
              + Real.tan θ * deriv f θ * f θ - 6 * (f θ) ^ 2
            = (-(deriv (fun t => deriv f t) θ) * f θ + (f θ / Real.cos θ) ^ 2
              + Real.tan θ * deriv f θ * f θ) + (-(6 * (f θ) ^ 2)) := by ring
        rw [hsplit]
        linarith [hA, hB, hC', h4]
      nlinarith [htri, h1, h2, h3]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσnn]
    calc |Work.FTS.EllipticEst.Lzero1 f θ * f θ| * σ θ
        ≤ ((1 / 2) * (deriv (fun t => deriv f t) θ) ^ 2 + (13 / 2 : ℝ) * (f θ) ^ 2
            + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2)) * σ θ :=
          mul_le_mul_of_nonneg_right hkey hσnn
      _ = (1 / 2) * ((deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
            + (13 / 2 : ℝ) * ((f θ) ^ 2 * σ θ)
            + ((C * (Real.pi / 2)) ^ 2 + (Real.pi / 2) * C ^ 2) * σ θ := by ring
  have hIntIoo : IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ) Iθo :=
    hmaj.mono' haesm (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hbound θ hθ))
  exact IntegrableOn.congr_set_ae hIntIoo (by
    show Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm)

/-! ## The target -/

/-- **L1 — the `σ`-weighted angular self-form lower bound for the slices of an `AeData` datum.**
(File `Submission/Work/FTS/EllipticEst/H2W/Ae/aeSigmaSliceLower.lean`, declaration
`Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower`.)

Route (do prove it; the pieces are all in the tree and are `#print axioms`-clean — check with
`#print axioms`, do NOT trust import-cone greps):
* for a.e. `z`, `Work.FTS.EllipticEst.H2W.AeProof.AeSliceLeftTendstoAe` gives
  `Tendsto (u z) (𝓝[>] 0) (𝓝 0)` and `Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto` gives the
  same at `(π/2)⁻` (for every `z > 0`); `AeData.dirZero`/`AeData.dirPi` give the *values*
  `u z 0 = u z (π/2) = 0`;
* `(∂_θθ u(z,·))² σ` is integrable (`Honest.HkMemSliceSqSigma` + `AeData.memAng2`), hence
  `deriv (u z)` has finite one-sided limits at `0` and `π/2` (Cauchy criterion: the difference of
  two values is bounded by `√(∫(∂_θθu)²σ)·√(∫σ⁻¹)` with `σ⁻¹ = sin(2θ)^η` integrable), so the
  hypotheses of `Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension` hold;
* apply `Work.FTS.EllipticEst.Honest.HonSliceSigmaLower` (`η = Work.Spaces.eta`, `hη0`, `hη1`)
  to the extension `g`; its hypotheses are `ContDiffOn ℝ 2 g (Ioo 0 (π/2))`,
  `ContDiffOn ℝ 1 g (Icc 0 (π/2))`, `g 0 = g (π/2) = 0`, and the integrability of `(g')²σ`,
  `(g'')²σ`, `g²σ` on `Ioo` and of `Lzero1 g · g · σ` on `Iθ` (the last one via the equation
  `Lzero1 u = G + α²z²∂_zzu + α(5+α)z∂_zu`, `AeData.eq`, plus Cauchy–Schwarz); it gives
  `((1-η)/(1+η))∫(g')²σ ≤ ∫(Lzero1 g)gσ + K∫g²σ`;
* drop the nonnegative left-hand term (so `-K∫g²σ ≤ ∫(Lzero1 g)gσ`) and transfer back to the
  slice: `g` and `u z` agree on `Ioo`, so the `Iθ`-integrals of the two integrands agree.
The constant `K` must depend only on `η` (universal in `α`, `u`, `G`). -/
theorem aeSigmaSliceLower : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ) θ * u z θ
                * Work.FTS.EllipticEst.sEta θ := by
  obtain ⟨K, hK0, hK⟩ :=
    Honest.HonSliceSigmaLower Work.Spaces.eta Work.Spaces.eta_nonneg Work.Spaces.eta_lt_one
  obtain ⟨_C0, _hC0, hSq⟩ := WeakMoment.SliceSqBoundsOpen
  refine ⟨K, hK0, ?_⟩
  intro α u G h
  -- the a.e. left trace, and the a.e. continuity of the slice on the closed interval
  have hL := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  have hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) Work.Spaces.Iθ := by
    filter_upwards [hL, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hLz hz
    refine Work.FTS.EllipticEst.H2W.AeProof.continuousOn_Icc_of_tendsto
      (by linarith [Real.pi_pos]) ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1).continuousOn
    · simpa only [h.dirZero z] using hLz
    · simpa only [h.dirPi z] using
        (Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz)
  filter_upwards [hL, hC, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hLz hCz hz
  set f : ℝ → ℝ := fun θ => u z θ with hfdef
  have hf0 : f 0 = 0 := by rw [hfdef]; exact h.dirZero z
  have hfπ : f (Real.pi / 2) = 0 := by rw [hfdef]; exact h.dirPi z
  have hCz' : ContinuousOn f Work.Spaces.Iθ := by simpa only [hfdef] using hCz
  have hLz' : Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [hfdef] using hLz
  have hπlim : Tendsto f (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [hfdef] using
      (Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz)
  -- the slice is smooth on the open interval
  have hsm_all : ∀ n : ℕ, ContDiffOn ℝ n f Iθo := fun n =>
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz n
  have hsm2 : ContDiffOn ℝ 2 f Iθo := hsm_all 2
  -- `(∂_θθ u(z,·))²σ` is integrable
  have hdd : IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * σ θ)
        Work.Spaces.Iθ := Honest.HkMemSliceSqSigma (α := α) h.memAng2 hz
    refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    change Work.Spaces.pthIter 2 u z θ ^ 2 * σ θ = deriv (fun t : ℝ => deriv f t) θ ^ 2 * σ θ
    have hpth : Work.Spaces.pthIter 2 u z θ = deriv (fun t : ℝ => deriv f t) θ := rfl
    rw [hpth]
  -- `f²σ` and `(f')²σ` are integrable on `Iθ`
  obtain ⟨hu2, _hu2b, hdu, _hdub⟩ := hSq f hsm_all hCz' hf0 hfπ hdd
  -- the endpoint bounds
  obtain ⟨C, hCpos, _hb1, hb2, hb3⟩ :=
    AngAWeak.angSliceBoundsWeak f hsm2 hCz' hf0 hfπ hdd
  -- the `Lzero1`-self-form integrand is integrable on the slice
  have hlz : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ)
      Work.Spaces.Iθ :=
    slice_lzero_sigma_integrable hCpos hsm2 hdd hu2 hb2 hb3
  -- the one-sided limits of `deriv`
  obtain ⟨hlim0, hlimπ⟩ := slice_deriv_limits hsm2 hdd
  -- the `C¹` extension of the slice to the closed interval
  obtain ⟨g, hg1, hg0, hgpi, hgeq⟩ :=
    Honest.PthCore.contDiffOnOneExtension (f := f) (hsm_all 1) hLz' hπlim hlim0 hlimπ
  -- the slice itself is `C²` on the open interval and `C¹` on the closed one
  have hg2 : ContDiffOn ℝ 2 g Iθo := hsm2.congr (fun x hx => (hgeq x hx).1)
  have hgeqIcc : ∀ θ ∈ Work.Spaces.Iθ, g θ = f θ := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, hg0, hf0]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, hgpi, hfπ]
    · exact (hgeq θ ⟨h0, h1⟩).1
  have hf1 : ContDiffOn ℝ 1 f Work.Spaces.Iθ :=
    hg1.congr (fun x hx => (hgeqIcc x hx).symm)
  -- the honest slicewise coercivity
  have hres := hK f hsm2 hf1 hf0 hfπ
    (hdu.mono_set Ioo_subset_Icc_self) (hdd.mono_set Ioo_subset_Icc_self)
    (hu2.mono_set Ioo_subset_Icc_self) hlz
  -- drop the nonnegative derivative term
  have hnn : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * σ θ) := by
    refine mul_nonneg ?_ ?_
    · have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_nonneg]
      exact div_nonneg (by linarith [Work.Spaces.eta_lt_one]) h1.le
    · exact MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sigma_nonneg_Iθ hθ))
  have hfinal : -K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ * σ θ := by
    have h := hres
    have h2 := hnn
    simp only [Work.FTS.EllipticEst.sEta] at h h2 ⊢
    linarith
  simpa only [hfdef] using hfinal

end Work.FTS.EllipticEst.H2W.Ae
