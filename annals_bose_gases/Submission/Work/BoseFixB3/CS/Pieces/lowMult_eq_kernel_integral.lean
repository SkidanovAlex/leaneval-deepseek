import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.kernel_joint_integrable
import Submission.Work.BoseFixB3.CS.Pieces.realPart_integral_integral_swap
import Submission.Work.BoseFixB3.HighMass.Base
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral`

The low-momentum multiplier `Work.BoseBoxFix.lowMult fc κ ℓ ψ x` (the `p`-convention Fourier
multiplier `f(‖p‖/κ)` of the box extension `1_{Λ(ℓ)}ψ`) as the **kernel integral**

  `lowMult fc κ ℓ ψ x
     = (2π)⁻³ ∫_z (∫_p Re(e^{i⟪p,x⟫} f(‖p‖/κ) e^{−i⟪p,z⟫})) · 1_{Λ(ℓ)}(z)ψ(z) dz`

i.e. the two momentum/position integrals in the definition of `lowMult` are interchanged
(Fubini) and the real part is moved inside (both operations being legitimate because the
integrand is `L¹` for the product measure, thanks to the compactly supported cut-off and the
boundedness of `ψ` on the finite-measure cube).

## Route

Write `g := 1_{Λ(ℓ)}ψ` and, for fixed `x`, the kernel
`F p z := e^{i⟪p,x⟫} f(‖p‖/κ) e^{−i⟪p,z⟫} · g(z)`.

* `Work.BoseFixB3.CS.Pieces.kernel_joint_integrable` — `F` is `L¹(volume × volume)`:
  its modulus is `|f(‖p‖/κ)|·|g z|`, a product of an `L¹` function of `p` (the cut-off is
  compactly supported) and of the `L¹` function `g` (bounded on a finite-measure set);
* the pointwise identity `e^{i⟪p,x⟫}f(‖p‖/κ)·kinFT g p = ∫_z F p z` pulls the constant
  `e^{i⟪p,x⟫}f(‖p‖/κ)` inside the `kinFT` integral, giving the LHS of the target as the
  real part of `∬ F`;
* `Work.BoseFixB3.CS.Pieces.realPart_integral_integral_swap` — Fubini for `F` together with
  `Re(∫) = ∫ Re` (the continuous linear functional `Complex.reCLM` commutes with the Bochner
  integral), turning `Re ∬ F` into the iterated integral `∫_z ∫_p Re(F p z)`;
* finally `Re(F p z) = Re(e^{i⟪p,x⟫}f(‖p‖/κ)e^{−i⟪p,z⟫})·g(z)` (`Complex.mul_re`, the
  imaginary part of the real factor vanishing) and `g(z)` is pulled out of the `p`-integral.
-/

namespace Work.BoseFixB3.CS.Pieces

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private lemma norm_phase (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (t : ℂ), Complex.norm_exp_ofReal_mul_I]

private lemma norm_phase_neg (t : ℝ) : ‖Complex.exp (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-t)

/-- The norm of a real number cast to `ℂ` is its absolute value. -/
private lemma norm_cast_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

private lemma continuous_kern (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (x z : E3) :
    Continuous (fun p : E3 =>
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) := by
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const))))
  · exact Complex.continuous_ofReal.comp
      (fc.smooth.continuous.comp (continuous_norm.div_const κ))
  · exact Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const)))))

set_option maxHeartbeats 1600000 in
theorem lowMult_eq_kernel_integral {fc : Work.BoseBoxFix.LowCut} {κ ℓ C : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψm : MeasureTheory.AEStronglyMeasurable ψ MeasureTheory.volume)
    (hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ C) (hC : 0 ≤ C)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ z : EuclideanSpace ℝ (Fin 3),
          (∫ p : EuclideanSpace ℝ (Fin 3),
            (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re)
          * ((Submission.BoseGases.acube ℓ).indicator ψ z) := by
  classical
  set F : E3 → E3 → ℂ := fun p z =>
      (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) *
        (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hFdef
  -- (0) the cut-off symbol is compactly supported, so is its modulus
  have hcs : HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) :=
    Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport hκ
  have hfabs : Integrable (fun p : E3 => |fc.f (‖p‖ / κ)|) :=
    (continuous_abs.comp (fc.smooth.continuous.comp (continuous_norm.div_const κ))).integrable_of_hasCompactSupport
      hcs.abs
  -- (1) the box indicator: bounded by `C` and integrable
  have hι_bdd : ∀ z : E3, |(Submission.BoseGases.acube ℓ).indicator ψ z| ≤ C := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]; exact hψb z hz
    · rw [Set.indicator_of_notMem hz]; simpa using hC
  have hι_int : Integrable
      (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) := by
    have h1 : Integrable (fun z : E3 => (Submission.BoseGases.acube ℓ).indicator ψ z) := by
      rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
      refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
        hψm.restrict C ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
        with z hz
      rw [Real.norm_eq_abs]
      exact hψb z hz
    refine MeasureTheory.Integrable.mono' h1.norm ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable h1.1
    · exact le_of_eq (RCLike.norm_ofReal _)
  -- (2) joint integrability of the kernel
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h := kernel_joint_integrable (s := Submission.BoseGases.acube ℓ) (fc := fc)
      (κ := κ) (C := C) hκ (Submission.BoseGases.acube_measurable ℓ)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hψm hψb hC x
    simpa only [hFdef] using h
  -- (3) slice integrability
  have hslice : ∀ z : E3, Integrable (fun p : E3 => F p z) := by
    intro z
    refine MeasureTheory.Integrable.mono' (hfabs.mul_const C) ?_ ?_
    · exact ((continuous_kern fc κ x z).mul continuous_const).aestronglyMeasurable
    · filter_upwards with p
      have hnorm : ‖(Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) *
            (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)‖
          = |fc.f (‖p‖ / κ)| * |(Submission.BoseGases.acube ℓ).indicator ψ z| := by
        simp only [norm_mul, norm_phase, norm_phase_neg, norm_cast_ofReal]
        ring
      simp only [hFdef]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (hι_bdd z) (abs_nonneg _)
  -- (4) `lowMult` as the real part of the iterated integral of `F`
  have hkey : (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT
          (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p)
      = ∫ p : E3, ∫ z : E3, F p z := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [Submission.BoseGases.kinFT, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    simp only [hFdef]
    ring
  have hLHS : Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ∫ z : E3, F p z).re := by
    rw [Work.BoseBoxFix.lowMult, Complex.re_ofReal_mul, hkey]
  -- (5) Fubini + real part
  have hcore : (∫ p : E3, ∫ z : E3, F p z).re
      = ∫ z : E3,
          (∫ p : E3,
            (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re)
          * ((Submission.BoseGases.acube ℓ).indicator ψ z) := by
    rw [realPart_integral_integral_swap hFint hslice]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    have hpt : ∀ p : E3,
        ((Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) *
            (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)).re
          = (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re
            * ((Submission.BoseGases.acube ℓ).indicator ψ z) := by
      intro p
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [hFdef]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_mul_const]
  rw [hLHS, hcore]

end

end Work.BoseFixB3.CS.Pieces
