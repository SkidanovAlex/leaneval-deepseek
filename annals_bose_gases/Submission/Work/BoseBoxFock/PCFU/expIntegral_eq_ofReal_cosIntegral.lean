import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.fL_latticeSum_eq_periodisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The complex exponential integral of an even weight

For an even weight `W` the complex Fourier integral `∫ W(x)·e^{i⟪x,k⟫}dx` is the (real) cosine
integral `∫ W(x)·cos⟪x,k⟫dx`: the imaginary part `∫ W(x)·sin⟪x,k⟫dx` vanishes because the
integrand is odd (and `∫ f(-x) = ∫ f(x)` for the Lebesgue measure on `ℝ³`). -/

private lemma expIntegral_aux (W : E3 → ℝ) (k : E3)
    (hWe : ∀ x : E3, W (-x) = W x)
    (hI : Integrable (fun x : E3 => Complex.exp (Complex.I * (inner ℝ x k : ℂ)) * (W x : ℂ))) :
    (∫ x : E3, Complex.exp (Complex.I * (inner ℝ x k : ℂ)) * (W x : ℂ))
      = ((∫ x : E3, W x * Real.cos (inner ℝ x k) : ℝ) : ℂ) := by
  set F : E3 → ℂ := fun x => Complex.exp (Complex.I * (inner ℝ x k : ℂ)) * (W x : ℂ) with hFdef
  have hFi : Integrable F := by simpa only [hFdef] using hI
  have hreF : ∀ x : E3, (F x).re = W x * Real.cos (inner ℝ x k) := by
    intro x
    have h1 : (Complex.exp (Complex.I * (inner ℝ x k : ℂ))).re = Real.cos (inner ℝ x k) := by
      rw [mul_comm Complex.I (inner ℝ x k : ℂ), Complex.exp_ofReal_mul_I_re]
    simp only [hFdef]
    rw [Complex.mul_re, h1, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have himF : ∀ x : E3, (F x).im = Real.sin (inner ℝ x k) * W x := by
    intro x
    have h2 : (Complex.exp (Complex.I * (inner ℝ x k : ℂ))).im = Real.sin (inner ℝ x k) := by
      rw [mul_comm Complex.I (inner ℝ x k : ℂ), Complex.exp_ofReal_mul_I_im]
    simp only [hFdef]
    rw [Complex.mul_im, h2, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsin_real : (∫ x : E3, W x * Real.sin (inner ℝ x k)) = 0 := by
    have h2 : (∫ x : E3, W x * Real.sin (inner ℝ x k))
        = ∫ x : E3, -(W x * Real.sin (inner ℝ x k)) := by
      rw [← MeasureTheory.integral_neg_eq_self (fun x : E3 => W x * Real.sin (inner ℝ x k))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [inner_neg_left, Real.sin_neg, hWe x]
      ring
    rw [MeasureTheory.integral_neg] at h2
    linarith
  have hre0 : (∫ x : E3, (F x).re) = ∫ x : E3, W x * Real.cos (inner ℝ x k) :=
    integral_congr_ae (Filter.Eventually.of_forall hreF)
  have hsin0 : (∫ x : E3, (F x).im) = 0 :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [himF x, mul_comm])).trans
      hsin_real
  have hre_int : (∫ x : E3, (F x).re) = (∫ x : E3, F x).re :=
    ContinuousLinearMap.integral_comp_comm Complex.reCLM hFi
  have him_int : (∫ x : E3, (F x).im) = (∫ x : E3, F x).im :=
    ContinuousLinearMap.integral_comp_comm Complex.imCLM hFi
  have h1 : (∫ x : E3, F x).re = ∫ x : E3, W x * Real.cos (inner ℝ x k) :=
    hre_int.symm.trans hre0
  have h2 : (∫ x : E3, F x).im = 0 := him_int.symm.trans hsin0
  conv_lhs => rw [← Complex.re_add_im (∫ x : E3, F x)]
  rw [h1, h2]
  simp

theorem expIntegral_eq_ofReal_cosIntegral (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
        Complex.exp (Complex.I * (inner ℝ p q : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ))
      = ((∫ p : EuclideanSpace ℝ (Fin 3), fc.f (‖p‖ / κ) * Real.cos (inner ℝ p q) : ℝ) : ℂ) := by
  -- the weight `p ↦ f(‖p‖/κ)` is continuous with compact support (it vanishes for `‖p‖ ≥ 2κ`)
  have hWc : Continuous (fun x : E3 => fc.f (‖x‖ / κ)) :=
    fc.smooth.continuous.comp (by fun_prop)
  have hWsc : HasCompactSupport (fun x : E3 => ((fc.f (‖x‖ / κ) : ℝ) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * κ))
      (isCompact_closedBall 0 (2 * κ)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    apply hx
    have h2 : (2 : ℝ) ≤ ‖x‖ / κ := by rw [le_div_iff₀ hκ]; linarith
    rw [fc.zero _ h2, Complex.ofReal_zero]
  have hcs : HasCompactSupport
      (fun x : E3 => Complex.exp (Complex.I * (inner ℝ x q : ℂ)) * ((fc.f (‖x‖ / κ) : ℝ) : ℂ)) :=
    hWsc.mul_left
  have hI : Integrable
      (fun x : E3 => Complex.exp (Complex.I * (inner ℝ x q : ℂ)) * ((fc.f (‖x‖ / κ) : ℝ) : ℂ)) := by
    have hInner : Continuous (fun x : E3 => inner ℝ x q) := continuous_id.inner continuous_const
    exact ((Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hInner))).mul
      (Complex.continuous_ofReal.comp hWc)).integrable_of_hasCompactSupport hcs
  exact expIntegral_aux (fun x : E3 => fc.f (‖x‖ / κ)) q (fun x => by simp [norm_neg]) hI

end Work.BoseBoxFock.PCFU
