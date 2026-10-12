import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseSym.Mollify.cs_ennreal
import Submission.Work.BoseSym.Mollify.eLpNorm_shift_norm_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Mollify.conv_fderiv_le`

The pointwise bound for the gradient of the mollified (convolved) function:

  `‖∇(f ⋆ ρ)(x)‖ ≤ ‖∇f‖_{L²} · ‖ρ‖_{L²}`,

where the convolution is taken with respect to Lebesgue measure on the
configuration space `Conf N = Fin N → EuclideanSpace ℝ (Fin 3)`.

The proof has two ingredients:

* the identity `∇(f ⋆ ρ) = ∇f ⋆ ρ`, which is Mathlib's
  `HasCompactSupport.hasFDerivAt_convolution_left` (this is why we need the
  first factor to be `C¹` with compact support, and why the `L²` norm of `ρ`
  appears on the right);
* the pointwise Cauchy–Schwarz/Young inequality
  `‖u ⋆ v (x)‖ ≤ ‖u‖_{L²} ‖v‖_{L²}`, which lives in
  `Submission.Work.BoseSym.Mollify.cs_ennreal`, together with the translation
  invariance of the `L²` seminorm
  (`Submission.Work.BoseSym.Mollify.eLpNorm_shift_norm_eq`).
-/

namespace Work.BoseSym.Mollify

open MeasureTheory Filter
open scoped Topology Real ContDiff ENNReal NNReal Convolution

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The bilinear map used to write the convolution in the form `∫ t, A t · b t`:
it sends a continuous linear functional `A : Conf N →L[ℝ] ℝ` and a scalar `b`
to the functional `v ↦ A v * b`. -/
def preL (N : ℕ) : (Conf N →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (Conf N →L[ℝ] ℝ) :=
  ContinuousLinearMap.precompL (Conf N) (ContinuousLinearMap.lsmul ℝ ℝ)

/-- The norm of `preL N A b` is `‖A‖ ‖b‖`. -/
lemma norm_preL (N : ℕ) (A : Conf N →L[ℝ] ℝ) (b : ℝ) : ‖preL N A b‖ = ‖A‖ * ‖b‖ := by
  rw [show preL N A b = b • A from by
    ext v; simp [preL, ContinuousLinearMap.precompL_apply, mul_comm]]
  rw [norm_smul, mul_comm]

/-- For a nonnegative real function, `ofReal` of its integral is bounded by the
Lebesgue integral of `ofReal` of the function.  (No integrability hypothesis is
needed: the Bochner integral of a non-integrable function is `0` by
convention.) -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ}
    (hg : 0 ≤ g) : ENNReal.ofReal (∫ a, g a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
  by_cases h : Integrable g μ
  · rw [ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hg)]
  · rw [integral_undef h]
    simp

theorem conv_fderiv_le {N : ℕ} {f ρ : Conf N → ℝ} (hf : Smooth1 f)
    (hcs : HasCompactSupport f) (hρ : Smooth ρ) (hρs : HasCompactSupport ρ)
    (x : Conf N) :
    ‖fderiv ℝ (convC N f ρ) x‖ ≤ (gradNorm N f).toReal * (eLp2 N ρ).toReal := by
  -- `volume` on configuration space is an inner regular Haar measure, hence
  -- invariant under reflection; this is needed to apply the convolution
  -- derivative formula with respect to the *first* argument.  We give the two
  -- instances explicitly because instance search does not find them on its own
  -- (it runs out of its instance budget).
  haveI hIR : (volC N).InnerRegular :=
    Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaCompactSpaceOfBorelSpaceOfSigmaFinite
      (volC N)
  haveI hNI : (volC N).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular (volC N)
  have hli : LocallyIntegrable ρ (volC N) := hρ.continuous.locallyIntegrable
  -- the total derivative of the convolution is the convolution with `∇f`
  have hD : fderiv ℝ (convC N f ρ) x = (fderiv ℝ f ⋆[preL N, volC N] ρ) x :=
    (hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hf hli x).fderiv
  rw [hD]
  -- Cauchy–Schwarz for the convolution and the translation invariance of `eLpNorm`
  have hu_aem : AEMeasurable (fun t : Conf N => ‖fderiv ℝ f t‖) (volC N) :=
    (hf.continuous_fderiv one_ne_zero).norm.aemeasurable
  have hv_aem : AEMeasurable (fun t : Conf N => ‖ρ (x - t)‖) (volC N) :=
    (hρ.continuous.comp (continuous_const.sub continuous_id)).norm.aemeasurable
  have hCS : ENNReal.ofReal ‖∫ t, ‖fderiv ℝ f t‖ * ‖ρ (x - t)‖ ∂(volC N)‖
      ≤ eLpNorm (fun t : Conf N => ‖fderiv ℝ f t‖) 2 (volC N)
        * eLpNorm (fun t : Conf N => ‖ρ (x - t)‖) 2 (volC N) :=
    cs_ennreal (volC N) hu_aem hv_aem
  have hshift : eLpNorm (fun t : Conf N => ‖ρ (x - t)‖) 2 (volC N) = eLpNorm ρ 2 (volC N) :=
    eLpNorm_shift_norm_eq hNI ρ x hρ.continuous.aestronglyMeasurable
  -- the pointwise bound `‖∇(f ⋆ ρ)(x)‖ ≤ ∫ ‖∇f t‖ ‖ρ (x - t)‖`
  have hnorm : ‖(fderiv ℝ f ⋆[preL N, volC N] ρ) x‖
      ≤ ∫ t, ‖fderiv ℝ f t‖ * ‖ρ (x - t)‖ ∂(volC N) := by
    rw [MeasureTheory.convolution_def]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [norm_preL N (fderiv ℝ f t) (ρ (x - t))]
  have hnn : 0 ≤ ∫ t, ‖fderiv ℝ f t‖ * ‖ρ (x - t)‖ ∂(volC N) :=
    integral_nonneg fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- assemble in `ℝ≥0∞`
  have key : ENNReal.ofReal ‖(fderiv ℝ f ⋆[preL N, volC N] ρ) x‖
      ≤ gradNorm N f * eLp2 N ρ := by
    calc ENNReal.ofReal ‖(fderiv ℝ f ⋆[preL N, volC N] ρ) x‖
        ≤ ENNReal.ofReal (∫ t, ‖fderiv ℝ f t‖ * ‖ρ (x - t)‖ ∂(volC N)) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal ‖∫ t, ‖fderiv ℝ f t‖ * ‖ρ (x - t)‖ ∂(volC N)‖ := by
          rw [Real.norm_of_nonneg hnn]
      _ ≤ eLpNorm (fun t : Conf N => ‖fderiv ℝ f t‖) 2 (volC N)
            * eLpNorm (fun t : Conf N => ‖ρ (x - t)‖) 2 (volC N) := hCS
      _ = gradNorm N f * eLp2 N ρ := by
          rw [hshift]
          simp only [gradNorm, eLp2]
  have hgrad_lt : gradNorm N f < ⊤ := by
    have h : MemLp (fun t : Conf N => ‖fderiv ℝ f t‖) 2 (volC N) :=
      MemLp.norm ((hf.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hcs.fderiv ℝ))
    simpa only [gradNorm] using h.eLpNorm_lt_top
  have heLp2_lt : eLp2 N ρ < ⊤ := by
    have h : MemLp ρ 2 (volC N) := hρ.continuous.memLp_of_hasCompactSupport hρs
    simpa only [eLp2] using h.eLpNorm_lt_top
  have hne : gradNorm N f * eLp2 N ρ ≠ ⊤ := (ENNReal.mul_lt_top hgrad_lt heLp2_lt).ne
  calc ‖(fderiv ℝ f ⋆[preL N, volC N] ρ) x‖
      = (ENNReal.ofReal ‖(fderiv ℝ f ⋆[preL N, volC N] ρ) x‖).toReal :=
        (ENNReal.toReal_ofReal (norm_nonneg _)).symm
    _ ≤ (gradNorm N f * eLp2 N ρ).toReal := ENNReal.toReal_mono hne key
    _ = (gradNorm N f).toReal * (eLp2 N ρ).toReal := ENNReal.toReal_mul

end

end Work.BoseSym.Mollify
