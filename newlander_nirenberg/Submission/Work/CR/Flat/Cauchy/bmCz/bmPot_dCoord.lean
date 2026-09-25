/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Differentiating the Bochner–Martinelli potential: the `(1,0)`-derivative

This is the `(1,0)`-analogue of `bmPot_dbarCoord`: the derivative `∂_j = dCoord j` of the
Bochner–Martinelli potential

  `bmPot f z = Σ_k ∫ x, bmKernel k x * f k (z + x)`

may be taken under the integral sign, the singular integral being absolutely convergent because
the `f k` are `C¹` with compact support:

  `dCoord j (bmPot f) z = Σ_k ∫ x, bmKernel k x * dCoord j (f k) (z + x)`.

The proof is a verbatim transcription of the proof of `bmPot_dbarCoord` with the linear
functional `dbarCoordPhi` replaced by its `(1,0)`-counterpart `dCoordPhi`; the only new
ingredients are `dCoord_eq_comp` (the decomposition of `dCoord` through `dCoordPhi`) and the
compatibility `dCoordPhi_precompR` of `dCoordPhi` with the convolution kernel.
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.fderiv_bmPotential
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg

noncomputable section

open scoped NNReal ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy.bmCz

/-! ## The `(1,0)`-derivative as a continuous linear functional -/

/-- The continuous linear map `L ↦ (1/2)(L e_j - i·L(i·e_j))` on `(ℂⁿ →L[ℝ] ℂ)`; composing it
with `fderiv ℝ u` gives `dCoord j u`. -/
noncomputable def dCoordPhi {n : ℕ} (j : Fin n) : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)
      - (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
          (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)))

/-- `dCoord j u = dCoordPhi j ∘ fderiv ℝ u`. -/
lemma dCoord_eq_comp {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.dCoord j u = dCoordPhi j ∘ (fderiv ℝ u) := by
  funext x
  simp only [dCoordPhi, Function.comp_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, Work.CR.Flat.dCoord, ContinuousLinearMap.mul_apply']

/-- `dCoordPhi j` is complex homogeneous: it commutes with the map `b ↦ a * b`. -/
lemma dCoordPhi_comp {n : ℕ} (j : Fin n) (a : ℂ) (b : (Fin n → ℂ) →L[ℝ] ℂ) :
    dCoordPhi j ((ContinuousLinearMap.mul ℝ ℂ a).comp b) = a * dCoordPhi j b := by
  simp only [dCoordPhi, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']
  ring

/-- The same identity for the convolution kernel `L.precompR` attached to multiplication. -/
lemma dCoordPhi_precompR {n : ℕ} (j : Fin n) (a : ℂ) (b : (Fin n → ℂ) →L[ℝ] ℂ) :
    dCoordPhi j
        ((ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ)) a b)
      = a * dCoordPhi j b := by
  rw [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply]
  exact dCoordPhi_comp j a b

/-! ## The main theorem -/

/-- **Differentiating the Bochner–Martinelli potential along `∂`.**  If the components `f k` are
`C¹` and vanish outside the closed ball of radius `R > 0` about the origin, then
`dCoord j (bmPot f) z = Σ_k ∫ x, bmKernel k x * dCoord j (f k) (z + x)`: the `(1,0)`-derivative
may be taken under the integral sign. -/
theorem bmPot_dCoord {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ k : Fin n, ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f k x = 0) (j : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPot f) z
      = ∑ k, ∫ x, Work.CR.Flat.Cauchy.bmKernel k x * Work.CR.Flat.dCoord j (f k) (z + x) := by
  have _hR := hR
  obtain hcs : ∀ k, HasCompactSupport (f k) := fun k => bmPotDbar_hasCompactSupport_of_norm (hsupp k)
  have hcs' : ∀ k, HasCompactSupport (fderiv ℝ (f k)) :=
    fun k => bmPotDbar_hasCompactSupport_fderiv (hcs k)
  have hcont' : ∀ k, Continuous (fderiv ℝ (f k)) :=
    fun k => (hf k).continuous_fderiv (by simp)
  -- `bmPot` is minus a sum of convolutions
  have hbmPot : bmPot f =
      fun w => -∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w := by
    funext w
    rw [← bmPotential_eq_bmPot f w]
    exact congrFun (bmPotential_eq_neg_conv f) w
  -- the derivative of the potential
  have hderiv : HasFDerivAt (bmPot f)
      (-∑ k, (bmKernel k ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
                volume] fderiv ℝ (f k)) z) z := by
    rw [hbmPot]
    refine HasFDerivAt.neg ?_
    have hsum : HasFDerivAt
        (fun w => ∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w)
        (∑ k, (bmKernel k ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
          (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (f k)) z) z := by
      have h := HasFDerivAt.sum (u := Finset.univ) fun k _ =>
        HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
          (hcs k) (locallyIntegrable_bmKernel hn k) (hf k) z
      have hfun : (∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k))
          = fun w => ∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w := by
        funext w
        rw [Finset.sum_apply]
      rw [hfun] at h
      exact h
    exact hsum
  -- the `∂`-derivative of a single convolution
  have hval : ∀ k, dCoordPhi j ((bmKernel k ⋆[
        ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (f k)) z) = -∫ x, bmKernel k x * dCoord j (f k) (z + x) := by
    intro k
    have hInt : MeasureTheory.ConvolutionExistsAt (bmKernel k) (fderiv ℝ (f k)) z
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ)) volume :=
      HasCompactSupport.convolutionExists_right
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
        (hcs' k) (locallyIntegrable_bmKernel hn k) (hcont' k) z
    rw [MeasureTheory.convolution_def]
    rw [← ContinuousLinearMap.integral_comp_comm (dCoordPhi j) hInt]
    have hcongr : (∫ t, dCoordPhi j
          ((ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
            (bmKernel k t) (fderiv ℝ (f k) (z - t))))
        = ∫ t, bmKernel k t * dCoord j (f k) (z - t) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [dCoord_eq_comp, dCoordPhi_precompR, Function.comp_apply]
    rw [hcongr]
    exact bmPotDbar_integral_flip k (dCoord j (f k)) z
  -- assemble
  have hcomp : dCoord j (bmPot f) z = dCoordPhi j (fderiv ℝ (bmPot f) z) := by
    simpa only [Function.comp_apply] using congrFun (dCoord_eq_comp j (bmPot f)) z
  rw [hcomp, hderiv.fderiv]
  simp only [map_neg, map_sum, hval, Finset.sum_neg_distrib, neg_neg]

end Work.CR.Flat.Cauchy.bmCz
