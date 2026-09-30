import Mathlib
import Submission.Work.Analysis.ParametricIntegral.contDiff_integral_parametric

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Analysis.Hadamard

open scoped ContDiff
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma two_le_infty : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

lemma minSmoothness_two_le_infty (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] : minSmoothness 𝕜 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_infty

/-- Currying a `2`-multilinear map to a nested continuous linear map. -/
noncomputable def curry₂ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).trans
    (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ))

lemma curry₂_apply (g : E [×2]→L[ℝ] ℝ) (u v : E) : curry₂ E g u v = g ![u, v] := by
  simp only [curry₂, LinearIsometryEquiv.trans_apply, continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply']
  congr 1
  ext i
  fin_cases i <;> simp

/-- Hadamard's bilinear form, as the integral of `(1-t) D²f(tx)`. -/
noncomputable def hadamardB (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  curry₂ E (∫ t in (0:ℝ)..1, (1 - t) • iteratedFDeriv ℝ 2 f (t • x))

lemma hadamardB_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    hadamardB f x u v =
      ∫ t in (0:ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ f) (t • x)) u v) := by
  rw [hadamardB, curry₂_apply, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  rw [ContinuousMultilinearMap.integral_apply]
  · apply integral_congr_ae
    filter_upwards with t
    rw [smul_apply, iteratedFDeriv_two_apply]
    congr 1
  · have h2 : Continuous (iteratedFDeriv ℝ 2 f) :=
      (show ContDiff ℝ ∞ (iteratedFDeriv ℝ 2 f) from by fun_prop).continuous
    have hcont : Continuous
        (fun t : ℝ => (1 - t) • iteratedFDeriv ℝ 2 f (t • x)) := by fun_prop
    have hint : IntervalIntegrable
        (fun t : ℝ => (1 - t) • iteratedFDeriv ℝ 2 f (t • x)) volume 0 1 :=
      hcont.intervalIntegrable 0 1
    have h := intervalIntegrable_iff.mp hint
    rwa [Set.uIoc_of_le zero_le_one] at h

lemma integral_one_sub : (∫ t in (0:ℝ)..1, (1 - t)) = 1/2 := by
  rw [intervalIntegral.integral_sub]
  · rw [integral_one, integral_id]; norm_num
  · exact intervalIntegrable_const
  · exact continuous_id.intervalIntegrable 0 1

lemma contDiff_hadamardB {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hadamardB f) := by
  have h2 : ContDiff ℝ ∞ (iteratedFDeriv ℝ 2 f) := by fun_prop
  have hφ : ContDiff ℝ ∞
      (fun p : ℝ × E => (1 - p.1) • iteratedFDeriv ℝ 2 f (p.1 • p.2)) := by
    have hlin : ContDiff ℝ ∞ (fun p : ℝ × E => p.1 • p.2) := by fun_prop
    have hcomp : ContDiff ℝ ∞ (fun p : ℝ × E => iteratedFDeriv ℝ 2 f (p.1 • p.2)) :=
      h2.comp hlin
    have hscal : ContDiff ℝ ∞ (fun p : ℝ × E => (1 - p.1 : ℝ)) := by fun_prop
    exact hscal.smul hcomp
  have hInt := Work.Analysis.ParametricIntegral.contDiff_integral_parametric hφ 0 1
  have hc : ContDiff ℝ ∞ (fun g : E [×2]→L[ℝ] ℝ => curry₂ E g) := by fun_prop
  change ContDiff ℝ ∞ (fun x : E =>
    curry₂ E (∫ t in (0:ℝ)..1, (1 - t) • iteratedFDeriv ℝ 2 f (t • x)))
  exact hc.comp hInt

lemma hadamardB_zero {f : E → ℝ} (_hf : ContDiff ℝ ∞ f) :
    hadamardB f 0 = (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ f) 0) := by
  have hcurry : curry₂ E (iteratedFDeriv ℝ 2 f 0) = fderiv ℝ (fderiv ℝ f) 0 := by
    ext u v
    rw [curry₂_apply, iteratedFDeriv_two_apply]
    simp
  rw [hadamardB]
  simp only [smul_zero]
  rw [intervalIntegral.integral_smul_const (f := fun t : ℝ => 1 - t)
        (c := iteratedFDeriv ℝ 2 f 0)]
  rw [integral_one_sub, map_smul, hcurry]

open scoped ContDiff in
theorem hadamard_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ B : E → (E →L[ℝ] E →L[ℝ] ℝ), ContDiff ℝ ∞ B ∧
      (∀ x u v, B x u v = B x v u) ∧
      B 0 = (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ f) 0) ∧
      (∀ x, f x - f 0 - (fderiv ℝ f 0) x = B x x x) := by
  refine ⟨hadamardB f, contDiff_hadamardB hf, ?_, hadamardB_zero hf, ?_⟩
  · intro x u v
    rw [hadamardB_apply hf x u v, hadamardB_apply hf x v u]
    apply intervalIntegral.integral_congr
    intro t _
    have hs : IsSymmSndFDerivAt ℝ f (t • x) :=
      ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt) (minSmoothness_two_le_infty ℝ)
    simp only [hs.eq u v]
  · intro x
    rw [hadamardB_apply hf x x x]
    have hkey : f x - f 0 - (fderiv ℝ f 0) x =
        ∫ t in (0:ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ f) (t • x)) x x) := by
      have htay := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := (0 : E))
        (y := x) (n := 1)
        (fun t _ => (hf.contDiffAt (x := 0 + t • x)).of_le two_le_infty)
      rw [Finset.sum_range_succ, Finset.sum_range_one] at htay
      simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
        zero_add, pow_one, Nat.reduceAdd, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
        iteratedFDeriv_two_apply] at htay
      linarith [htay]
    rw [hkey]

end Work.Analysis.Hadamard
