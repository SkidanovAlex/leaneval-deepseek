import Submission.Work.FunctionalEquations.Section8ValueDataOfRigidity
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-! ## Summability and bounds for a Dirichlet series with polynomially bounded coefficients -/

private lemma summable_nat_add_one_pow_mul_geometric' {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

/-! ## Closure properties of `TendsToZeroInStrip` -/

lemma TendsToZeroInStrip.add {n : ℕ} [NeZero n] {c : ℝ} {g g' : ℂ → E n → ℂ}
    (hg : TendsToZeroInStrip n c g) (hg' : TendsToZeroInStrip n c g') :
    TendsToZeroInStrip n c (fun τ x => g τ x + g' τ x) := by
  intro x
  obtain ⟨φ, hφ, hb⟩ := hg x
  obtain ⟨φ', hφ', hb'⟩ := hg' x
  refine ⟨fun y => φ y + φ' y, ?_, fun τ hτ h1 h2 => ?_⟩
  · simpa only [add_zero] using hφ.add hφ'
  · rw [add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add (hb τ hτ h1 h2) (hb' τ hτ h1 h2))

lemma TendsToZeroInStrip.congr {n : ℕ} [NeZero n] {c : ℝ} {g g' : ℂ → E n → ℂ}
    (hg : TendsToZeroInStrip n c g) (h : ∀ τ x, 0 < τ.im → g τ x = g' τ x) :
    TendsToZeroInStrip n c g' := by
  intro x
  obtain ⟨φ, hφ, hb⟩ := hg x
  exact ⟨φ, hφ, fun τ hτ h1 h2 => by rw [← h τ x hτ]; exact hb τ hτ h1 h2⟩

private lemma hasDerivAt_gaussianProfile' (c : ℂ) (x : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (c * (r : ℂ) ^ 2))
      (Complex.exp (c * (x : ℂ) ^ 2) * (c * (2 * (x : ℂ)))) x := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) ^ 2) ((2 : ℂ) * (x : ℂ)) x := by
    have h := (hasDerivAt_pow 2 x).ofReal_comp
    simpa using h
  have h2 : HasDerivAt (fun r : ℝ => c * (r : ℂ) ^ 2) (c * ((2 : ℂ) * (x : ℂ))) x :=
    h1.const_mul c
  simpa using h2.cexp

lemma differentiableAt_profile {n : ℕ} [NeZero n] {f : E n → ℂ} (hf : ContDiff ℝ ∞ f) (x : E n) :
    DifferentiableAt ℝ (fun r : ℝ => f (realIncl (n := n) r)) ‖x‖ := by
  have hd : DifferentiableAt ℝ f (realIncl (n := n) ‖x‖) :=
    (hf.differentiable (by simp)).differentiableAt
  exact hd.comp ‖x‖ (Work.Sampling.hasDerivAt_realIncl (n := n) ‖x‖).differentiableAt

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
