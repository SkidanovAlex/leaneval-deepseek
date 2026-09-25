import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one

namespace Work.NN.Core

open scoped NNReal ENNReal
open MeasureTheory Set Filter
open Work.CR.Flat

noncomputable section

/-! ## Auxiliary lemmas: support, continuity and integrability of translated `∂̄`-derivatives -/

/-- The translate `x ↦ ∂̄_j u (w + x)` of a `∂̄`-derivative of a function `u` vanishing off the
ball of radius `R` about the origin has compact support (the ball of radius `R` about `-w`). -/
private lemma hasCompactSupport_dbarCoord_comp_add' {n : ℕ} {u : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → u x = 0) (j : Fin n) (w : Fin n → ℂ) :
    HasCompactSupport (fun x => dbarCoord j u (w + x)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (-w) R) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hcon
  rw [not_le] at hcon
  refine hx (Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp j ?_)
  have : x - (-w) = w + x := by abel
  rwa [this] at hcon

/-- The Bochner–Martinelli kernel is locally integrable, so a continuous compactly supported
function times it is integrable. -/
private lemma integrable_bmKernel_mul_of {n : ℕ} (hn : 0 < n) (k : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) :
    Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel k x * u x) := by
  have h := (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn k)
    |>.integrable_smul_left_of_hasCompactSupport hu hus
  simpa only [smul_eq_mul, mul_comm] using h

/-- Integrability of `x ↦ bmKernel k x · ∂̄_i u (w + x)` for `u` of class `C¹` vanishing off the
ball of radius `R` about the origin. -/
private lemma integrable_bmKernel_mul_dbarCoord_comp_add {n : ℕ} (hn : 0 < n) (k : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → u x = 0) (w : Fin n → ℂ) (i : Fin n) :
    Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel k x * dbarCoord i u (w + x)) :=
  integrable_bmKernel_mul_of hn k
    ((Work.CR.Flat.Cauchy.continuous_dbarCoord hu i).comp (continuous_const.add continuous_id))
    (hasCompactSupport_dbarCoord_comp_add' hsupp i w)

/-- The Bochner–Martinelli divergence formula for a translate: for a `C¹` function `u` vanishing
off the ball of radius `R` about the origin, `Σ_l ∫ bmKernel l x · ∂̄_l u x = bmGamma n · u 0`. -/
private lemma bmKernel_divergence_translate {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → u x = 0) :
    ∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l u x
      = Work.CR.Flat.Cauchy.bmGamma n * u 0 :=
  Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps hn hR hu hsupp
    (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
    (fun ε hε => Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral (ε := ε) hn hR hu hsupp hε)

/-! ## The main lemma -/

theorem bmPotential_dbarDefect_eq {n : ℕ} (hn : 0 < n) {g : Fin n → (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ∀ j, ContDiff ℝ 1 (g j)) (hsupp : ∀ j x, R ≤ ‖x‖ → g j x = 0)
    (i : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.bmPotential
        (fun l w => Work.CR.Flat.dbarCoord i (g l) w - Work.CR.Flat.dbarCoord l (g i) w) z
      = Work.CR.Flat.dbarCoord i (Work.CR.Flat.Cauchy.bmPotential g) z
        - Work.CR.Flat.Cauchy.bmGamma n * g i z := by
  -- integrability of the two pieces of the split integrand
  have hIA : ∀ l : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord i (g l) (z + x)) :=
    fun l => integrable_bmKernel_mul_dbarCoord_comp_add hn l (hg l) (hsupp l) z i
  have hIB : ∀ l : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord l (g i) (z + x)) :=
    fun l => integrable_bmKernel_mul_dbarCoord_comp_add hn l (hg i) (hsupp i) z l
  -- the Bochner–Martinelli divergence formula applied to the translate `y ↦ g i (z + y)`
  have hB : (∑ l : Fin n, ∫ x : Fin n → ℂ,
        Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord l (g i) (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * g i z := by
    have hφ : ContDiff ℝ 1 (fun y : Fin n → ℂ => g i (z + y)) :=
      (hg i).comp (contDiff_const.add contDiff_id)
    have hφs : ∀ x : Fin n → ℂ, R + ‖z‖ ≤ ‖x‖ → g i (z + x) = 0 := by
      intro x hx
      refine hsupp i (z + x) ?_
      have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
        calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
      linarith
    have hk := bmKernel_divergence_translate hn (by positivity : (0 : ℝ) < R + ‖z‖) hφ hφs
    have hk' : (∑ l : Fin n, ∫ x : Fin n → ℂ,
          Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord l (fun y => g i (z + y)) x)
        = Work.CR.Flat.Cauchy.bmGamma n * g i z := by
      simpa using hk
    rw [← hk']
    refine Finset.sum_congr rfl fun l _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Work.CR.Flat.Cauchy.dbarCoord_comp_add l
      (((hg i).differentiable one_ne_zero).differentiableAt)]
  -- the potential of the defect form
  have hL : Work.CR.Flat.Cauchy.bmPotential
        (fun l w => Work.CR.Flat.dbarCoord i (g l) w - Work.CR.Flat.dbarCoord l (g i) w) z
      = ∑ l : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel l x *
          (Work.CR.Flat.dbarCoord i (g l) (z + x) - Work.CR.Flat.dbarCoord l (g i) (z + x)) := by
    rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    simp only [Work.CR.Flat.Cauchy.bmPot]
  -- the `∂̄`-derivative of the potential of `g`
  have hD : Work.CR.Flat.dbarCoord i (Work.CR.Flat.Cauchy.bmPotential g) z
      = ∑ l : Fin n, ∫ x : Fin n → ℂ,
          Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dbarCoord i (g l) (z + x) := by
    rw [show Work.CR.Flat.Cauchy.bmPotential g = Work.CR.Flat.Cauchy.bmPot g from
      funext fun w => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot g w]
    exact Work.CR.Flat.Cauchy.bmPot_dbarCoord hn hg hR hsupp i z
  rw [hL, hD, ← hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← integral_sub (hIA l) (hIB l)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

end

end Work.NN.Core
