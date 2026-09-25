import Mathlib
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- The `ℓ²` bound for a Fourier multiplier on `ℤ` whose symbol is pointwise bounded by `μ`: by Plancherel, `Σ_n ‖opMul Φ f hf n‖² ≤ μ² Σ_n ‖f n‖²`.  This is the generic form of the `ℓ²` endpoint of KMSZ §6.1(v) / §6.3 (6.23); the exact identity `Σ_n ‖opMul Φ f hf n‖² = ∫ ‖Φ ξ‖² ‖𝓕f(ξ)‖²` is `Work.BourgainPlan.IonescuWainger.tsum_norm_sq_opMul_eq_integral`. -/
theorem opMul_l2_bound {Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))} {f : ℤ → ℂ}
    (hf : Memℓp f 2) {μ : ℝ} (hμ : 0 ≤ μ)
    (hΦ : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ≤ μ) :
    ∑' n : ℤ, ‖opMul Φ f hf n‖ ^ 2 ≤ μ ^ 2 * ∑' n : ℤ, ‖f n‖ ^ 2 := by
  rw [tsum_norm_sq_opMul_eq_integral Φ f hf]
  -- integrability of the two integrands
  have hInt₁ : Integrable (fun ξ : AddCircle (1:ℝ) =>
      ‖(Φ : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2)
      (AddCircle.haarAddCircle (T := 1)) := by
    have h2 : Integrable (fun ξ : AddCircle (1:ℝ) =>
        ‖((Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2)
        (AddCircle.haarAddCircle (T := 1)) :=
      MemLp.integrable_norm_pow' (Lp.memLp (Φ • ftLp f hf : Lp ℂ 2
        (AddCircle.haarAddCircle (T := 1)))) (p := 2)
    refine h2.congr ?_
    filter_upwards [Lp.coeFn_lpSMul (r := 2) Φ (ftLp f hf)] with ξ hξ
    rw [hξ]
    simp [mul_pow]
  have hInt₂ : Integrable (fun ξ : AddCircle (1:ℝ) =>
      μ ^ 2 * ‖(ftLp f hf : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2) (AddCircle.haarAddCircle (T := 1)) :=
    ((Lp.memLp (ftLp f hf)).integrable_norm_pow' (p := 2)).const_mul _
  calc ∫ ξ, ‖(Φ : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1))
      ≤ ∫ ξ, μ ^ 2 * ‖(ftLp f hf : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1)) := by
        refine integral_mono_ae hInt₁ hInt₂ ?_
        filter_upwards [hΦ] with ξ hξ
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        nlinarith [hξ, norm_nonneg ((Φ : AddCircle (1:ℝ) → ℂ) ξ), hμ]
    _ = μ ^ 2 * ∫ ξ, ‖(ftLp f hf : AddCircle (1:ℝ) → ℂ) ξ‖ ^ 2 ∂(AddCircle.haarAddCircle (T := 1)) :=
        integral_const_mul _ _
    _ = μ ^ 2 * ∑' n : ℤ, ‖f n‖ ^ 2 := by
        rw [← norm_sq_eq_integral_l2 (ftLp f hf), ← tsum_norm_sq_eq_norm_ftLp hf]

end Work.BourgainPlan.Maximal
