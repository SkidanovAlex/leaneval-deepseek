import Mathlib
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.Maximal.opMul_l2_bound
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

set_option linter.unusedVariables false

/-- **Finite families of multipliers with a pointwise square-sum bound.**  If `(Φ i)_{i ∈ t}` are
`L^∞`-symbols whose squared pointwise norms have sum at most `B ^ 2` almost everywhere on the
circle, then the corresponding multiplier operators satisfy the Plancherel (Bessel) bound on
`ℓ²(ℤ)`:
`∑_{i ∈ t} ‖opMul (Φ i) f‖²_{ℓ²} ≤ B ^ 2 ‖f‖²_{ℓ²}`.

This is the `L²`-form of Tao's `ortho-apply`(ii) with the square function of the symbols in place of
the arc-counting bound: it is the identity
`∑_i ‖opMul (Φ i) f‖² = ∫ (∑_i ‖Φ i‖²) ‖𝓕f‖²` (Plancherel, `tsum_norm_sq_opMul_eq_integral`)
followed by the pointwise hypothesis. -/
theorem sum_tsum_norm_sq_opMul_le {ι : Type*} (t : Finset ι)
    (Φ : ι → MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∑ i ∈ t, ‖(Φ i : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2 ≤ B ^ 2)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑ i ∈ t, ∑' n : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul (Φ i) f hf n‖ ^ 2
      ≤ B ^ 2 * ∑' n : ℤ, ‖f n‖ ^ 2 := by
  classical
  -- Integrability of each summand of the pointwise expansion.
  have hInt : ∀ i ∈ t, Integrable (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      ‖(Φ i : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
        * ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2)
      (AddCircle.haarAddCircle (T := 1)) := by
    intro i _
    have h2 : Integrable (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        ‖((Φ i • Work.BourgainPlan.IonescuWainger.ftLp f hf :
            Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2)
        (AddCircle.haarAddCircle (T := 1)) :=
      MemLp.integrable_norm_pow'
        (Lp.memLp (Φ i • Work.BourgainPlan.IonescuWainger.ftLp f hf :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) (p := 2)
    refine h2.congr ?_
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (Φ i)
      (Work.BourgainPlan.IonescuWainger.ftLp f hf)] with ξ hξ
    rw [hξ]
    simp [mul_pow]
  -- Plancherel for each `i`, and the interchange of the finite sum with the integral.
  rw [Finset.sum_congr rfl
    (fun i _ => Work.BourgainPlan.IonescuWainger.tsum_norm_sq_opMul_eq_integral (Φ i) f hf)]
  rw [← integral_finsetSum t hInt]
  -- The pointwise bound coming from the hypothesis.
  have hpt : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      (∑ i ∈ t, ‖(Φ i : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
          * ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
              Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2)
        ≤ B ^ 2 * ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
              Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2 := by
    filter_upwards [h] with ξ hξ
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hξ (sq_nonneg _)
  calc ∫ ξ, (∑ i ∈ t, ‖(Φ i : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
        * ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2)
        ∂(AddCircle.haarAddCircle (T := 1))
      ≤ ∫ ξ, B ^ 2 * ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1)) := by
        refine integral_mono_ae ?_ ?_ hpt
        · refine (integrable_finsetSum' t (fun i hi => hInt i hi)).congr ?_
          filter_upwards with ξ
          simp [Finset.sum_apply]
        · exact ((Lp.memLp (Work.BourgainPlan.IonescuWainger.ftLp f hf)).integrable_norm_pow'
            (p := 2)).const_mul _
    _ = B ^ 2 * ∫ ξ, ‖(Work.BourgainPlan.IonescuWainger.ftLp f hf :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1)) := integral_const_mul _ _
    _ = B ^ 2 * ∑' n : ℤ, ‖f n‖ ^ 2 := by
        rw [← Work.BourgainPlan.IonescuWainger.norm_sq_eq_integral_l2
              (Work.BourgainPlan.IonescuWainger.ftLp f hf),
            ← Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp hf]

end Work.BourgainPlan.Maximal
