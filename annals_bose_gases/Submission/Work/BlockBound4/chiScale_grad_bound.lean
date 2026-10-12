import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BlockBound4.chi_fderiv_norm_bound
import Submission.Work.BlockBound4.fderiv_chiScale_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open Submission BoseGases
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The window-gradient constant of `chiScale s`.**  `chiScale s x = chi (s⁻¹ • x)`
(`Submission/KernelIds.lean`, `ChiSmall`/`CubicChi`'s cutoff), so the chain rule
gives `Σ_k (∂_k chiScale s x)² = s⁻² · Σ_k (∂_k chi (s⁻¹•x))²`, and `chi` is
`C^∞` with compact support, hence its gradient-sum is bounded by a universal `K`:

    Σ_k (∂_k chiScale s)(x)² ≤ K / s²      for every `s > 0` and every `x`.

This discharges the hypothesis of `Work.BlockBound4.diagWWord_le_kinWord_gap`
(the `1/s²`-loss of the per-box comparison, paid by the `ε_T`-gap term
`cgap·cnPlus ≥ n₊/(36s²)`).  A witness is `K := sup_x Σ_k(∂_k chi x)²` (or, from
`‖∇chi‖_∞ ≤ chiLip`, `K := 3 * chiLip ^ 2`). -/
theorem chiScale_grad_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : ℝ), 0 < s → ∀ x : EuclideanSpace ℝ (Fin 3),
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ K / s ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := chi_fderiv_norm_bound
  refine ⟨3 * M ^ 2, by positivity, ?_⟩
  intro s hs x
  have hchi_b :
      (∑ k : Fin 3, (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)) ^ 2) ≤ 3 * M ^ 2 := by
    have hterm : ∀ k : Fin 3, (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)) ^ 2 ≤ M ^ 2 := by
      intro k
      have h1 : ‖fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)‖ ≤ M := by
        calc ‖fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)‖
            ≤ ‖fderiv ℝ chi ((s⁻¹) • x)‖ * ‖kcStdBasis k‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * 1 := by
              rw [show ‖kcStdBasis k‖ = 1 from by simp [kcStdBasis]]
              exact mul_le_mul_of_nonneg_right (hM _) (by norm_num)
          _ = M := mul_one _
      calc (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)) ^ 2
          = ‖fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)‖ ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
        _ ≤ M ^ 2 := by nlinarith [norm_nonneg (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k))]
    calc ∑ k : Fin 3, (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)) ^ 2
        ≤ ∑ _k : Fin 3, M ^ 2 := Finset.sum_le_sum (fun k _ => hterm k)
      _ = 3 * M ^ 2 := by simp [Finset.sum_const, Fintype.card_fin]
  calc (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2)
      = (s⁻¹) ^ 2 * (∑ k : Fin 3, (fderiv ℝ chi ((s⁻¹) • x) (kcStdBasis k)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [fderiv_chiScale_apply s x (kcStdBasis k), mul_pow]
    _ ≤ (s⁻¹) ^ 2 * (3 * M ^ 2) := mul_le_mul_of_nonneg_left hchi_b (sq_nonneg _)
    _ = 3 * M ^ 2 / s ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
        ring

end Work.BlockBound4
