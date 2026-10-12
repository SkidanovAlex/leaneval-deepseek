import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The window-derivative error is bounded by `cnPlus`

The bridge's window error `winErrorQ s Ψ = Σ_i ∫_{abox N s} |∇χ_s(x_i)|²·(Q_iΨ)²`
carries the squared gradient of the window `χ_s` evaluated at the `i`-th particle.
When that gradient is dominated by a constant `B` (the hypothesis `hB`), the whole
error is bounded by `B` times the excited-particle count
`cnPlus s Ψ = Σ_i ∫_{abox N s} (Q_iΨ)²`.

This is a purely measure-theoretic domination: pointwise
`|∇χ_s(x_i)|²·(Q_iΨ)² ≤ B·(Q_iΨ)²` on the box, and the right-hand side is
integrable by `integrableOn_sq_aQ`.  No differentiability of `Ψ` is needed.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.SmallBoxBridge.Position

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Window-error bound.**  If the squared gradient sum of the scaled window
`χ_s` is everywhere at most `B`, then for every continuous `Ψ`

    winErrorQ s Ψ ≤ B · cnPlus s Ψ .

The bound is pointwise in the position variable: for each slot `i` the factor
`Σ_k (∂_kχ_s)(x i)²` is at most `B (x i)`, and `(Q_iΨ)² ≥ 0`, so the integrand
is dominated by `B·(Q_iΨ)²`, whose integral is `B·∫(Q_iΨ)²`. -/
theorem winErrorQ_le_cnPlus {N : ℕ} {s B : ℝ} (hs : 0 < s) (hB0 : 0 ≤ B)
    (hB : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale s) x
        (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ B)
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : Continuous Ψ) :
    Submission.BoseGases.winErrorQ s Ψ ≤ B * Submission.BoseGases.cnPlus s Ψ := by
  unfold Submission.BoseGases.winErrorQ Submission.BoseGases.cnPlus
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- `(Q_iΨ)²` is integrable on the box, hence so is its `B`-multiple.
  have hint : IntegrableOn (fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.aQ s i Ψ x) ^ 2) (Submission.BoseGases.abox N s) volume :=
    Submission.BoseGases.integrableOn_sq_aQ hs i hΨ
  have hBu : IntegrableOn (fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
      B * (Submission.BoseGases.aQ s i Ψ x) ^ 2) (Submission.BoseGases.abox N s) volume :=
    hint.const_mul B
  -- Pointwise domination by `B·(Q_iΨ)²` and integral monotonicity.
  have hmono := integral_mono_of_nonneg
      (μ := volume.restrict (Submission.BoseGases.abox N s))
      (f := fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
        (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale s) (x i)
          (Submission.BoseGases.kcStdBasis k)) ^ 2) * (Submission.BoseGases.aQ s i Ψ x) ^ 2)
      (g := fun x : Fin N → EuclideanSpace ℝ (Fin 3) =>
        B * (Submission.BoseGases.aQ s i Ψ x) ^ 2)
      (Filter.Eventually.of_forall (fun x =>
        mul_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (sq_nonneg _)))
      hBu
      (Filter.Eventually.of_forall (fun x =>
        mul_le_mul_of_nonneg_right (hB (x i)) (sq_nonneg _)))
  rw [integral_const_mul] at hmono
  exact hmono

end Work.SmallBoxBridge.Position
