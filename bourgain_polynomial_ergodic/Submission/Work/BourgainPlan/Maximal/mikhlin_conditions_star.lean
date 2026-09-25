import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.Thm52

/-- **Transfer of the Mikhlin conditions to the conjugate symbol**: if the compactly supported lift `circleLift ψ` of a circle symbol is `C²` and satisfies the Mikhlin bounds with constant `A`, then the same holds for `circleLift (fun ξ => star (ψ ξ)) = star ∘ circleLift ψ` (conjugation is a real-linear isometry of `ℂ`, so it commutes with `deriv` and `iteratedDeriv 2`). -/
theorem mikhlin_conditions_star {ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ} {A : ℝ}
    (hA : 0 ≤ A) :
    ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift ψ) →
    (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift ψ x‖ ≤ A) →
    (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
    (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift ψ) x‖ ≤ A) →
    ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (fun ξ => star (ψ ξ))) ∧
    (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift (fun ξ => star (ψ ξ)) x‖ ≤ A) ∧
    (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift (fun ξ => star (ψ ξ))) x‖ ≤ A) ∧
    (∀ x : ℝ, |x| ^ 2
      * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift (fun ξ => star (ψ ξ))) x‖ ≤ A) := by
  intro hcont h0 h1 h2
  -- the conjugate symbol's lift is the conjugate of the lift
  have hfun : Work.BourgainPlan.Thm52.circleLift (fun ξ => star (ψ ξ))
      = fun x => star (Work.BourgainPlan.Thm52.circleLift ψ x) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
    · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hx,
        Work.BourgainPlan.Thm52.circleLift_of_mem hx]
    · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hx,
        Work.BourgainPlan.Thm52.circleLift_of_notMem hx, star_zero]
  -- conjugation commutes with `deriv` and with `iteratedDeriv 2`
  have hderiv : deriv (fun x => star (Work.BourgainPlan.Thm52.circleLift ψ x))
      = fun x => star (deriv (Work.BourgainPlan.Thm52.circleLift ψ) x) := deriv.star'
  have hderiv2 : iteratedDeriv 2 (fun x => star (Work.BourgainPlan.Thm52.circleLift ψ x))
      = fun x => star (iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift ψ) x) := by
    funext x
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv.star']
  rw [hfun]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ℂ → ℂ` conjugation is a continuous linear isometry over `ℝ`
    exact (Complex.conjCLE.contDiff).comp hcont
  · intro x; rw [norm_star]; exact h0 x
  · intro x; rw [hderiv, norm_star]; exact h1 x
  · intro x; rw [hderiv2, norm_star]; exact h2 x

end Work.BourgainPlan.Maximal
