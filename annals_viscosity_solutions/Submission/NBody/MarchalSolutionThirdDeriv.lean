import Submission.NBody.MarchalThirdDeriv
import Submission.Commons.Analysis.Calculus.hasDerivAt_euclideanSpace_iff

/-!
# The third derivative of a Newtonian motion

The geometry of the Marchal chapter (F1), eighth layer.  All the blow-up modules
(`MarchalClusterAsymptotic2`, `MarchalClusterBlowUp`, `MarchalClusterCentConf`, …) demand

  `hd3 : ∀ t ∈ (0,ε), HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t`,

i.e. that the acceleration `deriv (deriv x)` is itself differentiable, and no module produced it.
It is a direct consequence of the motion equation: near `t` one has `deriv (deriv x) = ∇_[m] (U m) ∘ x`
(the ODE, differentiable), so the chain rule — here in the coordinatewise form
`hasDerivAt_weightedGrad_coord` plus the Pi-assembly
`Commons.Analysis.Calculus.hasDerivAt_euclideanSpace_iff` — gives the derivative of `deriv (deriv x)`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The acceleration is differentiable on a collision-free Newtonian motion.**  This is the `hd3`
hypothesis of the blow-up modules. -/
theorem hasDerivAt_deriv_deriv_of_solution {m : Fin N → ℝ} {x : ℝ → EN E N} {ε t : ℝ}
    (hmne : ∀ i, m i ≠ 0) (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x s) s)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s)) :
    HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t := by
  have heq : (deriv (deriv x)) =ᶠ[𝓝 t] (fun s : ℝ => ∇_[m] (U m) (x s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [← iteratedDeriv_two_eq_deriv_deriv x s, hode s hs]
  have hcoord : HasDerivAt (fun s : ℝ => ∇_[m] (U m) (x s))
      (WithLp.toLp 2 (fun i : Fin N => ∑ j ∈ Finset.univ.erase i,
        ((m j * (‖x t j - x t i‖ ^ 3)⁻¹) • (deriv x t j - deriv x t i)
        - (3 * (m j * ((‖x t j - x t i‖ ^ 5)⁻¹
            * inner ℝ (x t j - x t i) (deriv x t j - deriv x t i)))) • (x t j - x t i)))) t := by
    refine (Commons.Analysis.Calculus.hasDerivAt_euclideanSpace_iff (E := E) (N := N)).mpr ?_
    intro i
    simp only [WithLp.ofLp_toLp]
    exact hasDerivAt_weightedGrad_coord hmne ht hx hnc i
  have hfinal := hcoord.congr_of_eventuallyEq heq
  exact hfinal.congr_deriv hfinal.deriv.symm

end Submission.NBody
