import ChallengeDeps
import Submission.NBody.LocalExistence
import Mathlib

/-!
# Uniqueness of local solutions, and the second-order form

Second stone of the flow chapter.  Having the local solutions, the next ingredient for
continuation is *uniqueness*: on any set of states where the autonomous field
`stateField m` is Lipschitz, two solutions of `z' = stateField m z` that agree at one time agree
on the whole interval (`ODE_solution_unique_of_mem_Ioo`).  The field is locally Lipschitz at every
state with collision-free position (it is `C¹` there, `ContDiffAt.exists_lipschitzOnWith`).

We also record the second-order form of the local solutions: on the interval of existence,
`x'' = ∇ₘ (U m)(x)`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology
open scoped NNReal
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The state field is Lipschitz on a neighbourhood of every state with collision-free position. -/
lemma exists_lipschitzOnWith_stateField (m : Fin N → ℝ)
    (z : EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N)) (hz : WithoutCollisions z.1) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z, LipschitzOnWith L (stateField m) U :=
  (contDiffAt_stateField m z.1 z.2 hz).exists_lipschitzOnWith

/-- **Uniqueness of solutions of the `N`-body system.**  Two solutions whose trajectories lie in a
set on which the state field is Lipschitz, and which agree at one time, agree throughout. -/
theorem stateFlow_unique (m : Fin N → ℝ) {a b t₀ : ℝ} (ht : t₀ ∈ Ioo a b)
    {z₁ z₂ : ℝ → EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N)}
    {C : Set (EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N))} {L : ℝ≥0}
    (hL : LipschitzOnWith L (stateField m) C)
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt z₁ (stateField m (z₁ t)) t ∧ z₁ t ∈ C)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt z₂ (stateField m (z₂ t)) t ∧ z₂ t ∈ C)
    (heq : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => stateField m) (s := fun _ => C) (K := L)
    (fun _ _ => hL) ht h₁ h₂ heq

/-- **Local solutions satisfy the second-order equation**: on the interval of existence,
`x''(t) = ∇ₘ (U m)(x(t))`. -/
theorem exists_local_solution_secondOrder (m : Fin N → ℝ) (x₀ v₀ : EN E N)
    (hx₀ : WithoutCollisions x₀) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EN E N,
      x 0 = x₀ ∧ deriv x 0 = v₀ ∧
        ∀ t ∈ Ioo (-ε) ε, iteratedDeriv 2 x t = weightedGrad m (U m) (x t) := by
  obtain ⟨ε, hε, x, v, hx0, hv0, h⟩ := exists_local_solution m x₀ v₀ hx₀
  refine ⟨ε, hε, x, hx0, ?_, ?_⟩
  · rw [← hv0]
    exact (h 0 (by constructor <;> linarith)).1.deriv
  · intro t ht
    have hone : HasDerivAt x (v t) t := (h t ht).1
    have htwo : HasDerivAt v (weightedGrad m (U m) (x t)) t := (h t ht).2
    -- `deriv x` agrees with `v` near `t`, hence their derivatives agree
    have hev : deriv x =ᶠ[𝓝 t] v := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (h s hs).1.deriv
    have h1 : deriv (deriv x) t = deriv v t := by
      simpa only [iteratedDeriv_one] using hev.iteratedDeriv_eq 1
    have h2 : iteratedDeriv 2 x t = deriv (deriv x) t := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, h1]
    exact htwo.deriv

end Submission.NBody
