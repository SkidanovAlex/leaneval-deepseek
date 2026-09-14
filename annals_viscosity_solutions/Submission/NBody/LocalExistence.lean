import ChallengeDeps
import Submission.NBody.Flow
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib

/-!
# Local existence for the `N`-body problem from collision-free data

First stone of the flow chapter proper.  The second-order system `x'' = ∇ₘ (U m)(x)` is written
as the autonomous first-order system

    `stateField z = (z₂, ∇ₘ (U m) z₁)`   on `Eᴺ × Eᴺ`,

which is `C¹` at every state whose position part is collision-free (from `contDiffOn_gradient_U`).
Picard–Lindelöf (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`)
then produces a local solution on an open interval around `0`:

    `∃ ε > 0, ∃ x v : ℝ → Eᴺ,  x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt x (v t) t ∧ HasDerivAt v (∇ₘ (U m)(x t)) t`,

i.e. `x' = v` and `v' = ∇ₘ (U m)(x)`: the second-order equation holds at `0` and on a
neighbourhood of it, with `x` and `v` continuously differentiable.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The autonomous first-order vector field of the `N`-body problem on the state space
`Eᴺ × Eᴺ`: position `x`, velocity `v` evolve by `x' = v`, `v' = ∇ₘ (U m)(x)`. -/
noncomputable def stateField (m : Fin N → ℝ) :
    EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N) →
      EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N) :=
  fun z => (z.2, weightedGrad m (U m) z.1)

/-- The mass-weighted gradient is `C¹` at every collision-free configuration. -/
lemma contDiffOn_weightedGrad_U (m : Fin N → ℝ) :
    ContDiffOn ℝ 1 (fun x : EN E N => (weightedGrad m (U m) x : EN E N))
      {x : EN E N | WithoutCollisions x} := by
  refine contDiffOn_piLp' (p := 2) ?_
  intro i
  have h1 : (fun x : EN E N => (weightedGrad m (U m) x).ofLp i)
      = fun x : EN E N => (m i)⁻¹ • (gradient (U m) x).ofLp i := by
    funext x
    simp [weightedGrad]
  rw [h1]
  exact ContDiffOn.const_smul (𝕜 := ℝ) ((m i)⁻¹)
    (((contDiffOn_piLp (p := 2)).1 (contDiffOn_gradient_U m)) i)

/-- The mass-weighted gradient is `C¹` at a collision-free configuration. -/
lemma contDiffAt_weightedGrad_U (m : Fin N → ℝ) (x₀ : EN E N) (hx₀ : WithoutCollisions x₀) :
    ContDiffAt ℝ 1 (fun x : EN E N => (weightedGrad m (U m) x : EN E N)) x₀ :=
  (contDiffOn_weightedGrad_U m).contDiffAt
    ((isOpen_setOf_withoutCollisions (E := E) (N := N)).mem_nhds hx₀)

/-- The state field is `C¹` at every state with collision-free position. -/
lemma contDiffAt_stateField (m : Fin N → ℝ) (x₀ v₀ : EuclideanSpace E (Fin N))
    (hx₀ : WithoutCollisions x₀) :
    ContDiffAt ℝ 1 (stateField m) (x₀, v₀) := by
  have h1 : ContDiffAt ℝ 1
      (fun z : EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N) => z.2) (x₀, v₀) := contDiffAt_snd
  have h2 : ContDiffAt ℝ 1
      (fun z : EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N) => weightedGrad m (U m) z.1)
      (x₀, v₀) := by
    refine contDiffAt_piLp' (p := 2) ?_
    intro i
    have hcomp : ContDiffAt ℝ 1
        (fun z : EuclideanSpace E (Fin N) × EuclideanSpace E (Fin N) => (gradient (U m) z.1).ofLp i)
        (x₀, v₀) :=
      (((contDiffAt_piLp (p := 2)).1 (contDiffAt_gradient_U m x₀ hx₀)) i).comp (x₀, v₀) contDiffAt_fst
    simpa [weightedGrad] using ContDiffAt.const_smul (𝕜 := ℝ) ((m i)⁻¹) hcomp
  have hp := h1.prodMk h2
  exact hp

/-- **Local existence for the `N`-body problem.**  From any collision-free configuration `x₀`
and any velocity `v₀` there is a local solution of `x' = v`, `v' = ∇ₘ (U m)(x)` on some open
interval `Ioo (-ε) ε` around time `0`. -/
theorem exists_local_solution (m : Fin N → ℝ) (x₀ v₀ : EN E N) (hx₀ : WithoutCollisions x₀) :
    ∃ ε > (0 : ℝ), ∃ x : ℝ → EN E N, ∃ v : ℝ → EN E N,
      x 0 = x₀ ∧ v 0 = v₀ ∧
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt x (v t) t ∧ HasDerivAt v (weightedGrad m (U m) (x t)) t := by
  obtain ⟨r, hr, ε, hε, hsol⟩ :=
    (contDiffAt_stateField m x₀ v₀ hx₀).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨α, hα0, hα⟩ := hsol (x₀, v₀)
    (by simpa [Metric.mem_closedBall] using hr.le)
  refine ⟨ε, hε, fun t : ℝ => (α t).1, fun t : ℝ => (α t).2, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hα0
  · simpa using congrArg Prod.snd hα0
  · intro t ht
    have h := hα t (by simpa using ht)
    constructor
    · have := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t h
      simpa [stateField, Function.comp_def] using this
    · have := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t h
      simpa [stateField, Function.comp_def] using this

end Submission.NBody
