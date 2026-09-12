import Submission.Model
import Submission.ModelCore
import Mathlib

/-!
# Uniform local existence of geodesics with prescribed position and velocity

Task: prove the final theorem `uniform_exists_geodesic`.

This is a small variation of `Submission.ModelExists.exists_geodesic` (which treats one
initial condition); here we need the *same* time interval `Ioo (-T) T` to work for all
initial conditions in a closed ball around `(x₀, v₀)`, with continuous-in-data solutions.

## Available facts (all in this Mathlib snapshot)

`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`:

    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t

Apply it to `f := odeField g`, at `x₀ := (x₀, v₀)`, `t₀ := 0`.  From
`Submission.ModelCore.odeField_contDiffAt` we have `ContDiffAt ℝ 1 (odeField g) (x₀, v₀)`.

Then for every `z ∈ closedBall (x₀,v₀) r`, a solution `α : ℝ → E × E` with `α 0 = z` and
`HasDerivAt α (odeField g (α t)) t` on `Ioo (-ε) ε`.  Projecting gives position and velocity:

  let c : ℝ → E := fun t => (α t).1     let vel : ℝ → E := fun t => (α t).2

and then (as in `Submission.ModelExists.exists_geodesic`):
  `HasDerivAt (fun s => (α s).1) (odeField g (α t)).1 t` comes from `hαt.hasFDerivAt.fst.hasDerivAt`
  and `odeField g z = (z.2, accel (g z.1) (fderiv ℝ g z.1) z.2)`, so `(odeField g (α t)).1 = vel t`
  and `(odeField g (α t)).2 = accel (g (c t)) (fderiv ℝ g (c t)) (vel t)` (use `simp [c, vel, odeField]`).

See `Submission/ModelExists.lean` for the exact same extraction pattern (read it!).

Do NOT change the statement of `uniform_exists_geodesic`.  No placeholders/axioms may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Geodesics with prescribed position and velocity exist, uniformly for all data in a small
closed ball, on one common open time interval around `0`. -/
theorem uniform_exists_geodesic (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
    ∃ δ > (0 : ℝ), ∃ T > (0 : ℝ),
      ∀ x ∈ closedBall x₀ δ, ∀ v ∈ closedBall v₀ δ,
        ∃ c : ℝ → E, c 0 = x ∧ ∃ vel : ℝ → E, vel 0 = v ∧
          (∀ t ∈ Ioo (-T) T, HasDerivAt c (vel t) t) ∧
          (∀ t ∈ Ioo (-T) T,
            HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t) := by
  have hF : ContDiffAt ℝ 1 (odeField g) (x₀, v₀) := odeField_contDiffAt g hg hinv x₀ v₀
  rcases ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
    (f := odeField g) (x₀ := (x₀, v₀)) hF 0 with ⟨r, hr, T, hT, H⟩
  refine ⟨r, hr, T, hT, ?_⟩
  intro x hx v hv
  have hmem : (x, v) ∈ Metric.closedBall (x₀, v₀) r := by
    rw [← closedBall_prod_same]
    exact ⟨hx, hv⟩
  rcases H (x, v) hmem with ⟨α, hα0, hα⟩
  let c : ℝ → E := fun t => (α t).1
  let vel : ℝ → E := fun t => (α t).2
  refine ⟨c, ?_, vel, ?_, ?_, ?_⟩
  · simp [c, hα0]
  · simp [vel, hα0]
  · intro t ht
    have hαt := hα t (by simpa using ht)
    have h1 : HasDerivAt (fun s => (α s).1) (odeField g (α t)).1 t := by
      have hf := hαt.hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h1
  · intro t ht
    have hαt := hα t (by simpa using ht)
    have h2 : HasDerivAt (fun s => (α s).2) (odeField g (α t)).2 t := by
      have hf := hαt.hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h2

end

end Submission.Model
