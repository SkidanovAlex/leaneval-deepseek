import ChallengeDeps
import Submission.NBody.Continuation

/-!
# From the first-order flow to `IsNBodySolution`

The flow chapter produces solutions of the first-order system
`x' = v`, `v' = ∇ₘ (U m)(x)`.  The challenge predicate `IsNBodySolution m x` asks for a `C²`
curve `x : ℝ → Eᴺ`, continuous at `0`, with `x''(t) = ∇ₘ (U m)(x(t))` for `t > 0`.

This file records the (obvious) bridge: a curve that is differentiable with derivative the
velocity field `v`, where `v` is `C¹` and satisfies `v' = ∇ₘ (U m)(x)`, is an `N`-body solution,
provided it is continuous at `0`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology
open scoped ContDiff
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- A curve `x` whose derivative is `v`, where `v` is `C¹` and satisfies `v' = ∇ₘ (U m) ∘ x`,
is a solution of the `N`-body problem (as soon as it is continuous at `0`). -/
theorem isNBodySolution_of_hasDerivAt (m : Fin N → ℝ) {x v : ℝ → EN E N}
    (hx : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (weightedGrad m (U m) (x t)) t)
    (hvc : ContDiffOn ℝ 1 v (Ioi (0 : ℝ)))
    (h0 : ContinuousAt x 0) :
    IsNBodySolution m x := by
  have hs : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hdiff : DifferentiableOn ℝ x (Ioi (0 : ℝ)) :=
    fun t ht => (hx t ht).differentiableAt.differentiableWithinAt
  have hderiv' : EqOn (deriv x) v (Ioi (0 : ℝ)) := fun t ht => (hx t ht).deriv
  have hvc' : ContDiffOn ℝ 1 (deriv x) (Ioi (0 : ℝ)) := hvc.congr (fun t ht => hderiv' ht)
  have h2 : ContDiffOn ℝ 2 x (Ioi (0 : ℝ)) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := x) (n := (1 : ℕ∞ω))
      (s := Ioi (0:ℝ)) hs).2 ⟨hdiff, ?_, hvc'⟩
    simp
  refine ⟨h2, h0, ?_⟩
  intro t ht
  have hev : deriv x =ᶠ[𝓝 t] v :=
    Filter.eventuallyEq_of_mem (hs.mem_nhds ht) hderiv'
  have h1 : deriv (deriv x) t = deriv v t := hev.deriv_eq
  have h2' : iteratedDeriv 2 x t = deriv (deriv x) t := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2', h1, (hv t ht).deriv]

end Submission.NBody

namespace Submission.NBody

/-- **An `N`-body solution solves the first-order state equation.**  The state `(x, x')` of an
`N`-body solution satisfies `z' = stateField m z` on `(0,∞)`.  This is the bridge which allows the
flow-theoretic statements (existence, uniqueness, continuation) to be applied to solutions in the
sense of the challenge predicate. -/
theorem hasDerivAt_state_of_isNBodySolution (m : Fin N → ℝ) {x : ℝ → EN E N}
    (hx : IsNBodySolution m x) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    HasDerivAt (fun s : ℝ => (x s, deriv x s)) (stateField m (x t, deriv x t)) t := by
  have h2 := hx.contDiff
  have hderiv1 : ContDiffOn ℝ 1 (deriv x) (Ioi (0 : ℝ)) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hx' : HasDerivAt x (deriv x t) t :=
    ((h2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hdx' : HasDerivAt (deriv x) (weightedGrad m (U m) (x t)) t := by
    have h := ((hderiv1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds ht)).hasDerivAt
    have hiter : deriv (deriv x) t = iteratedDeriv 2 x t := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hiter, hx.eq t ht] at h
    exact h
  have hprod := hx'.prodMk hdx'
  simpa [stateField, Prod.mk.injEq] using hprod

end Submission.NBody
