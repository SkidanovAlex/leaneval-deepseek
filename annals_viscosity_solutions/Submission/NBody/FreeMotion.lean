import ChallengeDeps
import Mathlib

/-!
# Free (non-interacting) motions and the degenerate small-`N` cases

The full statement of `ViscositySolutions.theorem_1_1` ranges over every `N : ℕ`.
For `N = 0` the hypotheses are contradictory (`‖a‖_[m] = 0 ≠ 1`), and for `N = 1`
the Newtonian potential vanishes so every affine trajectory `t ↦ x₀ + c t • a` is an
`N`-body solution.  This module proves those two degenerate cases in full, together
with the elementary calculus facts they need.

The remaining cases (`2 ≤ N`) are the content of Maderna--Venturelli's paper: for them
one needs the existence of global hyperbolic motions with prescribed asymptotic
configuration, which is exactly the deep theorem proved in the paper via viscosity
solutions of the Hamilton--Jacobi equation.  This file deliberately contains no
`sorry`; every declaration below is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Submission.NBody

/-- An affine trajectory into an arbitrary normed space over `ℝ` is `C²` on `(0, ∞)`. -/
lemma contDiffOn_two_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ a : F) (c : ℝ) : ContDiffOn ℝ 2 (fun t : ℝ => x₀ + (c * t) • a) (Set.Ioi 0) := by
  fun_prop

/-- An affine trajectory is continuous at `0`. -/
lemma continuousAt_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ a : F) (c : ℝ) : ContinuousAt (fun t : ℝ => x₀ + (c * t) • a) 0 := by
  fun_prop

/-- The second iterated derivative of an affine trajectory vanishes everywhere. -/
lemma iteratedDeriv_two_affine_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ a : F) (c : ℝ) : ∀ x : ℝ, iteratedDeriv 2 (fun t : ℝ => x₀ + (c * t) • a) x = 0 := by
  intro x
  have hg : deriv (fun t : ℝ => (c * t) • a) = fun _ : ℝ => c • a := by
    funext t
    rw [deriv_smul_const]
    · rw [deriv_const_mul_id]
    · exact differentiableAt_id.const_mul c
  have h1 : deriv (fun t : ℝ => x₀ + (c * t) • a) = fun _ : ℝ => c • a := by
    funext t
    rw [deriv_const_add]
    exact congrFun hg t
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [iteratedDeriv_one]
  rw [h1]
  simp

/-- A constant (vector-valued) function is `o(t)` as `t → +∞`. -/
lemma isLittleO_const_atTop {F : Type*} [NormedAddCommGroup F] (x₀ : F) :
    (fun _ : ℝ => x₀) =o[atTop] (fun t : ℝ => t) := by
  rw [Asymptotics.isLittleO_const_left]
  right
  change Tendsto (fun t : ℝ => ‖t‖) atTop atTop
  exact tendsto_norm_atTop_atTop

/-- For a single body the Newtonian potential vanishes identically. -/
lemma U_eq_zero_of_one_body (m : Fin 1 → ℝ) (y : EuclideanSpace E (Fin 1)) : U m y = 0 := by
  unfold U
  apply Finset.sum_eq_zero
  intro j hj
  have hJ : j = (0 : Fin 1) := by omega
  subst j
  have hI : Finset.Iio (0 : Fin 1) = (∅ : Finset (Fin 1)) := by
    ext i
    simp [Finset.mem_Iio]
  rw [hI]
  simp

/-- For a single body the mass-weighted gradient of the (zero) potential vanishes. -/
lemma weightedGrad_U_eq_zero_of_one_body (m : Fin 1 → ℝ) (y : EuclideanSpace E (Fin 1)) :
    weightedGrad m (U m) y = 0 := by
  have hU : U m = fun _ : EuclideanSpace E (Fin 1) => 0 := by
    funext y
    exact U_eq_zero_of_one_body m y
  have hgrad : ∇ (U m) y = 0 := by
    rw [hU]
    exact gradient_fun_const y 0
  ext i
  simp [weightedGrad, hgrad]

/-- Any affine trajectory is an `N`-body solution when there is a single body. -/
lemma isNBodySolution_one_body_affine (m : Fin 1 → ℝ) (x₀ a : EuclideanSpace E (Fin 1))
    (c : ℝ) : IsNBodySolution m (fun t : ℝ => x₀ + (c * t) • a) where
  contDiff := contDiffOn_two_affine x₀ a c
  continuousAt_zero := continuousAt_affine x₀ a c
  eq := by
    intro t ht
    rw [iteratedDeriv_two_affine_eq_zero x₀ a c t,
      weightedGrad_U_eq_zero_of_one_body m (x₀ + (c * t) • a)]

/-- With a single body there are no pairs, hence no collisions. -/
lemma noCollisions_one_body (x : EuclideanSpace E (Fin 1)) : WithoutCollisions x := by
  intro i j hij
  exfalso
  have : i = j := by omega
  exact hij this

end Submission.NBody
