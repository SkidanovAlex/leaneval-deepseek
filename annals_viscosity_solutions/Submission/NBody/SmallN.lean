import ChallengeDeps
import Submission.NBody.FreeMotion

/-!
# The degenerate instances `N = 0` and `N = 1` of `theorem_1_1`

`theorem_1_1` is quantified over all `N : ℕ`.  This file proves the full statement of
`ViscositySolutions.theorem_1_1` in the cases `N = 0` and `N = 1` (and hence for `N ≤ 1`).

* `N = 0`: the hypothesis `‖a‖_[m] = 1` is contradictory because the empty sum is `0`.
* `N = 1`: the potential `U m` vanishes, so the affine (free) trajectory
  `t ↦ x₀ + (sqrt (2*h) * t) • a` is a global `N`-body solution without collisions whose
  remainder `o t := x₀` is `o(t)` as `t → ∞`.

For `2 ≤ N` one needs the deep existence theorem of Maderna--Venturelli (viscosity
solutions of the Hamilton--Jacobi equation), which is not developed here.
-/

open ViscositySolutions
open Filter Gradient Real Set

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

local notation "ℝᴺ" => Fin N → ℝ

local notation "Eᴺ" => EuclideanSpace E (Fin N)

/-- `theorem_1_1` for `N = 0`: the normalisation hypothesis is contradictory. -/
theorem theorem_1_1_of_eq_zero (hE : 2 ≤ Module.finrank ℝ E) (m : Fin 0 → ℝ)
    (hm : ∀ i : Fin 0, 0 < m i) (x₀ a : EuclideanSpace E (Fin 0))
    (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → EuclideanSpace E (Fin 0),
      ∃ o : ℝ → EuclideanSpace E (Fin 0),
        (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
          IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
            ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  exfalso
  have hzero : ‖a‖_[m] = 0 := by
    simp [weightedNorm]
  have hbad : (0 : ℝ) = 1 := by
    simpa [hzero] using a_norm
  norm_num at hbad

/-- `theorem_1_1` for `N = 1`: the single body moves freely along a straight line. -/
theorem theorem_1_1_of_eq_one (hE : 2 ≤ Module.finrank ℝ E) (m : Fin 1 → ℝ)
    (hm : ∀ i : Fin 1, 0 < m i) (x₀ a : EuclideanSpace E (Fin 1))
    (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → EuclideanSpace E (Fin 1),
      ∃ o : ℝ → EuclideanSpace E (Fin 1),
        (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
          IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
            ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  refine ⟨fun t => x₀ + (sqrt (2 * h) * t) • a, fun _ => x₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact isLittleO_const_atTop x₀
  · simp
  · exact isNBodySolution_one_body_affine m x₀ a (sqrt (2 * h))
  · intro t ht
    exact noCollisions_one_body (x₀ + (sqrt (2 * h) * t) • a)
  · intro t ht
    rw [add_comm]

/-- `theorem_1_1` for `N ≤ 1`, by splitting into `N = 0` and `N = 1`. -/
theorem theorem_1_1_of_le_one (hE : 2 ≤ Module.finrank ℝ E) (hN : N ≤ 1) (m : ℝᴺ)
    (hm : ∀ i : Fin N, 0 < m i) (x₀ a : Eᴺ) (a_nc : WithoutCollisions a)
    (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → Eᴺ, ∃ o : ℝ → Eᴺ, (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  have hN0 : N = 0 ∨ N = 1 := by omega
  rcases hN0 with hN0 | hN0
  · subst N
    exact theorem_1_1_of_eq_zero hE m hm x₀ a a_nc a_norm h h_pos
  · subst N
    exact theorem_1_1_of_eq_one hE m hm x₀ a a_nc a_norm h h_pos

end Submission.NBody
