import ChallengeDeps
import Submission.NBody.FreeMotion
import Submission.NBody.Force
import Submission.NBody.Translation
import Mathlib

/-!
# Translation invariance of the force field, and its use in `theorem_1_1`

The Newtonian potential `U m` is invariant under translating the whole configuration
(`U_shift`).  Using the explicit per-coordinate force identity `gradient_U_coord`, the
*gradient field* `∇(U m)` (hence the mass-weighted field `∇ₘ (U m)`, the right-hand side of
Newton's equations) is invariant as well, on the collision-free domain.

Consequently any `N`-body solution can be translated by a constant displacement and remains a
solution, and the existence question in `theorem_1_1` reduces to the existence of *one*
hyperbolic motion with the prescribed limit shape: the arbitrary initial condition `x₀` is
then absorbed by a translation (which does not change the asymptotic behaviour).

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Component computation for a translated configuration. -/
lemma add_shift_apply (x : EN E N) (v : E) (k : Fin N) :
    (x + shift v : EN E N) k = x k + v := by
  simp [shift]

/-- Uniform displacements add. -/
lemma shift_add (v w : E) : (shift v + shift w : EN E N) = shift (v + w) := by
  ext k
  simp [shift]

/-- A uniform displacement by `-v` undoes one by `v`. -/
lemma shift_add_neg (v : E) : (shift v + shift (-v) : EN E N) = 0 := by
  rw [shift_add]
  ext k
  simp [shift]

/-- Translating the whole configuration keeps it collision-free. -/
lemma withoutCollisions_shift (x : EN E N) (v : E) (hx : WithoutCollisions x) :
    WithoutCollisions ((x + shift v : EN E N)) := by
  intro i j hij
  rw [r_shift x v i j]
  exact hx i j hij

/-- The gradient field of the Newtonian potential is translation invariant on the
collision-free domain. -/
lemma gradient_U_shift (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) (v : E) :
    gradient (U m) ((x + shift v : EN E N)) = gradient (U m) x := by
  have hx' : WithoutCollisions ((x + shift v : EN E N)) := withoutCollisions_shift x v hx
  ext k
  rw [gradient_U_coord m ((x + shift v : EN E N)) hx' k, gradient_U_coord m x hx k]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : (x + shift v : EN E N) j = x j + v := add_shift_apply x v j
  have hk1 : (x + shift v : EN E N) k = x k + v := add_shift_apply x v k
  rw [hj1, hk1]
  have hdiff : x j + v - (x k + v) = x j - x k := by abel
  rw [hdiff]

/-- The mass-weighted gradient field (`∇ₘ (U m)`, the right-hand side of Newton's equations)
is translation invariant on the collision-free domain. -/
lemma weightedGrad_U_shift (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) (v : E) :
    weightedGrad m (U m) ((x + shift v : EN E N)) = weightedGrad m (U m) x := by
  ext k
  simp only [weightedGrad]
  rw [gradient_U_shift m x hx v]

/-- Translating a solution by a common displacement of all bodies produces another solution. -/
lemma isNBodySolution_shift (m : Fin N → ℝ) {y : ℝ → EN E N} (hy : IsNBodySolution m y)
    (hnc : ∀ t > 0, WithoutCollisions (y t)) (v : E) :
    IsNBodySolution m (fun t : ℝ => (y t + shift v : EN E N)) :=
  isNBodySolution_translate_of_grad_inv m hy v
    (fun t ht => weightedGrad_U_shift m (y t) (hnc t ht) v)

/-- **Invariance of `theorem_1_1` under uniform translation of the initial configuration.**
If the statement holds for the initial configuration `x₀ + shift v`, then it holds for `x₀`:
translate the motion back by `-v` (a constant remainder, hence still `o(t)`). -/
theorem theorem_1_1_shift_x₀ (hE : 2 ≤ Module.finrank ℝ E) (m : Fin N → ℝ) (x₀ a : EN E N)
    (h : ℝ) (v : E)
    (H : ∃ x : ℝ → EN E N, ∃ o : ℝ → EN E N, (o =o[atTop] fun t ↦ t) ∧
      x 0 = (x₀ + shift v : EN E N) ∧ IsNBodySolution m x ∧
        (∀ t > 0, WithoutCollisions (x t)) ∧
          ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t) :
    ∃ x : ℝ → EN E N, ∃ o : ℝ → EN E N, (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  obtain ⟨x, o, ho, hx0, hx, hnc, hasym⟩ := H
  refine ⟨fun t : ℝ => (x t + shift (-v) : EN E N),
    fun t : ℝ => o t + shift (-v), ?_, ?_, ?_, ?_, ?_⟩
  · have hconst : (fun _ : ℝ => shift (-v) : ℝ → EN E N) =o[atTop] fun t ↦ t :=
      isLittleO_const_atTop (shift (-v))
    simpa using ho.add hconst
  · -- `(x 0 + shift (-v)) = x₀`
    change x 0 + shift (-v) = x₀
    rw [hx0]
    have hcomp : ((x₀ + shift v : EN E N) + shift (-v) : EN E N) = x₀ := by
      rw [add_assoc, shift_add_neg, add_zero]
    exact hcomp
  · exact isNBodySolution_shift m hx hnc (-v)
  · intro t ht
    exact withoutCollisions_shift (x t) (-v) (hnc t ht)
  · intro t ht
    have hy' := hasym t ht
    calc (x t + shift (-v) : EN E N)
        = ((sqrt (2 * h) * t) • a + o t) + shift (-v) := by rw [hy']
      _ = (sqrt (2 * h) * t) • a + (o t + shift (-v)) := by abel

end Submission.NBody
