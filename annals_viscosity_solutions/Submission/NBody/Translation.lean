import ChallengeDeps
import Mathlib

/-!
# Translation invariance of the Newtonian potential

Adding the *same* displacement vector `v : E` to every body (i.e. translating the whole
configuration) does not change any inter-body distance, hence does not change the Newtonian
potential `U m` nor the (total) gradient field `∇ (U m)` on the collision-free domain.  This
is the Galilean-translation symmetry of the `N`-body problem: if `y` is a solution then
`t ↦ y t + (v everywhere)` is again a solution, which is what turns the existence of *one*
hyperbolic motion with prescribed limit shape into the full `theorem_1_1` statement with an
arbitrary initial configuration `x₀`.

This file contains the distance/potential part and the trajectory-level consequences, all fully
proved: translating a solution by a constant displacement keeps it `C²`, continuous at `0` and
gives the same iterated derivatives; the only remaining ingredient for
`isNBodySolution_translate_of_grad_inv` is the invariance of the *gradient field*
`∇ (U m)` under translations, which holds on the collision-free open set and needs the
differentiability of the pairwise terms `x ↦ mᵢ mⱼ ‖xᵢ - xⱼ‖⁻¹` away from collisions.
-/

open ViscositySolutions
open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

local notation "Eᴺ" => EuclideanSpace E (Fin N)

/-- Displace every body by the same vector `v : E`. -/
def shift (v : E) : Eᴺ :=
  WithLp.toLp 2 (fun _ : Fin N => v)

/-- Inter-body distances are translation invariant. -/
lemma r_shift (x : Eᴺ) (v : E) (i j : Fin N) : r ((x + shift v) : Eᴺ) i j = r x i j := by
  simp [r, shift]

/-- The Newtonian potential is translation invariant. -/
lemma U_shift (m : Fin N → ℝ) (x : Eᴺ) (v : E) : U m ((x + shift v) : Eᴺ) = U m x := by
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [r_shift]


/-- Second iterated derivatives are unchanged by adding a constant. -/
lemma iteratedDeriv_two_add_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (s : F) (t : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => f x + s) t = iteratedDeriv 2 f t := by
  have hfunext : (fun x : ℝ => f x + s) = (fun x : ℝ => s + f x) := by
    funext x
    rw [add_comm]
  rw [hfunext]
  exact iteratedDeriv_const_add (n := 2) (by norm_num : 0 < 2) s

/-- `C²` smoothness is preserved under translating the values by a constant. -/
lemma contDiffOn_two_add_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) (s : F) :
    ContDiffOn ℝ 2 (fun t : ℝ => f t + s) (Set.Ioi 0) := by
  simpa [Pi.add_def] using hf.add contDiffOn_const

/-- Continuity at `0` is preserved under translating the values by a constant. -/
lemma continuousAt_add_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContinuousAt f 0) (s : F) :
    ContinuousAt (fun t : ℝ => f t + s) 0 := by
  simpa [Pi.add_def] using hf.add continuousAt_const

/-- Translating a solution by the same displacement of all bodies gives a solution,
provided the gradient field of `U m` is translation invariant (which holds away from
collisions; see the module docstring). -/
lemma isNBodySolution_translate_of_grad_inv (m : Fin N → ℝ) {y : ℝ → Eᴺ}
    (hy : IsNBodySolution m y) (v : E)
    (hgrad : ∀ t > 0, weightedGrad m (U m) ((y t + shift v : Eᴺ)) = weightedGrad m (U m) (y t)) :
    IsNBodySolution m (fun t : ℝ => (y t + shift v : Eᴺ)) where
  contDiff := by
    simpa [Pi.add_def] using contDiffOn_two_add_const hy.contDiff (shift v)
  continuousAt_zero := by
    simpa [Pi.add_def] using continuousAt_add_const hy.continuousAt_zero (shift v)
  eq := by
    intro t ht
    rw [iteratedDeriv_two_add_const (shift v) t, hy.eq t ht]
    exact (hgrad t ht).symm
end Submission.NBody
