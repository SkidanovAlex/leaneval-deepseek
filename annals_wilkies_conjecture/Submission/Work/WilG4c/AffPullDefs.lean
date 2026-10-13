/-
  WilG4c / AffPullDefs — vocabulary for pulling an `Ω`-set back along an affine map.

  Given `c : Fin N → ℝ` and `M : Fin N → Fin N → ℝ`, the map `affPullMap c M` is
  `x ↦ c + M·x` (an arbitrary affine self-map of `ℝ^N`).  Its graph, inside `ℝ^{N+N}` with
  the first `N` coordinates carrying `x` and the last `N` carrying the value, is the set
  `affPullDiag N c M`.  The sum of squares

      `affPullPoly N c M = Σ_i (W_i − c_i − Σ_j M_{ij} X_j)²`

  (with `W` the last-block variables and `X` the first-block variables) has total degree
  `2` uniformly in `N` and cuts out `affPullDiag`.  This is the affine analogue of the
  "substitution atom" `Work.WilG0.diagSet` / `Work.WilG0.diagPoly`, whose degree-2 bound is
  what makes a substitution affordable; here the linear forms `W_i − c_i − Σ_j M_{ij} X_j`
  replace `W_j − X_{ι j}`, and the sum-of-squares form keeps the degree at `2`.

  The two memberships (`affPullDiag` is `Ω` of degree `2`; the projection of
  `liftNM N N X ∩ affPullDiag` is the pullback of `X`) are proved in the sibling modules
  `Submission.Work.WilG4c.AffPullbackDiag` and `Submission.Work.WilG4c.AffPullProject`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilkG4c
open WilkiesDesign

/-- The affine self-map `x ↦ c + M · x` of `ℝ^N`. -/
def affPullMap {N : ℕ} (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => c i + ∑ j : Fin N, M i j * x j

@[simp] theorem affPullMap_apply {N : ℕ} (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ)
    (x : Fin N → ℝ) (i : Fin N) :
    affPullMap c M x i = c i + ∑ j : Fin N, M i j * x j := rfl

/-- The relation set in `ℝ^{N+N}`: the last `N` coordinates are the image of the first `N`
under `affPullMap c M`. -/
def affPullDiag (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) : Set (Fin (N + N) → ℝ) :=
  {v | ∀ i : Fin N, v (Fin.natAdd N i) = c i + ∑ j : Fin N, M i j * v (Fin.castAdd N j)}

/-- Membership in `affPullDiag`, unfolded. -/
theorem mem_affPullDiag {N : ℕ} (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ)
    (v : Fin (N + N) → ℝ) :
    v ∈ affPullDiag N c M ↔
      ∀ i : Fin N, v (Fin.natAdd N i) = c i + ∑ j : Fin N, M i j * v (Fin.castAdd N j) :=
  Iff.rfl

/-- The sum of squares `Σ_i (W_i − c_i − Σ_j M_{ij} X_j)²` cutting out `affPullDiag`. -/
def affPullPoly (N : ℕ) (c : Fin N → ℝ) (M : Fin N → Fin N → ℝ) : MvPolynomial (Fin (N + N)) ℝ :=
  ∑ i : Fin N, (MvPolynomial.X (Fin.natAdd N i) - MvPolynomial.C (c i)
      - ∑ j : Fin N, MvPolynomial.C (M i j) * MvPolynomial.X (Fin.castAdd N j)) ^ 2

end Work.WilkG4c
