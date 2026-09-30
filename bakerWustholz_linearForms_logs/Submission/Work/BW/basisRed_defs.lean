import Mathlib
import Submission.Work.BW.minkowski_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the basis-reduction lemma (BW, Lemma 4)

This file sets up the vocabulary for `Work.BW.basis_reduction_l1`, which is Lemma 4 of
Baker–Wüstholz, *Logarithmic forms and group varieties*, J. reine angew. Math. **442** (1993),
p. 27–28: a lattice has a basis whose product of successive-minimum-normalised lengths is at
most `n!/2^{n-1}` times the product of the successive minima.

* `Work.BW.wNorm A c` is the weighted `ℓ¹`-norm of the image under `A`: `y ↦ ∑ᵢ cᵢ |(A y)ᵢ|`.
* `Work.BW.IsLatticeNorm F` collects the elementary properties of such a norm that are used:
  positivity, absolute homogeneity, subadditivity, and finiteness of sublevel sets on `ℤⁿ`.
* `Work.BW.succMinL F j` is the `j`-th successive minimum of the lattice `ℤⁿ` with respect to
  the unit ball of `F`, defined by the same `sInf` convention as `Work.BW.succMin`.

Everything is stated for the lattice `ℤⁿ ⊆ ℝⁿ`; the lattice `A ℤⁿ` of the application is
transported along the linear isomorphism given by `A`.
-/

namespace Work.BW

variable {n : ℕ}

/-- The weighted `ℓ¹` norm of the image of `y` under `A`: `y ↦ ∑ᵢ cᵢ |(A y)ᵢ|`. -/
noncomputable def wNorm (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ) : (Fin n → ℝ) → ℝ :=
  fun y => ∑ i, c i * |(A.map (Int.castRingHom ℝ)).mulVec y i|

/-- Properties of a norm-like function on `ℝⁿ` used by the basis reduction: it is nonnegative,
vanishes only at `0`, is absolutely homogeneous, is subadditive, and its sublevel sets on the
lattice `ℤⁿ` are finite. -/
structure IsLatticeNorm (F : (Fin n → ℝ) → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ F x
  eq_zero : ∀ x, F x = 0 ↔ x = 0
  smul : ∀ (t : ℝ) (x : Fin n → ℝ), F (t • x) = |t| * F x
  add_le : ∀ x y, F (x + y) ≤ F x + F y
  finite : ∀ t : ℝ, {v : Fin n → ℤ | F (fun i => (v i : ℝ)) ≤ t}.Finite

/-- The `j`-th successive minimum of the lattice `ℤⁿ` with respect to the unit ball of `F`:
the infimum of the `λ > 0` for which the `ℝ`-span of the lattice points of `F`-norm `≤ λ` has
dimension at least `j`. (The `sInf` convention agrees with `Work.BW.succMin`.) -/
noncomputable def succMinL (F : (Fin n → ℝ) → ℝ) (j : ℕ) : ℝ :=
  sInf {t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ
    {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t})}

end Work.BW
