import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein lift is equivariant under the diagonal Lorentz matrices of sign changes

The diagonal matrices `diag(ε)` with `ε i = ±1` are the Lorentz transformations of `ℝ^{1,4}` that
change the signs of the space-like coordinates of the Klein model.  This file records the
corresponding equivariance of the Klein lift `y ↦ (y,1)/√(1-|y|²)`:

`hypOfKlein (rot4 (diagonal ε) y) = blockLast (diagonal ε) *ᵥ hypOfKlein y`.

Everything is a coordinate computation.  The only non-trivial input is that a sign change of the
coordinates of `E4` preserves the norm, so the normalising factor `(√(1-|y|²))⁻¹` is unchanged;
after that the identity is `ε i * (ε i * x) = x` and the diagonal ↔ block-diagonal bookkeeping of
`blockLast`.

## Main results

* `Work.HypModel.blockLast_diagonal` : `blockLast (diagonal ε)` is the diagonal `5 × 5` matrix with
  entries `ε 0, ε 1, ε 2, ε 3, 1`.
* `Work.HypModel.hypOfKlein_diagonal` : the equivariance of `hypOfKlein`.
-/

noncomputable section

open scoped Matrix InnerProductSpace
open Matrix

namespace Work.HypModel

/-- `rot4` of a diagonal matrix is the componentwise multiplication by `ε`. -/
theorem rot4_diagonal (ε : Fin 4 → ℝ) (y : E4) :
    rot4 (Matrix.diagonal ε) y = fun i => ε i * y i := by
  ext i
  fin_cases i <;> simp [rot4, Matrix.diagonal_apply]

/-- A sign change of the coordinates of `E4` preserves the norm: the two normalising factors of
`hypOfKlein` agree. -/
theorem one_sub_norm_sq_rot4_diagonal (ε : Fin 4 → ℝ) (hε : ∀ i, ε i ^ 2 = 1) (y : E4) :
    (1 : ℝ) - ‖rot4 (Matrix.diagonal ε) y‖ ^ 2 = 1 - ‖y‖ ^ 2 := by
  have h1 : ‖rot4 (Matrix.diagonal ε) y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_eq_dotProduct,
      inner_eq_dotProduct, rot4_diagonal]
    simp only [dotProduct, Fin.sum_univ_four]
    nlinarith [hε 0, hε 1, hε 2, hε 3]
  rw [h1]

/-- `blockLast` of a diagonal `4 × 4` matrix is the diagonal `5 × 5` matrix with the same diagonal
entries, completed by `1` in the last place. -/
theorem blockLast_diagonal (ε : Fin 4 → ℝ) :
    blockLast (Matrix.diagonal ε) =
      Matrix.diagonal (fun i : Fin 5 => if h : (i : ℕ) < 4 then ε ⟨i, h⟩ else 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hi : (i : ℕ) < 4 <;> simp [blockLast, hi]
  · by_cases hi : (i : ℕ) < 4
    · by_cases hj : (j : ℕ) < 4
      · have hne : (⟨i, hi⟩ : Fin 4) ≠ ⟨j, hj⟩ :=
          fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh))
        simp [blockLast, hi, hj, h, hne]
      · simp [blockLast, hi, hj, h]
    · by_cases hj : (j : ℕ) < 4
      · simp [blockLast, hi, hj, h]
      · exfalso; omega

/-- **The Klein lift is equivariant under diagonal Lorentz matrices of sign changes.**  For
`ε : Fin 4 → ℝ` with `ε i = ±1` (recorded as `ε i ^ 2 = 1`) and every `y : E4`,
`hypOfKlein (rot4 (diagonal ε) y) = blockLast (diagonal ε) *ᵥ hypOfKlein y`. -/
theorem hypOfKlein_diagonal (ε : Fin 4 → ℝ) (hε : ∀ i, ε i ^ 2 = 1) (y : E4) :
    hypOfKlein (rot4 (Matrix.diagonal ε) y) = (blockLast (Matrix.diagonal ε)).mulVec (hypOfKlein y) := by
  have hs' : (Real.sqrt (1 - ‖rot4 (Matrix.diagonal ε) y‖ ^ 2))⁻¹ =
      (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ := by
    rw [one_sub_norm_sq_rot4_diagonal ε hε y]
  rw [blockLast_diagonal ε]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec_diagonal, hypOfKlein, ray, rot4_diagonal, hs'] <;>
    ring

end Work.HypModel
