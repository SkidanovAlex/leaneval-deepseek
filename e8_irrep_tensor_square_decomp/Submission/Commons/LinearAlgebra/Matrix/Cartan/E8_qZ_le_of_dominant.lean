import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique

/-!
# Adding a vector of the dominant cone to a dominant weight does not decrease `qZ`

Weights `v : Fin 8 → ℤ` of `E₈` are written in the fundamental-weight (`ω`) basis, so that the
squared length is `qZ v = v ⬝ A⁻¹ v` (`A = CartanMatrix.E₈`) and the simple-root coordinates are
`coords v = A⁻¹ v`.  A weight is *dominant* when all its `ω`-coordinates are nonnegative.

The main result `Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_le_of_dominant` states that if `x` is
dominant and `y - x` lies in the dominant cone (`coords (y - x) ≥ 0`, i.e. `y - x` is a
nonnegative combination of the simple roots), then `qZ x ≤ qZ y`.

Write `z = y - x`.  Expanding the quadratic form `qZ u = bil u u` in the symmetric bilinear form
`bil u w = u ⬝ A⁻¹ w = u ⬝ coords w` gives

  `qZ y = qZ (x + z) = qZ x + qZ z + 2 · bil x z`.

Both correction terms are nonnegative: `bil x z = ∑ᵢ xᵢ (coords z)ᵢ ≥ 0` (the `ω`-coordinates of the
dominant `x` and the `α`-coordinates of the cone element `z` are both nonnegative), and
`qZ z ≥ 0` because `qZ` is positive semidefinite (`qZ_pos'`, from the positive definiteness
`E8_posDef` of the Cartan matrix).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- `bil` is additive in its first argument. -/
private lemma bil_add_left' (a b w : Fin 8 → ℤ) : bil (a + b) w = bil a w + bil b w := by
  simp only [bil, add_dotProduct]

/-- `bil` is additive in its second argument. -/
private lemma bil_add_right' (a b w : Fin 8 → ℤ) : bil a (b + w) = bil a b + bil a w := by
  simp only [bil, coords_add, dotProduct_add]

/-- Expansion of `qZ` at a sum: `qZ (x + z) = qZ x + qZ z + 2 · bil x z`. -/
private lemma qZ_add' (x z : Fin 8 → ℤ) :
    E8NormTwo.qZ (x + z) = E8NormTwo.qZ x + E8NormTwo.qZ z + 2 * bil x z := by
  rw [qZ_eq_bil, qZ_eq_bil, qZ_eq_bil]
  rw [bil_add_left', bil_add_right', bil_add_right', bil_comm' z x]
  ring

/-- `qZ` is nonnegative (positive semidefinite). -/
private lemma qZ_nonneg' (z : Fin 8 → ℤ) : 0 ≤ E8NormTwo.qZ z := by
  rcases eq_or_ne z 0 with h | h
  · subst h
    simp [E8NormTwo.qZ]
  · exact le_of_lt (qZ_pos' z h)

theorem E8_qZ_le_of_dominant (x y : Fin 8 → ℤ) (hx : ∀ i, 0 ≤ x i) (h : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (y - x) i) : Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ x ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ y := by
  have hy : y = x + (y - x) := by abel
  rw [hy, qZ_add']
  have hcross : 0 ≤ bil x (y - x) := by
    simp only [bil, dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (h i))
  have hz : 0 ≤ E8NormTwo.qZ (y - x) := qZ_nonneg' _
  linarith

end Commons.LinearAlgebra.Matrix.Cartan
