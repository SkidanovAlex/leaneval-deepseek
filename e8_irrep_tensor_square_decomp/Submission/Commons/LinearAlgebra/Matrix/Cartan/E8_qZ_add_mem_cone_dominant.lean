import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_add_nsmul_posRoot_dominant

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# `qZ` is superadditive on the dominant cone of `E₈`

Let `A = E₈` be the Cartan matrix and `qZ v = v ⬝ A⁻¹ v` the integral squared length of a weight
`v : Fin 8 → ℤ` (written in the `ω`-basis).  For `x` dominant (all `ω`-coordinates `xᵢ ≥ 0`) and
`c` in the dominant cone (`coords c = A⁻¹ c ≥ 0`),

  `qZ x + qZ c ≤ qZ (x + c)`.

Indeed `qZ v = bil v v` for the symmetric bilinear form `bil v w = v ⬝ coords w`, so

  `qZ (x + c) = qZ x + qZ c + bil x c + bil c x = qZ x + qZ c + 2 · (x ⬝ coords c)`,

and the cross term is a sum of products of nonnegative integers, `xᵢ · (coords c)ᵢ ≥ 0`.
-/

/-- `bil` is additive in its first argument. -/
private lemma qZ_add_bil_add_left (a b w : Fin 8 → ℤ) : bil (a + b) w = bil a w + bil b w := by
  simp only [bil, add_dotProduct]

/-- `bil` is additive in its second argument. -/
private lemma qZ_add_bil_add_right (a b w : Fin 8 → ℤ) : bil a (b + w) = bil a b + bil a w := by
  simp only [bil, coords_add, dotProduct_add]

/-- The quadratic expansion `qZ (x + y) = qZ x + qZ y + bil x y + bil y x`. -/
private lemma qZ_add_expand (x y : Fin 8 → ℤ) :
    E8NormTwo.qZ (x + y) = E8NormTwo.qZ x + E8NormTwo.qZ y + bil x y + bil y x := by
  rw [qZ_eq_bil, qZ_eq_bil, qZ_eq_bil, qZ_add_bil_add_left, qZ_add_bil_add_right,
    qZ_add_bil_add_right]
  ring

/-- The cross term `bil x c = x ⬝ coords c` is nonnegative when `x` is dominant and `c` lies in
the dominant cone. -/
private lemma qZ_add_bil_nonneg (x c : Fin 8 → ℤ) (hx : ∀ i, 0 ≤ x i)
    (hc : ∀ i, 0 ≤ coords c i) : 0 ≤ bil x c := by
  simp only [bil, dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hc i))

theorem E8_qZ_add_mem_cone_dominant (x c : Fin 8 → ℤ) (hx : ∀ i, 0 ≤ x i) (hc : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords c i) : Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ x + Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ c ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ (x + c) := by
  have hexp := qZ_add_expand x c
  have hnn := qZ_add_bil_nonneg x c hx hc
  have hcomm := bil_comm' x c
  linarith

end Commons.LinearAlgebra.Matrix.Cartan
