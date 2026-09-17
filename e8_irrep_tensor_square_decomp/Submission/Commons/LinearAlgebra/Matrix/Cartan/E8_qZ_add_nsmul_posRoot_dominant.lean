import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# Adding a nonnegative multiple of a positive root increases `qZ` by at least `2k²`

Let `μ : Fin 8 → ℤ` be a *dominant* weight (all its `ω`-coordinates `μ i` are nonnegative) and let
`α` be a positive root of `E₈` (`α ∈ E8posRoots.P`), i.e. a vector of squared length `qZ α = 2`
whose simple-root coordinates `coords α = A⁻¹ α` are all nonnegative.  Then for every `k : ℕ`

  `qZ μ + 2k² ≤ qZ (μ + k • α)`.

The proof is the binomial expansion of the quadratic form `qZ v = bil v v`, where
`bil v w = v ⬝ A⁻¹ w = v ⬝ coords w` is the symmetric bilinear form of `A⁻¹`:

  `qZ (μ + kα) = qZ μ + 2k·bil μ α + k²·qZ α`.

Since `qZ α = 2` and `bil μ α = ∑ᵢ μᵢ (coords α)ᵢ ≥ 0` (both factors are nonnegative), the
cross term is nonnegative and the claim follows.
-/

/-- `bil` is additive in its first argument. -/
private lemma bil_add_left_aux (a b w : Fin 8 → ℤ) : bil (a + b) w = bil a w + bil b w := by
  simp only [bil, add_dotProduct]

/-- `bil` is additive in its second argument. -/
private lemma bil_add_right_aux (a b w : Fin 8 → ℤ) : bil a (b + w) = bil a b + bil a w := by
  simp only [bil, coords_add, dotProduct_add]

/-- The binomial expansion of `qZ` along a line `μ + k·α`. -/
private lemma qZ_add_zsmul_aux (x y : Fin 8 → ℤ) (c : ℤ) :
    E8NormTwo.qZ (x + c • y)
      = E8NormTwo.qZ x + c * bil x y + c * bil y x + c ^ 2 * E8NormTwo.qZ y := by
  rw [qZ_eq_bil, qZ_eq_bil, qZ_eq_bil]
  rw [bil_add_left_aux, bil_add_right_aux, bil_add_right_aux]
  rw [bil_smul_right, bil_smul_left, bil_smul_left, bil_smul_right]
  ring

theorem E8_qZ_add_nsmul_posRoot_dominant (μ α : Fin 8 → ℤ) (hμ : ∀ i, 0 ≤ μ i) (hα : α ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P) (k : ℕ) : Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ μ + 2 * (k : ℤ) ^ 2 ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ (μ + k • α) := by
  obtain ⟨hqα, -, hcα⟩ := (E8posRoots.memP α).mp hα
  -- rewrite the `ℕ`-scalar as a `ℤ`-scalar
  have hk : (k : ℤ) • α = k • α := by simp
  rw [← hk]
  -- the cross term is nonnegative
  have hb : 0 ≤ bil μ α := by
    simp only [bil, dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (hcα i))
  rw [qZ_add_zsmul_aux, bil_comm' α μ, hqα]
  have hknn : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  nlinarith [mul_nonneg hknn hb]

end Commons.LinearAlgebra.Matrix.Cartan
