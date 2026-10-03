import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Inner product against a real multiple of `‖v‖ ^ (p - 2) • v`

For a complex inner product space `H`, a vector `v : H` and reals `p > 1`, `c`,
we compute
`⟪v, c • (‖v‖ ^ (p - 2) • v)⟫ = ↑(c * ‖v‖ ^ p)`.
-/

namespace Commons.Analysis.InnerProductSpace

theorem inner_smul_rpow_smul_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) {p c : ℝ} (hp : 1 < p) : inner ℂ v (c • ((‖v‖ ^ (p - 2)) • v)) = ((c * ‖v‖ ^ p : ℝ) : ℂ) := by
  -- `‖v‖ ^ p = ‖v‖ ^ (p - 2) * ‖v‖ ^ 2`, valid also at `‖v‖ = 0` since `p ≠ 0`.
  have hx : ‖v‖ ^ p = ‖v‖ ^ (p - 2) * ‖v‖ ^ 2 := by
    have h : ‖v‖ ^ ((p - 2) + 2) = ‖v‖ ^ (p - 2) * ‖v‖ ^ (2 : ℝ) :=
      Real.rpow_add' (norm_nonneg v) (by linarith)
    rw [show (p - 2) + 2 = p by ring, Real.rpow_two] at h
    exact h
  -- `⟪v, v⟫ = ↑(‖v‖ ^ 2)` as a complex number.
  have hvv : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rfl
  -- Push the real scalar multiplications inside and use `inner_smul_right`.
  rw [← Complex.coe_smul, inner_smul_right]
  rw [← Complex.coe_smul, inner_smul_right, hvv]
  rw [hx, Complex.ofReal_mul, Complex.ofReal_mul]

end Commons.Analysis.InnerProductSpace