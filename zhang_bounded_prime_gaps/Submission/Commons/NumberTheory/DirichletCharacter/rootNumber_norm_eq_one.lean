import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive
import Submission.Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- **The global root number of a primitive character has modulus one.**
`rootNumber χ = gaussSum χ stdAddChar / I^(if χ.Even then 0 else 1) / N^(1/2)`.
Use `gaussSum_norm_sq_of_isPrimitive` (`‖gaussSum χ stdAddChar‖^2 = (N:ℝ)`, so the
norm is `√N`), `‖(N:ℂ)^(1/2)‖ = √(N:ℝ)` (via
`Complex.norm_natCast_cpow_of_pos` and `Real.sqrt_eq_rpow`), and `‖I‖ = 1`.
-/
theorem rootNumber_norm_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  classical
  -- The Gauss sum of a primitive character has squared norm `N`.
  let τ : ℂ := gaussSum χ (ZMod.stdAddChar (N := N))
  have hτ_sq : ‖τ‖ ^ 2 = (N : ℝ) := by
    simpa [τ] using gaussSum_norm_sq_of_isPrimitive χ hχ
  have hτ : ‖τ‖ = Real.sqrt (N : ℝ) := by
    calc
      ‖τ‖ = Real.sqrt (‖τ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg τ)).symm
      _ = Real.sqrt (N : ℝ) := by rw [hτ_sq]
  -- The Archimedean root-number factor `I ^ (if χ.Even then 0 else 1)` has norm one.
  have hI : ‖I ^ (if χ.Even then 0 else 1)‖ = 1 := by
    rw [norm_pow]
    simp
  -- The factor `N ^ (1 / 2)` has norm `√N`.
  have hNcpow : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt (N : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))]
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N) : 0 < N))
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  -- Combine: the root number is the quotient of these three factors.
  rw [rootNumber]
  rw [norm_div, norm_div]
  rw [hτ, hI, hNcpow]
  field_simp [hsqrt_ne]

end Commons.NumberTheory.DirichletCharacter