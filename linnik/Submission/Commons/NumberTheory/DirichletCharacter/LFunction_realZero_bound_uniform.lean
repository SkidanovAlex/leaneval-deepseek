import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform

/-!
# Uniform real-zero bound for quadratic Dirichlet `L`-functions

This is the "Siegel zero bound" in the shape needed downstream: for every real (quadratic)
primitive non-principal Dirichlet character `χ` modulo `N` and every real zero `β ∈ (0,1)` of
`L(s, χ)`,

  `c / N ^ K ≤ 1 - β`

with *absolute* constants `c > 0`, `K > 0` (i.e. independent of `χ` and `N`).

The uniform form with an arbitrary exponent `ε > 0` in place of `K`,

  `∀ ε > 0, ∃ C > 0, ∀ χ, β, L(β,χ) = 0 → C * N ^ (-ε) ≤ 1 - β`,

is Siegel's theorem and has already been established by the team in the shared commons as
`LFunction_realZero_siegel_uniform` (via Estermann's positivity method: if some quadratic
character has a zero close to `1`, then `‖L(1,χ)‖` cannot be too small for any other quadratic
character).  The statement requested here is the specialisation `ε = 1`, which is the form used
by the analytic part of Chen's theorem.
-/

namespace Commons.NumberTheory.DirichletCharacter

/-- **Uniform bound for the real zeros of `L(s, χ)` for quadratic `χ`.**

There are absolute constants `c > 0` and `K > 0` such that every real zero `β ∈ (0,1)` of
`L(s, χ)`, for `χ` a primitive non-principal Dirichlet character of modulus `N` with
`χ * χ = 1`, satisfies `c / N ^ K ≤ 1 - β`.

This is deduced from the sharper uniform Siegel bound
`LFunction_realZero_siegel_uniform` (which permits an arbitrary exponent `ε > 0`), applied
with `ε = 1`. -/
theorem LFunction_realZero_bound_uniform :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        c / (N : ℝ) ^ K ≤ 1 - β := by
  obtain ⟨C, hCpos, hC⟩ :=
    LFunction_realZero_siegel_uniform 1 (by norm_num)
  refine ⟨C, hCpos, 1, one_pos, ?_⟩
  intro N _ χ hχprim hχne hχsq β hβ0 hβ1 hz
  have h := hC N χ hχprim hχne hχsq β hβ0 hβ1 hz
  rw [Real.rpow_one, div_eq_mul_inv]
  rwa [Real.rpow_neg_one] at h

end Commons.NumberTheory.DirichletCharacter
