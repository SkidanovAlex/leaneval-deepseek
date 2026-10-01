import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess

/-!
# The imprimitive `L`-function is the primitive one times the local factors at `p | q`

For a non-principal Dirichlet character `χ` of level `q`, with conductor `q₀ = χ.conductor` and
primitive character `χ₀ = χ.primitiveCharacter`, Mathlib's
`DirichletCharacter.LFunction_changeLevel` — applied to the identity
`χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter` — gives the exact factorisation

`L(s, χ) = L(s, χ₀) · ∏_{p | q} (1 - χ₀(p) p^{-s})`,

the product running over the primes dividing the level.  On the critical line `Re s = 1/2` each
local factor is bounded by `‖1 - χ₀(p) p^{-s}‖ ≤ 1 + p^{-1/2}`, and the divergence of
`∏_{p | q} (1 + p^{-1/2})` is at most `q^o(1)` — indeed `≤ C_δ q^δ` for every `δ > 0` — because the
number of prime factors of `q` is controlled by the divisor bound.

Both ingredients are already available in the workspace:

* `Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le` — the factorisation
  together with the pointwise local bound `‖1 - χ₀(p) p^{-s}‖ ≤ 1 + p^{-σ}` for `σ = Re s ≥ 1/2`;
* `Commons.NumberTheory.DirichletCharacter.prod_primeFactors_one_add_rpow_le'` — the bound
  `∏_{p | q} (1 + p^{-σ}) ≤ C_δ q^δ` for `σ ≥ 1/2` and every `δ > 0`.

The lemma below simply specialises the second estimate to `δ = 1/24` and `σ = 1/2`, which is the
statement the critical-line bound for imprimitive characters consumes.
-/

namespace Work.Sieve

open DirichletCharacter

/-- **The imprimitive factor.**  There is an absolute constant `C` with
`‖L(1/2 + it, χ)‖ ≤ C q^{1/24} ‖L(1/2 + it, χ.primitiveCharacter)‖`
for every non-principal Dirichlet character `χ` of level `q`. -/
theorem LFunction_imprimitive_factor :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → ∀ t : ℝ,
      ‖DirichletCharacter.LFunction χ ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (q : ℝ) ^ ((1 : ℝ) / 24)
            * ‖DirichletCharacter.LFunction χ.primitiveCharacter
                ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  -- the product bound over the prime factors of the level, with `σ = 1/2` and `δ = 1/24`
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.prod_primeFactors_one_add_rpow_le'
      (σ := (1 : ℝ) / 2) (by norm_num) (δ := (1 : ℝ) / 24) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro q _instq χ _hcond hχ t
  -- the two points `↑(1/2)` and `1/2` of `ℂ` agree
  have hcast : (((1 : ℝ) / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by simp
  -- factorisation of the imprimitive `L`-function plus the pointwise local bounds
  have hred :=
    Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le χ hχ
      (σ := (1 : ℝ) / 2) (by norm_num) (t := t)
  rw [hcast] at hred
  have hprod : (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-((1 : ℝ) / 2))))
      ≤ C * (q : ℝ) ^ ((1 : ℝ) / 24) := hC q (NeZero.ne q)
  calc ‖DirichletCharacter.LFunction χ ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-((1 : ℝ) / 2))))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := hred
    _ ≤ (C * (q : ℝ) ^ ((1 : ℝ) / 24))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = C * (q : ℝ) ^ ((1 : ℝ) / 24)
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              ((1/2 : ℂ) + (t : ℂ) * Complex.I)‖ := by ring

end Work.Sieve
