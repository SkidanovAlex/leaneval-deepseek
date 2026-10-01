import Mathlib

/-!
# `L(χ,·)` as the completed `L`-function times the inverse archimedean factor

For a non-principal Dirichlet character `χ` of level `q`, Mathlib's
`DirichletCharacter.LFunction_eq_completed_div_gammaFactor` writes

  `L(χ,s) = Λ(χ,s) / gammaFactor χ s`   (away from the exceptional point `s = 1`, which
                                          does not arise since `q ≠ 1`),

where the archimedean factor `gammaFactor χ` is the Riemann Gamma factor of the parity of `χ`:

* `gammaFactor χ = Gammaℝ`            when `χ` is even,
* `gammaFactor χ = (· + 1).Gammaℝ`    when `χ` is odd.

Choosing `a = 0` in the even case and `a = 1` in the odd case therefore gives the identity

  `L(χ,s) = Λ(χ,s) · (Gammaℝ (s + a))⁻¹`

as an identity of *functions* of `s`, the form in which the inverse Gamma factor is an entire
function (its zeros are exactly the trivial zeros of `L(χ,·)`).
-/

namespace Work.LinnikAreas.TuranOther

/-- **The `L`-function is the completed `L`-function times the inverse archimedean factor.**

For a non-principal `χ` there is a parity integer `a ∈ {0,1}` (`a = 0` for even `χ`, `a = 1` for
odd `χ`) such that, as functions of the complex variable,

  `L(χ,·) = Λ(χ,·) * (Gammaℝ (· + a))⁻¹`.

This is the factorization that makes the inverse Gamma factor entire, so that the multiplicity of
every zero of `L(χ,·)` — trivial zeros included — is the sum of the multiplicities of `Λ(χ,·)`
and of `(Gammaℝ (· + a))⁻¹` at that point. -/
theorem lFunction_eq_completed_mul_invGamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ∃ a : ℕ, (χ.Even → a = 0) ∧ (χ.Odd → a = 1) ∧
      DirichletCharacter.LFunction χ
        = fun s : ℂ => DirichletCharacter.completedLFunction χ s
            * (Complex.Gammaℝ (s + a))⁻¹ := by
  -- the exceptional point `s = 1` of the factorization is excluded by `χ ≠ 1`
  have hq1 : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  rcases χ.even_or_odd with hE | hO
  · -- even `χ`: `gammaFactor χ = Gammaℝ`, so `a = 0`
    refine ⟨0, fun _ => rfl, fun h => absurd h hE.not_odd, ?_⟩
    funext s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq1),
      DirichletCharacter.Even.gammaFactor_def hE s, div_eq_mul_inv]
    simp
  · -- odd `χ`: `gammaFactor χ = (· + 1).Gammaℝ`, so `a = 1`
    refine ⟨1, fun h => absurd h hO.not_even, fun _ => rfl, ?_⟩
    funext s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq1),
      DirichletCharacter.Odd.gammaFactor_def hO s, div_eq_mul_inv]
    simp

end Work.LinnikAreas.TuranOther
