/-
# The completed L-function of the primitive character of `χ⁻¹`

The primitive character of `χ⁻¹` has level `(χ⁻¹).conductor`, while the inverse of the primitive
character of `χ` has level `χ.conductor`; by `DirichletCharacter.conductor_inv` these levels
coincide.  Lifting both characters to the common level `q` (the level of `χ`) via `changeLevel`
gives `χ⁻¹` in both cases, since `changeLevel` is a monoid homomorphism and
`changeLevel_primitiveCharacter` says that `changeLevel` of the primitive character is the
character itself.  Injectivity of `changeLevel` then identifies the two characters (up to the cast
along the equality of levels), and the completed L-functions agree because `completedLFunction`
depends only on the level and the character.

This is the identity used to replace `completedLFunction (χ⁻¹).primitiveCharacter` by
`completedLFunction (χ.primitiveCharacter)⁻¹` (e.g. when comparing the functional equations of
`χ` and `χ⁻¹`).
-/
import Mathlib

namespace Work.A7

open DirichletCharacter

/-- Rewriting the level of a Dirichlet character along an equality `h : n = m` and then applying
`changeLevel` to a common multiple `q` of the new level is the same as applying `changeLevel` to
the transported divisor. -/
private lemma changeLevel_recOn {R : Type*} [CommMonoidWithZero R] {n m q : ℕ} (h : n = m)
    (hm : m ∣ q) (ψ : DirichletCharacter R n) :
    changeLevel hm (h ▸ ψ) = changeLevel (h ▸ hm) ψ := by
  cases h
  rfl

/-- `completedLFunction` is compatible with rewriting the level of a Dirichlet character along an
equality of levels. -/
private lemma completedLFunction_cast {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (ψ : DirichletCharacter ℂ n) :
    DirichletCharacter.completedLFunction ψ = DirichletCharacter.completedLFunction (h ▸ ψ) := by
  cases h
  rfl

theorem completedLFunction_primitiveCharacter_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    @DirichletCharacter.completedLFunction ((χ⁻¹).conductor) ⟨(χ⁻¹).conductor_ne_zero⟩ (χ⁻¹).primitiveCharacter
      = @DirichletCharacter.completedLFunction (χ.conductor) ⟨χ.conductor_ne_zero⟩ (χ.primitiveCharacter)⁻¹ := by
  have h1 : NeZero (χ.conductor) := ⟨χ.conductor_ne_zero⟩
  have h2 : NeZero ((χ⁻¹).conductor) := ⟨(χ⁻¹).conductor_ne_zero⟩
  -- The two levels agree.
  have hcond : (χ⁻¹).conductor = χ.conductor := conductor_inv χ
  -- The two characters agree, once the levels are identified: both lift to `χ⁻¹` at level `q`.
  have hchar : hcond ▸ (χ⁻¹).primitiveCharacter = (χ.primitiveCharacter)⁻¹ := by
    apply changeLevel_injective (χ.conductor_dvd_level)
    have hL : changeLevel (χ.conductor_dvd_level) (hcond ▸ (χ⁻¹).primitiveCharacter) = χ⁻¹ := by
      rw [changeLevel_recOn hcond (χ.conductor_dvd_level) (χ⁻¹).primitiveCharacter]
      exact changeLevel_primitiveCharacter (χ⁻¹)
    have hR : changeLevel (χ.conductor_dvd_level) ((χ.primitiveCharacter)⁻¹) = χ⁻¹ := by
      rw [map_inv, changeLevel_primitiveCharacter]
    rw [hL, hR]
  rw [completedLFunction_cast hcond (χ⁻¹).primitiveCharacter, hchar]

end Work.A7
