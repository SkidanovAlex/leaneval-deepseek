import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.completedLFunction_conj
import Submission.Work.A7.analyticOrderNatAt_starComp
import Submission.Work.A7.trivialChar_completedLFunction_conj_order
import Submission.Work.A7.completedLFunction_primitiveCharacter_inv

open Work.LinnikContract

namespace Work.A7

set_option linter.style.haveILetI false

/-- **Zeros of `χ⁻¹` are the complex conjugates of the zeros of `χ`**, with multiplicity:
the multiplicity of `ρ` as a non-trivial zero of `L(s, χ)` (i.e. as a zero of the completed
L-function of the primitive character inducing `χ`) equals the multiplicity of `conj ρ` as a
zero of `L(s, χ⁻¹)`.

This is the level-independent form of the classical Schwarz reflection identity
`Λ(χ⁻¹)(conj s) = conj(Λ(χ)(s))`. -/
theorem zeroMult_conj_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    Work.LinnikContract.zeroMult χ⁻¹ ((starRingEnd ℂ) ρ) = Work.LinnikContract.zeroMult χ ρ := by
  by_cases hχ : χ = 1
  · -- `χ` trivial: both sides compute the zero-multiplicity of the completed zeta function
    rw [hχ, inv_one]
    simp only [Work.LinnikContract.zeroMult]
    rw [DirichletCharacter.primitiveCharacter_one]
    haveI : NeZero (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q)) :=
      ⟨DirichletCharacter.conductor_ne_zero _⟩
    exact trivialChar_completedLFunction_conj_order ρ
  · -- the primitive character `ψ` of `χ` is non-trivial, so `Λ(ψ)` and `Λ(ψ⁻¹)` are entire
    have hψ : χ.primitiveCharacter ≠ 1 := by
      intro h
      apply hχ
      have h1 := χ.changeLevel_primitiveCharacter
      rw [h, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
      exact h1.symm
    simp only [Work.LinnikContract.zeroMult]
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    -- function form of the reflection identity, at the level of the primitive character
    have hL1f : DirichletCharacter.completedLFunction (χ.primitiveCharacter)⁻¹
        = fun t => (starRingEnd ℂ)
            (DirichletCharacter.completedLFunction χ.primitiveCharacter ((starRingEnd ℂ) t)) := by
      funext t
      simpa using completedLFunction_conj χ.primitiveCharacter hψ ((starRingEnd ℂ) t)
    -- `(χ⁻¹).primitiveCharacter` and `(χ.primitiveCharacter)⁻¹` have the same completed L-function
    rw [completedLFunction_primitiveCharacter_inv χ]
    rw [hL1f]
    -- transport the vanishing order across the reflection
    rw [analyticOrderNatAt_starComp (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      ((starRingEnd ℂ) ρ)]
    simp

end Work.A7
