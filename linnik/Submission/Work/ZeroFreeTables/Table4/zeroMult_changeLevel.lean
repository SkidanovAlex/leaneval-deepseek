import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroDensity.Montgomery.charFamilyConductorSum

set_option linter.style.haveILetI false

namespace Work.ZeroFreeTables.Table4

open DirichletCharacter

/-- `completedLFunction` is compatible with rewriting the level of a Dirichlet character along an
equality of levels (the two Dirichlet characters have the same underlying function). -/
private lemma completedLFunction_cast {n m : ℕ} [NeZero n] [NeZero m] (hn : n = m)
    (ψ : DirichletCharacter ℂ n) :
    DirichletCharacter.completedLFunction ψ
      = DirichletCharacter.completedLFunction (hn ▸ ψ) := by
  cases hn; rfl

/-- **Multiplicity of a zero is invariant under `changeLevel`.**  `zeroMult χ u` is the order of
vanishing of the completed `L`-function of the *primitive* character inducing `χ` at `u`, so it
only depends on that primitive character.  For `h : N ∣ q`, the primitive character inducing
`changeLevel h χ` is (up to the identification of levels supplied by `conductor_changeLevel h`) the
primitive character inducing `χ`; hence the multiplicities agree. -/
theorem zeroMult_changeLevel {N q : ℕ} [NeZero N] [NeZero q] (h : N ∣ q)
    (χ : DirichletCharacter ℂ N) (u : ℂ) :
    Work.LinnikContract.zeroMult (DirichletCharacter.changeLevel h χ) u
      = Work.LinnikContract.zeroMult χ u := by
  -- the `NeZero` instances that `completedLFunction` asks for
  haveI hc : NeZero ((changeLevel h χ).conductor) := ⟨(changeLevel h χ).conductor_ne_zero⟩
  haveI hc' : NeZero (χ.conductor) := ⟨χ.conductor_ne_zero⟩
  -- `changeLevel` does not change the conductor
  have hcond : (changeLevel h χ).conductor = χ.conductor := conductor_changeLevel χ h
  -- ... so the two primitive characters agree once the levels are identified: both lift to
  -- `changeLevel h χ` at level `q`.
  have hchar : hcond ▸ (changeLevel h χ).primitiveCharacter = χ.primitiveCharacter := by
    apply changeLevel_injective (χ.conductor_dvd_level.trans h)
    rw [Work.ZeroDensity.Montgomery.changeLevel_cast hcond ((changeLevel h χ).conductor_dvd_level)
          (χ.conductor_dvd_level.trans h) ((changeLevel h χ).primitiveCharacter),
        DirichletCharacter.changeLevel_primitiveCharacter]
    rw [show χ.conductor_dvd_level.trans h = dvd_trans χ.conductor_dvd_level h from
          Subsingleton.elim _ _,
        DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level h,
        DirichletCharacter.changeLevel_primitiveCharacter]
  -- hence the completed `L`-functions of the two primitive characters coincide
  have hfun : DirichletCharacter.completedLFunction ((changeLevel h χ).primitiveCharacter)
      = DirichletCharacter.completedLFunction (χ.primitiveCharacter) := by
    rw [completedLFunction_cast hcond ((changeLevel h χ).primitiveCharacter), hchar]
  -- unfolding `zeroMult`, the two orders of vanishing are the same
  rw [Work.LinnikContract.zeroMult, Work.LinnikContract.zeroMult, hfun]

end Work.ZeroFreeTables.Table4
