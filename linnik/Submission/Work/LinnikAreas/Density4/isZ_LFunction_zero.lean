import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikContract.API.isZ_primitive_facts
import Submission.Work.LinnikAreas.Density4.SsmSetup

namespace Work.LinnikAreas.Density4

/-- A zero of the completed `L`-function of the primitive character inducing `χ`, at a point
in HB's working region, is a zero of `L(s, χ)`. -/
theorem isZ_LFunction_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ ρ) : DirichletCharacter.LFunction χ ρ = 0 := by
  have hχ : χ ≠ 1 := h.1
  have hcond : χ.conductor ≠ 1 := fun hc =>
    hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr hc)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- the completed L-function of the primitive character vanishes at ρ
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero h.2.1
  -- hence so does the ordinary L-function of the primitive character
  have hLprim : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inr hcond), hcomp,
      zero_div]
  -- the primitive character is non-trivial
  have hprim_ne : χ.primitiveCharacter ≠ 1 := by
    intro hψ
    have h1 := χ.changeLevel_primitiveCharacter
    rw [hψ, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
    exact hχ h1.symm
  -- and `χ` is the (level change of the) primitive character
  rw [← χ.changeLevel_primitiveCharacter]
  rw [DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Or.inl hprim_ne), hLprim, zero_mul]

end Work.LinnikAreas.Density4
