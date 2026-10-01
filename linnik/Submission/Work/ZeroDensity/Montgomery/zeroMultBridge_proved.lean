import Mathlib
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult

namespace Work.ZeroDensity.Montgomery

/-- **The bridge from `zeroMult`-zeros to zeros of the ordinary `L`-function.**  If `ρ` in the
closed strip `1/2 ≤ Re ρ ≤ 1` is a zero of `Λ(χ*,·)` for a non-principal `χ` mod `q` (i.e.
`Work.LinnikContract.zeroMult χ ρ ≠ 0`), then `L(ρ,χ) = 0`.

This generalises `Work.LinnikAreas.LFunction_eq_zero_of_zeroMult` (stated for real zeros
`β ∈ (0,1)`) to arbitrary complex `ρ`: `L(·,χ)` is a finite Euler-factor multiple of
`L(·,χ*)`, and Mathlib's `LFunction_changeLevel` plus
`Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero` give `L(ρ,χ*) = 0` directly, whence
`L(ρ,χ) = 0 · (product) = 0`.  (The strip hypotheses are not needed for the conclusion; they are
kept so that the statement matches the shape in which the assembly uses it.) -/
theorem zeroMultBridge_proved : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    χ ≠ 1 → (1 : ℝ) / 2 ≤ ρ.re → ρ.re ≤ 1 → Work.LinnikContract.zeroMult χ ρ ≠ 0 →
    DirichletCharacter.LFunction χ ρ = 0 := by
  intro q _ χ ρ hχ _ _ hzm
  -- the primitive character inducing `χ` has level `χ.conductor`, which is non-zero
  have hcond_ne : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- a non-principal `χ` has conductor `≠ 1`
  have hcond : χ.conductor ≠ 1 := fun hc =>
    hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr hc)
  -- `zeroMult` is the vanishing order of the completed `L`-function of the primitive character
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by
      simpa only [Work.LinnikContract.zeroMult] using hzm)
  -- hence `ρ` is a zero of the ordinary `L`-function of the primitive character inducing `χ`
  have hLprim : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inr hcond), hcomp,
      zero_div]
  -- the primitive character inducing a non-principal character is non-principal
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro hψ
    have h1 := χ.changeLevel_primitiveCharacter
    rw [hψ, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
    exact hχ h1.symm
  -- and `χ` is the level-`q` lift of that primitive character, so `L(·,χ)` differs from
  -- `L(·,χ*)` by a finite Euler product
  rw [← χ.changeLevel_primitiveCharacter]
  rw [DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Or.inl hψne), hLprim, zero_mul]

end Work.ZeroDensity.Montgomery
