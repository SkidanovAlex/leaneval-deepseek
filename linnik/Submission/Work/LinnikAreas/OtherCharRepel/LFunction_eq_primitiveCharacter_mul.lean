import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter

/-- Relation between the L-function of a non-principal Dirichlet character and that of the
primitive character inducing it: the two Euler products differ exactly by the local factors at
the primes dividing the level `N`.

This is `DirichletCharacter.LFunction_changeLevel` applied to the fact that `ψ` is the level-`N`
lift (`changeLevel`) of its primitive character. -/
theorem LFunction_eq_primitiveCharacter_mul {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) [NeZero ψ.conductor] (hψ : ψ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction ψ s = DirichletCharacter.LFunction ψ.primitiveCharacter s *
      ∏ p ∈ N.primeFactors, (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) := by
  have hprim : ψ.primitiveCharacter ≠ 1 := by
    intro h
    apply hψ
    rw [← changeLevel_primitiveCharacter (χ := ψ), h]
    exact changeLevel_one _
  conv_lhs => rw [← changeLevel_primitiveCharacter (χ := ψ)]
  exact LFunction_changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter (Or.inl hprim)

end Work.LinnikAreas.OtherCharRepel
