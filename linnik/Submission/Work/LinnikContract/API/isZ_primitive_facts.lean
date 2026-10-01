import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.API

/-- Unfolding `zeroMult`: a zero in the working region is a zero of the completed L-function of a
primitive non-trivial character of some level `N` (namely `χ.primitiveCharacter`, `N = χ.conductor`).

Prover notes: `IsZ` is `χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1`; use
`apply_eq_zero_of_analyticOrderNatAt_ne_zero`, `primitiveCharacter_isPrimitive` and
`primitiveCharacter_one`/`changeLevel_one_iff` for `χ.primitiveCharacter ≠ 1`.  Mind the
`letI : NeZero χ.conductor` inside `zeroMult` (proof irrelevance lets you pass `⟨χ.conductor_ne_zero⟩`).
No `native_decide`. -/
theorem isZ_primitive_facts {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ ρ) : ∃ (N : ℕ) (hN : NeZero N) (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 ∧ ψ.IsPrimitive ∧ @DirichletCharacter.completedLFunction N hN ψ ρ = 0 := by
  refine ⟨χ.conductor, ⟨χ.conductor_ne_zero⟩, χ.primitiveCharacter,
    ?_, χ.primitiveCharacter_isPrimitive, ?_⟩
  · -- `χ.primitiveCharacter` is non-trivial, else `χ` itself would be trivial
    intro hψ
    have h1 := χ.changeLevel_primitiveCharacter
    rw [hψ, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
    exact h.1 h1.symm
  · -- `zeroMult χ ρ ≠ 0` says `ρ` is a zero of `completedLFunction χ.primitiveCharacter`
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.2.1

end Work.LinnikContract.API
