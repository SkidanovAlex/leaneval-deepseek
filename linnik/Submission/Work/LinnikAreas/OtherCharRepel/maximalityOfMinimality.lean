import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical

theorem maximalityOfMinimality {q : ℕ} [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ₂ : ℂ)
    (hβ₂pos : 0 < ρ₂.re) (hlogq : 0 < Real.log q)
    (hmin : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hne : ψ ≠ χ₀) [NeZero ψ.conductor] :
    ∀ u : ℂ, DirichletCharacter.LFunction ψ.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re := by
  intro u hu him
  by_cases h1 : u.re < 1
  · by_cases h0 : u.re ≤ 0
    · linarith
    · -- `0 < u.re < 1`: `u` is a genuine non-trivial zero, so the minimality hypothesis applies.
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        (zeroMultTransfer ψ hψ).2.2 u hu (not_le.mp h0) h1
      have hne' : (ψ, u) ≠ (χ₀, ρ₀) := fun h => hne (by simpa using congrArg Prod.fst h)
      have hle := hmin ψ u hψ hzm him hne'
      rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at hle
      nlinarith [hle, hlogq]
  · -- `1 ≤ u.re`: a non-trivial `L`-function does not vanish there.
    exact absurd hu (LFunction_ne_zero_of_one_le_re
      (χ := ψ.primitiveCharacter) (s := u) (Or.inl (primitiveCharacter_ne_one ψ hψ)) (not_lt.mp h1))

end Work.LinnikAreas.OtherCharRepel
