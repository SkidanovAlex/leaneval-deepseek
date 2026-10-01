import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikContract.Defs

namespace Work.ZeroFreeTables

open DirichletCharacter

/-- Auxiliary: a non-trivial `L`-function never vanishes in the half-plane `Re s ≥ 1`. -/
theorem LFunction_ne_zero_of_one_le_re' {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) [NeZero ψ.conductor] {u : ℂ} (hu : 1 ≤ u.re) :
    DirichletCharacter.LFunction ψ.primitiveCharacter u ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ.primitiveCharacter
    (Or.inl (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one ψ hψ)) hu

/-- Auxiliary: `zeroMult ψ u ≠ 0` for a zero `u` of the primitive `L`-function in the
critical strip. -/
theorem zeroMult_ne_zero_of_LFunction_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) [NeZero ψ.conductor] {u : ℂ}
    (hu : DirichletCharacter.LFunction ψ.primitiveCharacter u = 0) (h0 : 0 < u.re) (h1 : u.re < 1) :
    Work.LinnikContract.zeroMult ψ u ≠ 0 :=
  (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer ψ hψ).2.2 u hu h0 h1

/-- Auxiliary: `lamOf q ρ₂ ≤ lamOf q u` together with `0 < log q` forces `u.re ≤ ρ₂.re`. -/
theorem re_le_of_lamOf_le {q : ℕ} (hlogq : 0 < Real.log q) {ρ₂ u : ℂ}
    (h : Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) : u.re ≤ ρ₂.re := by
  rw [Work.LinnikContract.lamOf] at h
  have h' : 1 - ρ₂.re ≤ 1 - u.re := le_of_mul_le_mul_right h hlogq
  linarith

theorem maximalityAt {q : ℕ} [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ₂ : ℂ)
    (hβ₂pos : 0 < ρ₂.re) (hlogq : 0 < Real.log q) {H H' : ℝ} (hHH' : H' ≤ H)
    (hmin : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ H → (ψ, u) ≠ (χ₀, ρ₀) →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hne : ψ ≠ χ₀) [NeZero ψ.conductor] :
    ∀ u : ℂ, DirichletCharacter.LFunction ψ.primitiveCharacter u = 0 →
      |u.im| ≤ H' → u.re ≤ ρ₂.re := by
  intro u hu hIm
  by_cases hcase : u.re ≤ ρ₂.re
  · exact hcase
  · have hcase' : ρ₂.re < u.re := not_le.mp hcase
    have hu0 : 0 < u.re := lt_trans hβ₂pos hcase'
    by_cases hlt : u.re < 1
    · -- `u` lies in the critical strip: `hmin` applies
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        zeroMult_ne_zero_of_LFunction_zero ψ hψ hu hu0 hlt
      have him : |u.im| ≤ H := le_trans hIm hHH'
      have hne' : (ψ, u) ≠ (χ₀, ρ₀) := by
        intro hh
        exact hne (by simpa using congrArg Prod.fst hh)
      exact re_le_of_lamOf_le hlogq (hmin ψ u hψ hzm him hne')
    · -- `u.re ≥ 1`: impossible for a non-trivial `L`-function
      exact absurd hu (LFunction_ne_zero_of_one_le_re' ψ hψ (not_lt.mp hlt))

end Work.ZeroFreeTables
