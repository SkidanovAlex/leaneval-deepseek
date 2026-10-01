import Mathlib
import Submission.Work.ZeroFreeTables.maximalityAt

namespace Work.ZeroFreeTables

/-- Closed form of the maximality principle: if every zero `u` of a non-principal,
non-exceptional character with `|Im u| ≤ H` satisfies `lamOf q ρ₂ ≤ lamOf q u`, then
every zero `u` of `L(·, ψ*)` with `|Im u| ≤ H' ≤ H` has real part at most `Re ρ₂`.

Same conclusion as `maximalityAt`, but with the extra exclusion of the distinguished
pair `(χ₀, ρ₀)` dropped, i.e. from a strictly stronger hypothesis; note that
`hmin` is only invoked at the particular `ψ` supplied, for which `ψ ≠ χ₀` holds. -/
theorem maximalityAtClosed {q : ℕ} [NeZero q] {χ₀ : DirichletCharacter ℂ q} {ρ₂ : ℂ}
    (hβ₂pos : 0 < ρ₂.re) (hlogq : 0 < Real.log q) {H H' : ℝ} (hHH' : H' ≤ H)
    (hmin : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₀ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ H →
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
    · -- `u` lies in the critical strip: `hmin` applies at `(ψ, u)`
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        zeroMult_ne_zero_of_LFunction_zero ψ hψ hu hu0 hlt
      have him : |u.im| ≤ H := le_trans hIm hHH'
      exact re_le_of_lamOf_le hlogq (hmin ψ u hψ hne hzm him)
    · -- `u.re ≥ 1`: impossible for a non-trivial `L`-function
      exact absurd hu (LFunction_ne_zero_of_one_le_re' ψ hψ (not_lt.mp hlt))

end Work.ZeroFreeTables
