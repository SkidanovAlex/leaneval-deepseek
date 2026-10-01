import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.PrincipalZeroCount

/-!
# `Work.ZeroDensity.Zeta.ZetaZeroDefs` — the zero count of the Riemann zeta function

`Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T` counts the zeros of the completed
`L`-function of the primitive character inducing the principal character mod `q`, i.e. of the
completed Riemann zeta function.  This module records that fact as a standalone count
`zetaZeroCount σ T` of the zeros of `completedRiemannZeta` in the rectangle
`σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`, and the bridge

`zetaZeroCount σ T = zeroCountIn (1 : DirichletCharacter ℂ q) σ T`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.Zeta

/-- The multiplicity-weighted number of non-trivial zeros of the Riemann zeta function
(equivalently, of zeros of the entire completion `Ξ`), in the rectangle `σ ≤ Re ρ ≤ 1`,
`|Im ρ| ≤ T`. -/
def zetaZeroCount (σ T : ℝ) : ℝ :=
  ∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T then
    (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0

/-- **The principal character's zero count is the zeta zero count.**  The primitive character
inducing `1 : DirichletCharacter ℂ q` is the trivial character mod `1`, whose completed
`L`-function is `completedRiemannZeta`, so the multiplicities agree pointwise
(`Work.LinnikAreas.zeroMult_one_eq`). -/
theorem zetaZeroCount_eq_zeroCountIn {q : ℕ} [NeZero q] (σ T : ℝ) :
    zetaZeroCount σ T = Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T := by
  rw [zetaZeroCount, Work.LinnikAreas.zeroCountIn]
  exact finsum_congr (fun ρ => by rw [Work.LinnikAreas.zeroMult_one_eq])

end Work.ZeroDensity.Zeta
