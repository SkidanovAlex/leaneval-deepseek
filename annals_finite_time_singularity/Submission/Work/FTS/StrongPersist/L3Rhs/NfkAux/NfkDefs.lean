/-
# The profiles of the `N₄^{g*} + N₅^{g*}` block

`N₄^{g*}` and `N₅^{g*}` are the two rows of the nonlinear right-hand side in which the
angular moment `FK g` of the perturbation `g = f` multiplies the *star* profile `F_*`
(row 21 resp. row 25a of the paper's table):

```
N₄^{g*} α g z θ = -(1/2) sin(2θ) · FK g z · ∂_θF_*(z,θ)
N₅^{g*} α g z θ = -sin²θ · FK g z · F_* z θ
```

Since `F_* α z θ = α (Γ θ / c α) · 2 hKer z` with `hKer z = z/(1+z)²`, both rows factor as a
product of an *angular* profile and a *radial* function, with the **same** radial factor

```
rProf g z = FK g z · hKer z
```

and the angular profiles `-(α/c)·D_θΓ` (row 21) resp. `-(2α/c)·sin²θ·Γ` (row 25a).  Their sum
is the single angular profile

```
aProf α θ = -(α / c α) · (D_θΓ(θ) + 2 sin²θ · Γ(θ)).
```

`Gprof` is the angular majorant used to dominate the `D_θ`-iterates of `aProf` up to order
`4`: it is the sum of the two terms that occur, `Γ·(α + sin 2θ)` (the sharp bound for the
`D_θ`-iterates of `Γ`, `RNP.dthU_pow_Gam_sharp`) and `sin(2θ)^{α/5}` (the bound for the
`D_θ`-iterates of `sin²θ·Γ`, `RNP24.dthSinSqGam_le`).  Its square times the weight
`sin(2θ)^{-γ(α)}` is integrable with an integral `O(1/α)`, which is what makes the final
constant of the block estimate uniform in `α` after the `α` gain of the two iteration bounds.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false

/-- The angular profile of `N₄^{g*} + N₅^{g*}`: `a θ = -(α/c α)·(D_θΓ(θ) + 2 sin²θ·Γ(θ))`. -/
def aProf (α : ℝ) (θ : ℝ) : ℝ :=
  -(α / Work.Spaces.c α) *
    (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
      + 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ)

/-- The radial profile of `N₄^{g*} + N₅^{g*}`: `r z = FK g z · hKer z`, `hKer z = z/(1+z)²`. -/
def rProf (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  Work.Construction.FK g z * Work.Spaces.hKer z

/-- The angular majorant of the `D_θ`-iterates of `aProf`: `Γ(α + sin 2θ) + sin(2θ)^{α/5}`. -/
def Gprof (α : ℝ) (θ : ℝ) : ℝ :=
  Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) + (Real.sin (2 * θ)) ^ (α / 5)

end Work.FTS.StrongPersist.L3Rhs.NfkAux
