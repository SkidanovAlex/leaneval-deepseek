import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Submission.Work.BoseB7A.Est1.estR1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.Wb1_defs` — the coefficients of the `σ₁`-word `Wb1`

Family 2 of the leftover `R1` of FS `eq:EstimateQ3Tilde1` (`Est1.estR1_defs`) is
the linear word

  `Wb1 = (z/ℓ³) Σ_{s∈suppL} Σ_{k∈P_H} γ_{sk}β_{sk}κB_{sk} (b_k† + b_k)`,

and this module names its two natural coefficient families, so that the estimate
of `Wb1` (`Est1.Wb1_bound`) can be split into a *coefficient* statement (about
sums of scalars) and an *operator* statement (Cauchy–Schwarz in the Fock form):

* `cB1 T E s k = (z/ℓ³)γ_{sk}β_{sk}κB_{sk}` — the `(s,k)` coefficient
  (`γ = gA`, `β = bA`, `κB = kB` are the scalars of `Est1.Defs`),
* `CB1 T E k = Σ_{s∈suppL} cB1 T E s k` — the coefficient of `b_k† + b_k` after
  collecting the `s`-sum.

`cB1` is *definitionally* the scalar appearing in `Est1.Wb1`, so
`simp only [Est1.Wb1, Est1.cB1]` rewrites the word into these coefficients.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

/-- **The `(s,k)` coefficient of the `σ₁`-word `Wb1`**:
`cB1 T E s k = (z/ℓ³)γ_{sk}β_{sk}κB_{sk}` with `γ_{sk} = gA E s k`,
`β_{sk} = bA E s k`, `κB_{sk} = kB T E s k`. -/
def cB1 (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : ℝ :=
  (E.z / E.ell ^ 3) * (gA E s k * bA E s k * kB T E s k)

/-- **The collected `k`-coefficient of `Wb1`**: `CB1 T E k = Σ_{s∈suppL} cB1 T E s k`,
the coefficient with which `b_k† + b_k` occurs in the word. -/
def CB1 (T : TildeData F) (E : Q3Env Mode) (k : Mode) : ℝ :=
  ∑ s ∈ suppL E, cB1 T E s k

end Est1

end Work.BoseB7A
