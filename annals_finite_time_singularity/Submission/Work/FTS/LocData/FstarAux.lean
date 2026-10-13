/-
# `Work.FTS.LocData.FstarAux` — auxiliary definitions for the `D_z`-estimate of `F_*`

The fundamental-model profile of the route is the *one-variable* function

  `F_* (z) = 2z/(1+z)²`   (`Work.FM.Fstar`).

`Work.Spaces.DzIter j (fun z _ => F_* z) z θ` is the `j`-th iterate of `D_z = z ∂_z` applied to
the `z`-slice of this profile.  This module collects the two definitions needed to describe it:

* `Gker k` is the **closed form of the `k`-th plain derivative** of `F_*`,

  `Gker k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`,

  which satisfies `deriv (Gker k) z = Gker (k+1) z` off `z = -1` (proved in the sibling module
  `Submission.Work.FTS.LocData.FstarGkerDeriv`) and is bounded by `10·k!/z` for `z ≥ 1`
  (`Submission.Work.FTS.LocData.FstarGkerBound`).  Note `Gker 0 = F_*`.

* `T1 u z = z · ∂_z u z` is the action of `D_z` on a function of `z` alone; the `θ`-variable of
  `fun z _ => F_* z` is a dummy, so `DzIter j (fun z _ => F_* z) z θ = (T1^[j]) F_* z`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The closed form of the `k`-th derivative of the profile** `F_* (z) = 2z/(1+z)²`:

  `Gker k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`.

For `k = 0` this is `F_*` itself; in general `deriv^[k] F_* = Gker k` off `z = -1`. -/
noncomputable def Gker (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

/-- The action of `D_z = z ∂_z` on a function of `z` alone: `T1F u z = z * deriv u z`. (Renamed from `T1` on 2026-10-10: `LocData.DzIter_bumpZ_bound` declares the same `Work.FTS.LocData.T1`, and the two clashed on import.) -/
noncomputable def T1F (u : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv u z

@[simp] theorem Gker_apply (k : ℕ) (z : ℝ) :
    Gker k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

@[simp] theorem T1_apply (u : ℝ → ℝ) (z : ℝ) : T1F u z = z * deriv u z := rfl

/-- `Gker 0` is the profile itself. -/
theorem Gker_zero (z : ℝ) : Gker 0 z = Work.FM.Fstar z := by
  simp only [Gker_apply, Work.FM.Fstar]
  norm_num

end Work.FTS.LocData
