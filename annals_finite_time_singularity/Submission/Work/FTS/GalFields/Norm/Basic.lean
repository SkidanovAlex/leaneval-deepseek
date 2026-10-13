/-
# `FTS/GalFields/Norm` — the two `ℋ⁵`-comparisons behind the `RHSData` interface

The field bounds of this chapter consume `|Fr g|_{ℋ⁴}` with `Fr` involving `D_zg` and `D_θg`
(see `NOTES_RHSData.md`), and the `ℋ⁴`-size of those is controlled by the `ℋ⁵`-size of `g`:

  `HkSq α 4 (D_zg) ≤ HkSq α 5 g`,   `HkSq α 4 (D_θg) ≤ HkSq α 5 g`,

because the `ℋ⁴`-integrand of `D_zg` (resp. `D_θg`) is a sub-sum of the `ℋ⁵`-integrand of `g`.
Both are available in the workspace for the *open* class (`SmoothOpen`, i.e. `C^∞` only on the open
quadrant, which is all a `GalClass` profile satisfies):

* `Work.FTS.CoercivityStep.Norm.HkSq_Dth_le` — no smoothness hypothesis at all;
* `Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm` — from `Q0Sm`, converted from `SmoothOpen` by
  `Work.FTS.StrongPersist.q0Sm_of_smoothOpen`.

This module records the two consequences in the vocabulary of the chapter (`Xn`, `Xn5`).
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.GalFields

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis Xn PsiCan)
open Work.FTS.Galerkin (Fn Fam galFun)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `ℋ⁴`-size of `D_zg` is controlled by the `ℋ⁵`-size of `g`.** -/
theorem Xn_Dz_le_Xn5 {α : ℝ} (hα : 0 < α) {g : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (h : Work.Spaces.HkMem α 5 g) :
    Xn α (Work.Spaces.Dz g) ≤ Xn5 α g :=
  Real.sqrt_le_sqrt
    (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hsm 5) h)

/-- **The `ℋ⁴`-size of `D_θg` is controlled by the `ℋ⁵`-size of `g`.** -/
theorem Xn_Dth_le_Xn5 {α : ℝ} (hα : 0 < α) {g : Fn} (h : Work.Spaces.HkMem α 5 g) :
    Xn α (Work.Spaces.Dth g) ≤ Xn5 α g :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 4 h)

end Work.FTS.GalFields
