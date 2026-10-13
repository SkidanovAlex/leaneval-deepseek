/-
# The radial factor `φ(z) = z/(1+z)` of the row-10 auxiliary estimate

This module only *defines* the object (and records two trivial bounds); the facts about it
(`SmoothOpen`, boundedness of the iterated radial derivatives `D_z^b`) are in
`Submission/Work/FTS/NonlinRows/NRow10aux/phiFacts.lean`.

The purpose of the whole `NRow10aux` chain is the statement

`HkMem α 4 (fun z θ => φ z * g z θ) ∧ Xn α (fun z θ => φ z * g z θ) ≤ C * Xn α g`
  (`Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk`),

i.e. multiplication by the bounded radial factor `φ` costs nothing in the weighted `ℋ⁴`-norm.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

/-- `φ(z) = z / (1 + z)`: the bounded radial (i.e. `θ`-independent) factor whose multiplication
on `ℋ⁴` is the content of `Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk`. -/
def phiF (z : ℝ) : ℝ := z / (1 + z)

theorem phiF_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ phiF z := by
  rw [phiF]
  exact div_nonneg hz (by linarith)

theorem phiF_le_one {z : ℝ} (hz : 0 ≤ z) : phiF z ≤ 1 := by
  rw [phiF, div_le_one (by linarith : (0 : ℝ) < 1 + z)]
  linarith

/-- `φ` does not depend on the angular variable: this is the `1`-line bridge used when the
shared `HkIntegrand` bites on `fun z θ => phiF z`. -/
theorem phiF_eq (z θ : ℝ) : phiF z = z / (1 + z) := rfl

end Work.FTS.NonlinRows.NRow10aux
