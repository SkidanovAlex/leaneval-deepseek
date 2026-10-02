import Mathlib
import Submission.Work.GATE2.D1.exitPath_of_tongue_trans
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.Relay
import Submission.Work.MandelWire.GATE2n.TransFree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! # GATE2 / D1At — the leak-data-free form of the D1 exit-path construction

A copy of `Submission.Work.GATE2.D1At.TransFree` in which the `LeakData` bundle is replaced by the bare leak
centre `xLeak`, its radius `r₀` and its positivity (`hr₀`).  Only `L.xstar - L.j₀` and
`L.r₀`/`L.hr₀` are used by that file, so the `LeakData` is never needed and the drive can
**choose** its leak centre (`NOTES_LEAD_mandelbar_gaps3.md` §2.2). -/

namespace Work.MandelWire.G2n

open Work.GATE2

open Work.GATE2.D1

/-! ## The `ι b`-tongue is the `b`-tongue of the shifted level

`Work.GATE.iotaTongue trans xLeak r₀` requires the transit coordinate to be within `r₀/2` of a
point of the half-integer lattice `xLeak + 1/2 + ℤ`; `Work.GATE.bTongue trans xLeak r₀` requires it
to be within `r₀/2` of a point of the integer lattice `xLeak + ℤ`.  Shifting the *level* by `1/2`
exchanges the two, and the two statements are in fact the very same unfolded term. -/

/-- `iotaTongue trans xLeak r₀` is `bTongue trans (xLeak + 1/2) r₀` with the level shifted. -/
theorem iotaTongue_eq_bTongue_add_half (trans : ℂ → ℂ) (xLeak r₀ : ℝ) :
    (fun e => Work.GATE.iotaTongue trans xLeak r₀ e)
      = (fun e => Work.GATE.bTongue trans (xLeak + 1 / 2) r₀ e) := rfl

/-- **The exit-path datum of the `ι b`-tongue, for an arbitrary transit coordinate.**  This is
`Work.GATE2.D1.exitPathData_of_exitLoop_trans` read at the level `x₀ = X + 1/2` and the angle
`α`, where the `b`-tongue of the shifted level is *the same predicate* as the `ι b`-tongue of the
unshifted level `X`.  It is the general-`trans` form of the `ι`-tongue exit path consumed by
PARIMPL2 (with `trans := transPh` in place of PARIMPL's `transU P nIn`). -/
theorem exitPath_of_tongue_iota_trans {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀)
    (trans : ℂ → ℂ)
    (hPa : Pa = fl.Pa) (hφa : φa = fl.φa) (hΨ : Ψ = fl.Ψ)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hEXL : Work.GATE2.ExitLoop c₀ fl.Ψ ((xLeak) + 1 / 2) r₀
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)) Work.EL.alpha2)
    (hUT : Work.GATE2.TransitLockstepAbove c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (hPL.X + 1)
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b) :
    Work.GATE2.ExitPathData c₀ P.Nm trans
      ((xLeak) + 1 / 2) r₀
      (fun e => Work.GATE.iotaTongue trans
        (xLeak) r₀ e) Work.EL.alpha2 := by
  rw [iotaTongue_eq_bTongue_add_half]
  exact Work.MandelWire.G2n.exitPathData_of_exitLoop_trans
    (xLeak := xLeak) (r₀ := r₀) (hr₀ := hr₀)
    (v := ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (x₀ := xLeak + 1 / 2) (α := Work.EL.alpha2)
    (FF := FF) (nIn := nIn) trans hPa hφa hΨ hcrit hPL hEXL hUT hblow

end Work.MandelWire.G2n
