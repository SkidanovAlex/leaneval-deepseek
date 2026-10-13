/-
# `smoothOpen_FK_of_pkg` needs the `GalClass`-strength hypothesis on `g`

`Submission/Work/FTS/GalFields/RHS/smoothOpen_FK_of_pkg.lean` (the assigned file) asks for

  `SmoothOpen (fun z _ => Construction.FK g z)`

from the *open-quadrant* elliptic packages `hell : EllPkgGo α Ce g Φg`,
`hstar : StarPkgo2 α Cs Φs` together with `hg : SmoothOpen g`.  That statement is
**under-hypothesised**: see `RHS/NOTES_smoothOpen_FK_of_pkg_FALSE.md` in this directory for the
diagnosis.  This file records the *repair*, proved: the same conclusion follows as soon as the
datum `g` carries the honesty/regularity facts that every consumer of this chapter has anyway
(`GalClass α g`, i.e. `SmoothQuad g`, `HkMem α 6 g`, `L12 g 0 = 0`, `VanishTheta g`, the axis
conditions and decay), which is exactly the form of the papers's own setting
(`RHS/NOTES_discharge.md` §3 and the `lip` clause of `Defs.RHSData`, whose hypotheses begin with
`GalClass α g`).

The proof is nothing but the already delivered `AuxFK.smoothOpen_FK_radial`: `hell.V.1.1`
(`SmoothOpen (Vop (PhiTil α g Φg))` = `Vop (PhiTg α g Φg)`) gives `L12 g ∈ C^∞` on `(0,∞)` by
`NonlinRows.smoothOpen_L12_radial`, and `OpenPkg.deriv_L12_eq` needs precisely
`SmoothQuad g`, `HkMem α 4 g`, `L12 g 0 = 0` — all fields of `GalClass α g` — to identify
`FK g = -z·∂_z L₁₂(g)`.

Both declines are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.AuxFK.smoothOpen_FK_radial
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **`FK g` is `C^∞` on the open quadrant — the repaired form of `smoothOpen_FK_of_pkg`.**

Drop-in replacement for `Work.FTS.GalFields.RHS.smoothOpen_FK_of_pkg` with the single extra
hypothesis `hgal : GalClass α g` (supplied by the `lip`/`bdd` clauses of `Defs.RHSData` and by
`Nonlin.GalClass` in every row of §8); `hg`, `hΦs`, `hstar` are kept only so that the statement
matches the assigned one. -/
theorem smoothOpen_FK_of_pkg_gal {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Φg : Fn}
    (hgal : Work.FTS.Nonlin.GalClass α g)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) := by
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  exact Work.FTS.NonlinRows.AuxFK.smoothOpen_FK_radial hα hα1 hsm hmem4 hgal.l12
    hell.smooth hell.V.1.1

end Work.FTS.GalFields.RHS
