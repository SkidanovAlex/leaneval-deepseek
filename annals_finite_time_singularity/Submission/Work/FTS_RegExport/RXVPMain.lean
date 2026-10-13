import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_RegExport.VPOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVPMain` — the `VelPkg` assembly

`Work.FTS_RegExport.VelPkg_of_open` is the one-line glue between the area's `VelPkgOpen`
(the repaired eight-field package: open-`θ` `bnd`/`vz0`/`cont`, no `axis`) and the frozen
`RegExportIface.VelPkg` (the same fields plus the `thHol` Hölder clause).  It exists so that the
final `velPkg_proved` is `VelPkg_of_open (RXVP3.velPkgOpen_of_vopLower …) (thHol …)`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface

set_option autoImplicit false

/-- **`VelPkgOpen` + `thHol` = the frozen `VelPkg`.** -/
theorem VelPkg_of_open {αG : ℝ} {μ : ℝ → ℝ} {G Φ : Fam} {S : ℝ}
    (h : Work.FTS_RegExport.VelPkgOpen αG μ G Φ S)
    (hth : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ThHol (Vz7 αG μ G Φ) S β ∧ ThHol (cs7 αG μ G Φ) S β) :
    VelPkg αG μ G Φ S where
  bnd := h.bnd
  vz0 := h.vz0
  vth_ends := h.vth_ends
  c2 := h.c2
  dbnd := h.dbnd
  cont := h.cont
  thHol := hth
  vanish0 := h.vanish0
  vanishK := h.vanishK

end Work.FTS_RegExport
