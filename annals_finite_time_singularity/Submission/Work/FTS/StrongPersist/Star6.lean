/-
# `Work.FTS.StrongPersist.Star6` — the API of the level-six star package `StarPkg6`

`Clauses.lean` introduces `StarPkg6 α Cs Φs`, the level-six lift of the sibling area's
`Work.FTS.VocabO2.StarPkgo2` (the five star fields `ℛ`, `V`, `((z+1)/z)V`, `U/sin 2θ`,
`((z+1)/z)U/sin 2θ` bounded in the paper's `𝒲^{6,∞}`-norm by `Cs·α`).  This module records the
projections in the form in which the level-six rows consume them — one `WlInfMem` and one
`WlInf`-bound per field — together with the two elementary manipulations of the constant `Cs`.

All the lemmas here are projections of the structure fields, so they rest on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

variable {α Cs : ℝ} {Φs : Fn}

/-! ## The five fields, split into membership and bound -/

/-- The `ℛ`-field `((z+1)/z)·ℛ(Φ̃_*)` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.RW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  h.RW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.RW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      ≤ Cs * α :=
  h.RW6.2

/-- The `V`-field `V(Φ̃_*)` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.VW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6 (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) :=
  h.VW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.VW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6 (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ≤ Cs * α :=
  h.VW6.2

/-- The weighted `V`-field `((z+1)/z)·V(Φ̃_*)` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.VzW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  h.VzW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.VzW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
      ≤ Cs * α :=
  h.VzW6.2

/-- The `U/ sin 2θ`-field lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.UsW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) :=
  h.UsW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.UsW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) ≤ Cs * α :=
  h.UsW6.2

/-- The weighted `U/ sin 2θ`-field `((z+1)/z)·U(Φ̃_*)/sin 2θ` lies in `𝒲^{6,∞}`. -/
theorem StarPkg6.UszW6_mem (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInfMem α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) :=
  h.UszW6.1

/-- Its `𝒲^{6,∞}`-norm is bounded by `Cs·α`. -/
theorem StarPkg6.UszW6_bd (h : StarPkg6 α Cs Φs) :
    Work.Spaces.WlInf α 6
      (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ≤ Cs * α :=
  h.UszW6.2

end Work.FTS.StrongPersist
