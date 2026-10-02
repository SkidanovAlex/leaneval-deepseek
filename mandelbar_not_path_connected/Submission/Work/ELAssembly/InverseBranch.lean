/-
# `ELAssembly` — the inverse branches `gQ`, `gD6` and their defining properties

The certificate geometry of the two nests provides, for every level, the pull-back as a
`Set.BijOn` of the polynomial (`CertGeometry.pbQ`, `CertGeometry.pbD`).  The inverse branches
`Work.ELAssembly.gQ` (of `F c` on `Q̂₀`) and `Work.ELAssembly.gD6` (of `f_c^6` on `Δ̂₀`) are then
*defined* as the arbitrary inverse `Function.invFunOn` of those bijections, and the two properties
the interface `Work.ELNest.NestData` asks for (`g_left`, `g_mem`, `g6_left`, `g6_mem`) become
pure API of `Set.BijOn`:

* `gQ_left` / `gD6_left` — the branch is a right inverse of the map on the *outer* level
  (`Set.BijOn.invOn_invFunOn`), and
* `gQ_mem` / `gD6_mem` — the branch maps the outer level into the *inner* level
  (`Set.BijOn.surjOn` + `Function.invFunOn_mem`).

Only the holomorphy of the two branches is left as a genuine hypothesis
(`CertGeometry.g_diff`, `CertGeometry.g6_diff`).
-/
import Mathlib
import Submission.Work.ELAssembly.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The branch of `F c` on `Q̂₀` -/

/-- **`gQ` is a right inverse of `F c` on `Q̂₀`**: from the certified pull-back `pbQ 0`
(a `Set.BijOn`), the arbitrary inverse `Function.invFunOn` is a right inverse.  This is the field
`g_left` of `Work.ELNest.NestData`. -/
theorem gQ_left {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (h : Set.BijOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1))
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0))) :
    ∀ z ∈ Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0),
      Work.EL.F c (gQ c d L P0 N z) = z := by
  intro z hz
  have h' : Set.RightInvOn (Function.invFunOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1))) (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0)) :=
    (h.invOn_invFunOn).2
  exact h'.eq hz

/-- **`gQ` maps `Q̂₀` into `Q̂₁`**: this is the field `g_mem` of `Work.ELNest.NestData`. -/
theorem gQ_mem {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (h : Set.BijOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1))
      (Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0))) :
    ∀ z ∈ Work.EL.polyRegion [P0, N.Qp 0] (Work.ELNest.Qlev L 0),
      gQ c d L P0 N z ∈ Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1) := by
  intro z hz
  obtain ⟨w, hw, hfw⟩ := h.surjOn hz
  exact Function.invFunOn_mem ⟨w, hw, hfw⟩

/-! ## The branch of `f_c^6` on `Δ̂₀` -/

/-- **`gD6` is a right inverse of `f_c^6` on `Δ̂₀`**: the field `g6_left` of
`Work.ELNest.NestData`. -/
theorem gD6_left {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (h : Set.BijOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))
      (Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0))) :
    ∀ z ∈ Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0),
      Work.ELNest.F6 c (gD6 c L N z) = z := by
  intro z hz
  have h' : Set.RightInvOn (Function.invFunOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))) (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0)) :=
    (h.invOn_invFunOn).2
  exact h'.eq hz

/-- **`gD6` maps `Δ̂₀` into `Δ̂₁`**: the field `g6_mem` of `Work.ELNest.NestData`. -/
theorem gD6_mem {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (h : Set.BijOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))
      (Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0))) :
    ∀ z ∈ Work.EL.polyRegion [N.Za 0, N.Zb 0, N.Zc 0] (Work.ELNest.Dlev L 0),
      gD6 c L N z ∈ Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1) := by
  intro z hz
  obtain ⟨w, hw, hfw⟩ := h.surjOn hz
  exact Function.invFunOn_mem ⟨w, hw, hfw⟩

end Work.ELAssembly
