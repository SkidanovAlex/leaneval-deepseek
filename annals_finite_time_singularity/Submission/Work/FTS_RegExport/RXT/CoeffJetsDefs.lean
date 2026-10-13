import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.CoeffJets` — the *true* coefficient package of RX-VP

The frozen `RegExportIface.VelPkg` (and its split `Work.FTS_RegExport.VelPkgSup`) carry three
clauses whose angular quantifier is the **closed** interval `Iθ = Icc 0 (π/2)`:

* `bnd` (`|Vz7| ≤ M`, `|Vθ7| ≤ M sin 2θ`, `|cs7| ≤ M` for `θ ∈ Iθ`),
* `vz0` (`0 ≤ Vz7` for `θ ∈ Iθ`),
* `cont` (joint continuity on `Ioi 0 ×ˢ Icc 0 (π/2) ×ˢ Icc 0 S`),

and they are **false** for the constructed profile: `Vz7` is discontinuous at `θ = π/2`
(`RXVP2/NOTES_velPkgSup_FALSE.md`, machine-checked `not_continuousOn_Vz7`; the defect is
`Real.tan (π/2) = 0` inside `Vop`) and `vz0` fails there too for `α > 1/4`.  The clause `axis`
of `VelPkg` is false as well (`RXVP/NOTES_velPkgEnd_axis_FALSE.md`).

Every *consumer* on the RX-St1 path quantifies over the **open** interval `0 < θ < π/2`
(`R7Block.hVz0/hVza/hVθb/hcsc`, and the leaf statements S5b/S5c/S6 of
`RegExportIface/RXT/Leaves.lean`), and the open-θ clauses are not affected by the `tan (π/2)`
artefact.  This file therefore fixes the package in the only place that matters:

* `dbnd` — the order-≤2 mixed jets of the three coefficient slices (open `θ`), verbatim from
  the frozen `dbnd`;
* `cont` — τ-continuity of the three coefficient slices at a fixed point of the open quadrant.

`CoeffJets` is what S5b/S5c/S6 and the assembly of S8 (`weighted_system`) actually consume;
it is implied by any open-θ repair of `VelPkgSup`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7)

set_option autoImplicit false

/-- **The coefficient package actually consumed by the RX-St1 chain** (open angular interval):
the order-≤2 jet bounds `dbnd` of the frozen `VelPkg`, plus τ-continuity of the three coefficient
slices at each point of the open quadrant. -/
structure CoeffJets (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  /-- order-≤2 mixed jets of `Vz7`, `Vθ7/sin 2θ`, `cs7` and of `∂_θVz7` (open `θ`) -/
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ →
    θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Vθ7 αG Φ z θ τ / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  /-- τ-continuity of the three coefficient slices at a fixed point of the open quadrant -/
  cont : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ContinuousOn (fun τ => (Vz7 αG μ G Φ z θ τ, Vθ7 αG Φ z θ τ / Real.sin (2 * θ),
      cs7 αG μ G Φ z θ τ)) (Icc 0 S)

end Work.FTS_RegExport.RXT
