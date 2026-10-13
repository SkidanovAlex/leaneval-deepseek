/-
# `Work.FTS_RegExport.VPDefs` — the split of RX-VP's `VelPkg` into a sup-bounds part and a rest part

LEAD (StreamBdry design review §5): `VelPkg` is consumed by two items that must not form a cycle —
StreamBdry's `hΦsm`/`hΦaxis` needs the *slot bounds* (`dbnd`, and with them `bnd`) while RX-T/RX-St1
need the *endpoint/vanishing* clause `vanish0` and the axis clause `axis`.  To keep the item graph
acyclic the package is split here into

* `VelPkgSup` — the sup-bounds part: `bnd`, `vz0`, `vth_ends`, `dbnd`, `cont` (verbatim copies of
  the corresponding `RegExportIface.VelPkg` fields);
* the rest — `c2`, `vanish0`, `vanishK`, `axis`, supplied separately and glued by
  `VelPkgSup.toVelPkg`.

Nothing here changes the frozen `RegExportIface.VelPkg`; the split exists so that the sup-bounds
half can land first and unblock StreamBdry, and the endpoint half (the `Φ̃`-conductor conditions)
can be proved afterwards without anyone waiting.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **The sup-bounds half of `RegExportIface.VelPkg`** (REVIEW F3a `dbnd` and its companions).
Fields are verbatim copies; this is what StreamBdry (SB4) consumes. -/
structure VelPkgSup (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  bnd : ∃ M : ℝ, ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ →
    |Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ| ≤ M ∧
      |Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ| ≤ M * Real.sin (2 * θ) ∧
      |Work.FTS.RegExportIface.cs7 αG μ G Φ z θ τ| ≤ M
  vz0 : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ →
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
  vth_ends : ∀ z τ, 0 < z → 0 ≤ τ →
    Work.FTS.RegExportIface.Vθ7 αG Φ z 0 τ = 0 ∧
      Work.FTS.RegExportIface.Vθ7 αG Φ z (π / 2) τ = 0
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ →
    θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ
      / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Work.FTS.RegExportIface.Vz7 αG μ G Φ p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.Vθ7 αG Φ p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.cs7 αG μ G Φ p.1 p.2.1 p.2.2))
    (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S)

/-- **The endpoint / `Φ̃`-conductor half of `RegExportIface.VelPkg`**: `C²` of the stream
function, the `O(z)` vanishing `vanish0` (F3a) and `vanishK`, and the axis condition
`∂_θΦ̃(z,π/2) = 0` (F2.2).  This is the half shared with StreamBdry's `hΦaxis`. -/
structure VelPkgEnd (αG : ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  c2 : ∀ τ ∈ Icc (0:ℝ) S,
    ContDiffOn ℝ 2 (Function.uncurry (slice Φ τ)) Work.FTS.EllipticEst.Q0
  vanish0 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ∀ Q ∈ ({(Work.Construction.Rop αG (Work.FTS.RegExportIface.phiTil αG G Φ τ)),
        Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ),
        fun z θ => Work.Construction.Uop αG (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
          / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
      |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dz Q z θ| ≤ M * min z 1 ∧
        |Work.Spaces.Dth Q z θ| ≤ M * min z 1
  vanishK : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |Work.Construction.FK (slice G τ) z| + |Work.Construction.L12 (slice G τ) z| ≤ M * min z 1
  axis : ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    Work.Spaces.pth (Work.FTS.RegExportIface.phiTil αG G Φ τ) z (π / 2) = 0

/- `VelPkgSup.toVelPkg` (the glue of the two halves into the old `VelPkg` with `axis` and the
closed-θ `bnd`/`cont`) was REMOVED 2026-10-11 by the lead's install of the repaired `VelPkg`
(`cbc/fts_velpkg_fix.md` + REVIEW FIX 1): the repaired `VelPkg` = `VelPkgOpen` + `thLip`, with no
`axis` field, so the old glue no longer typechecks. Snapshot:
`~/snapshots/fts_velpkg_fix/Submission/Work/FTS_RegExport/VPDefs.lean`. -/

end Work.FTS_RegExport
