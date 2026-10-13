/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_RegExport.VPOpen` — the REPAIR of `RegExportIface.VelPkg` (open angular interval)

`NOTES_area_state.md` §2 records the defect of the frozen `RegExportIface.VelPkg`: its `axis`
field and the `θ = π/2` instances of `bnd`/`vz0`/`cont` are all equivalent to the single
axis-slope condition

  (★)  `pth (slice Φ τ) z (π/2) = - L₁₂ (Ftau αG G τ)(z) / (2 αG)`  for all `z > 0`, `τ ∈ [0,S]`,

(for `Φ = psiR α Φs E (tauExt g)`).  It FAILS for the constructed profile: the true axis
conditions are `Ψ(z,π/2) = 0` and `Ψ = O(cos θ)`, so `∂_θΨ(z,π/2)` is the (**non-zero**) axial
strain, and the honest value of `pth (phiTil …) z (π/2)` is
`∂_θΨ(z,π/2) + L₁₂(Ftau)(z)/(2αG) ≠ 0`.

(The earlier justification "`Γ(θ)` is even about `π/2`, so `∂_θΨ(z,π/2) = 0`" is **WRONG** —
correction of the project lead, 2026-10-11, `sources/ftsV2/fts_velpkg_fix.md`.  The lead has
already installed the interface fix: the frozen `VelPkg` is now `open-θ bnd/vz0/cont` without
`axis` and with a new `thLip` field, and `R7Block` takes the edge-extended coefficients
`edgeExt Vz7`, `Vθ7`, `edgeExt cs7`.  `VelPkgOpen` below is that package minus `thLip`.)

`VelPkgOpen` below is the same structure with the three clauses restricted to the **open**
interval `0 < θ < π/2` and `axis` dropped.  Every consumer of the frozen package already carries
`0 < θ < π/2` (`R7Block.hVz0`, `hVza`, `hVθb`, `hcsc`, `hEq`, and `R7e.support_strip_zL`), so
this is the minimal repair; the `vth_ends`/`vanishK`/`c2`/`dbnd`/`vanish0` fields are unchanged
from the frozen ones (`VPDefs.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.VPDefs

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
open Work.FTS.FinalV2 (gS tauExt Sol DynOK' EllLimOK3)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **The repaired velocity package**: `VelPkgEnd`'s fields with the three former
closed-quantifier clauses taken on `0 < θ < π/2`, and without `axis`. -/
structure VelPkgOpen (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  bnd : ∃ M : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ →
    |Vz7 αG μ G Φ z θ τ| ≤ M ∧ |Vθ7 αG Φ z θ τ| ≤ M * Real.sin (2 * θ) ∧
      |cs7 αG μ G Φ z θ τ| ≤ M
  vz0 : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ → 0 ≤ Vz7 αG μ G Φ z θ τ
  vth_ends : ∀ z τ, 0 < z → 0 ≤ τ → Vθ7 αG Φ z 0 τ = 0 ∧ Vθ7 αG Φ z (π / 2) τ = 0
  c2 : ∀ τ ∈ Icc (0:ℝ) S, ContDiffOn ℝ 2 (Function.uncurry (slice Φ τ)) Work.FTS.EllipticEst.Q0
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Vθ7 αG Φ z θ τ / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Vz7 αG μ G Φ p.1 p.2.1 p.2.2, Vθ7 αG Φ p.1 p.2.1 p.2.2, cs7 αG μ G Φ p.1 p.2.1 p.2.2))
    (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S)
  vanish0 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ∀ Q ∈ ({(Work.Construction.Rop αG (phiTil αG G Φ τ)), Work.Construction.Vop (phiTil αG G Φ τ),
        fun z θ => Work.Construction.Uop αG (phiTil αG G Φ τ) z θ / Real.sin (2 * θ)} :
          Set (ℝ → ℝ → ℝ)),
      |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dz Q z θ| ≤ M * min z 1 ∧
        |Work.Spaces.Dth Q z θ| ≤ M * min z 1
  vanishK : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |Work.Construction.FK (slice G τ) z| + |Work.Construction.L12 (slice G τ) z| ≤ M * min z 1

end Work.FTS_RegExport
