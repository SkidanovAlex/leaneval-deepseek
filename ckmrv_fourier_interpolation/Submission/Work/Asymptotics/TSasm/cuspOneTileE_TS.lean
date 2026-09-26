import Mathlib
import Submission.Work.Asymptotics.cuspOneTileInputs
import Submission.Work.Asymptotics.Tile.tileLayerSeminorm
import Submission.Work.Asymptotics.TSasm.LayerAgreementClean

/-!
# The cusp-`1` tile bound for `w ∈ E = KEpsilon`

The statement and the two `sorry`-free reductions (from the layer seminorm bound plus the layer
agreement, and from the `(T*S)`-slashed funnel bound) live in
`Submission/Work/Asymptotics/cuspOneTileInputs.lean`; this file carries the target itself, so that
the module proving an input never has to import this one.

The bound is obtained from the layer route of `Work.Asymptotics.cuspOneTileE_TS_of_inputs`,
supplied with

* the tile layer `r`-seminorm bound `Work.Asymptotics.TileLayerSeminorm ℓ d`, proved in
  `Submission/Work/Asymptotics/Tile/tileLayerSeminorm.lean`
  (`Work.Asymptotics.Tile.tileLayerSeminorm`) from the principal-part window
  `Tile.tilePPWindow_bound`, the below-pole window `Tile.tileWindowRestricted_own` and the explicit
  `highPart` bound `Gcusp_tile_bound`; and
* the cusp-`±1` layer agreement `Work.Asymptotics.TileLayerAgreement ℓ d`, obtained by
  specialising `Work.Asymptotics.layer_agreement_cuspTile` to the tile set `cuspTileSet`, which
  here comes in the clash-free branch-`KPlusXiDefs`-compatible copy
  `Submission/Work/Asymptotics/CleanAgree/LayerAgreement.lean` (the original lives in the
  `MiddleRange` branch, which cannot be imported together with the tile seminorm bound).

No `sorry`, `axiom` or `admit` is used anywhere in this file or in the two modules above it.
-/
noncomputable section

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-- **The cusp-`±1` tile layer agreement on the tile set `cuspTileSet`**, specialising
`Work.Asymptotics.layer_agreement_cuspTile` (a tile point is `n +ᵥ w` with `n = ±1` and
`w ∈ E`). -/
theorem tileLayerAgreementOfCuspTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) : TileLayerAgreement ℓ d := by
  intro σ hσ r hr hint
  obtain ⟨w, hw, n, hn, rfl⟩ := hσ
  exact layer_agreement_cuspTile ℓ d hd w n hn hw r hr hint

/-- The cusp-`1` tile bound for `w ∈ E = KEpsilon`: the `n = 1` half of the workspace's
`Work.Asymptotics.cuspTile_seminorm`, i.e. the `r`-seminorm bound for the naive contour transform
of `K^{(d)}` at the cusp-`1` translate `1 + w` of a point `w` of the cusp-`0` funnel
`E = {w : w ∈ DomainD ∧ 2 ≤ (S • w).im}`.  Route: the `(T*S)`-slash transport plus
`(T*S) • τ = 1 + S • τ` reduces it to the `(T S)`-slashed funnel bound
(`Work.Asymptotics.funnel_seminorm_slashed`, the `γ = T*S` case), which is CKMRV §5.2's cusp-`1`
analysis; alternatively the tile route of `Submission/Work/Asymptotics/Tile/`. -/
theorem cuspOneTileE_TS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ w) s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N :=
  cuspOneTileE_TS_of_inputs ℓ d hd (Work.Asymptotics.Tile.tileLayerSeminorm ℓ d hd)
    (tileLayerAgreementOfCuspTile ℓ d hd)

end Work.Asymptotics
