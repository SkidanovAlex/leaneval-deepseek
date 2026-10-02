/-
# `Work.MandelWire.Root` — the pointed root (W4 of `NOTES_LEAD_mandelbar_wire.md` §B.3 R4)

`Work.FinalFix.RootArcHeightZero` is an *existential* `Prop` (`∃ c, ∃ A : RootArc c,
A.critHeight = 0`), and `Work.FinalFix.c₀Of` is `Classical.choose` applied to it.  A parameter
obtained that way carries **no** extra data: in particular the quasiconformal conjugacy `θ`
produced by MNS's height shift (and consumed by the tripod transfer
`Work.TripodCert.tripod_of_seed_transfer` and by `Work.ELAssembly.hzero_of_transfer`) is lost.

This module therefore exposes the *pointed* root: the FQC height shift re-run at the seed with the
conjugacy and the transported base point kept.  The structure `Work.MandelWire.PointedRoot cb db`
bundles

* `c₀` — the transported parameter;
* `θ : ℂ ≃ₜ ℂ` — the quasiconformal conjugacy `T_cb → T_{c₀}`, with its decay at infinity and
  `θ 0 = 0`;
* `d₀ : Work.EL.RootParabolic c₀` — the transported root-parabolic structure, with
  `d₀.z₁ = θ db.z₁` and `Work.FQC.critHeight d₀ = 0`.

The flower / petal-input / phase-normalisation / petal-direction inputs are exactly those of
`Work.MandelFinal.rootArcHeightZero_of_rootParabolic`, so this is the same application of
`Work.FQC.heightShift` with the witness exposed.
-/
import Submission.Work.MandelWire.Deps
import Submission.Work.MandelWire.heightShift_transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.MandelWire

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The pointed root.**  A seed root-parabolic parameter `db` at `cb`, transported by the
FQC quasiconformal deformation `θ` to `c₀`, where the critical Écalle height vanishes. -/
structure PointedRoot (cb : ℂ) (db : Work.EL.RootParabolic cb) where
  /-- the transported parameter. -/
  c₀ : ℂ
  /-- the quasiconformal conjugacy of the deformation. -/
  θ : ℂ ≃ₜ ℂ
  /-- `θ` conjugates the two antipolynomials. -/
  hconj : ∀ z : ℂ, θ (Tantibar cb z) = Tantibar c₀ (θ z)
  /-- `θ` is `O(1/‖z‖)`-close to the identity at infinity. -/
  hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖
  /-- `θ` fixes the critical point. -/
  h0 : θ 0 = 0
  /-- the transported root-parabolic structure. -/
  d₀ : Work.EL.RootParabolic c₀
  /-- the transported characteristic point. -/
  hz₁ : d₀.z₁ = θ db.z₁
  /-- the critical Écalle height vanishes at `c₀`. -/
  hcrit0 : Work.FQC.critHeight d₀ = 0

namespace PointedRoot

variable {cb : ℂ} {db : Work.EL.RootParabolic cb}

/-- The Böttcher coordinate the deformation carries to `c₀`. -/
theorem transfer_bottcher (R : PointedRoot cb db) :
    Work.ParamRays.IsDynBottcher R.c₀ (db.φ ∘ (R.θ.symm : ℂ → ℂ)) :=
  Work.FQC.transfer_bottcher R.θ db.bottcher R.hconj R.hdecay

/-- The escaping set is transported by `θ`. -/
theorem escaping_iff (R : PointedRoot cb db) (z : ℂ) :
    Work.ParamRays.Escaping R.c₀ (R.θ z) ↔ Work.ParamRays.Escaping cb z :=
  Work.FQC.escaping_theta_iff R.θ R.hconj R.hdecay z

/-- **The critical height vanishes at every flower.**  The critical Écalle height of the root arc
with *any* repaired flower of `R.d₀` is `0`: this is
`Work.FlowerGlue.critHeight_eq_of_fix` (the height does not depend on the flower) together with
`Work.FlowerGlue.critHeight_ofRootParabolic_eq_critHeight` and the field `hcrit0`. -/
theorem critHeight_eq_zero (R : PointedRoot cb db)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft R.c₀)
      (Work.PARIMPL.gtc R.c₀) R.d₀.z₁) :
    Work.Final.RootArc.critHeight
      (⟨R.d₀, fl.toParabolicFlower⟩ : Work.Final.RootArc R.c₀) = 0 := by
  have h1 := Work.FlowerGlue.critHeight_eq_of_fix R.d₀ fl (Work.Final.ofRootParabolic R.d₀).fl
    Work.FlowerGlue.fatouUnique
  have h2 : Work.Final.RootArc.critHeight (Work.Final.ofRootParabolic R.d₀) = 0 := by
    rw [Work.FlowerGlue.critHeight_ofRootParabolic_eq_critHeight R.d₀]
    exact R.hcrit0
  rw [h1]
  exact h2

/-- **The `critHeight_zero` field of `Work.PARIMPL2.Lavaurs.LavaursInputs`.**  The Fatou coordinate
of the entry point of the critical orbit is real. -/
theorem critHeight_zero (R : PointedRoot cb db)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft R.c₀)
      (Work.PARIMPL.gtc R.c₀) R.d₀.z₁) (P : Work.PARIMPL.ParNormal R.d₀) :
    (fl.φa (Work.PARIMPL.entryPt P (Work.PARIMPL.nEnter R.d₀ fl.toParabolicFlower) R.c₀)).im = 0 :=
  R.critHeight_eq_zero fl

/-- The root arc of the pointed root at a given repaired flower. -/
def arc (R : PointedRoot cb db)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft R.c₀)
      (Work.PARIMPL.gtc R.c₀) R.d₀.z₁) : Work.Final.RootArc R.c₀ :=
  ⟨R.d₀, fl.toParabolicFlower⟩

end PointedRoot

/-- **The pointed root exists at every root-parabolic parameter** — this is
`Work.FQC.heightShift` with the witness of its `transfer_parabolic` call exposed.  The flower,
the petal input, the phase normalisation and the petal-direction input are exactly those of
`Work.MandelFinal.rootArcHeightZero_of_rootParabolic`
(`Work.FlowerGlue.exists_petalInput` → `Work.FQCInputs.shiftFlower` ∘ `phaseShift` →
`Work.FQCInputs.phase_normalised` → `Work.FQCInputs.simpleTransfer_all`), with the Fatou-coordinate
uniqueness `Work.FlowerGlue.fatouUnique` and the target height `0`. -/
theorem nonempty_pointedRoot {c : ℂ} (d : Work.EL.RootParabolic c) : Nonempty (PointedRoot c d) := by
  obtain ⟨fl₀, hpetal₀⟩ := Work.FlowerGlue.exists_petalInput d
  obtain ⟨hpetal₀⟩ := hpetal₀
  obtain ⟨c₂, θ, hconj, hdecay, h0, d₂, hz, hcrit⟩ :=
    heightShift_transfer d
      (Work.FQCInputs.shiftFlower (Work.FQCInputs.phaseShift d fl₀.toParabolicFlower)
        fl₀.toParabolicFlower)
      (Work.FQCInputs.petalShift hpetal₀ (Work.FQCInputs.phaseShift d fl₀.toParabolicFlower))
      (Work.FQCInputs.phase_normalised d fl₀.toParabolicFlower)
      (Work.FQCInputs.simpleTransfer_all d _ _)
      Work.FlowerGlue.fatouUnique 0
  exact ⟨⟨c₂, θ, hconj, hdecay, h0, d₂, hz, hcrit⟩⟩

/-- The pointed root of a root-parabolic parameter. -/
noncomputable def pointedRoot {c : ℂ} (d : Work.EL.RootParabolic c) : PointedRoot c d :=
  (nonempty_pointedRoot d).some

end Work.MandelWire
