/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FlowerGlue.FatouUnique
import Submission.Work.FlowerGlue.PetalInput
import Submission.Work.Final.FQCBridge
import Submission.Work.FinalFix.FQCRoot
import Submission.Work.FQC.Seed
import Submission.Work.FinalFix.RootExport
import Submission.Work.FatouCoordFix.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.Coherence` — one flower for the arc, PARIMPL and ELRig

The ledger's §6 "flower-coherence gap": `Work.Final.RootArc` stores the Leau–Fatou flower of its
parabolic point as a *field*, and the flower that the final wiring actually gets is
`Work.Final.ofRootParabolic`'s, i.e. an arbitrary `Classical.choice` of
`Work.FatouCoord.Flower.exists_parabolicFlower`.  The repaired flower
`Work.FatouCoordFix.ParabolicFlowerFix` — the one that carries the `g`-invariant half-petal `Pg`,
the Abel equation and the measurability of `Pg.indicator φa` that PARIMPL's `fix` and ELRig's
consumers need — is a *different* object.  The ledger offers two ways out: prove the height
transfer between the flowers, or restate the root-arc data with `ParabolicFlowerFix`.

This file does both, with the *smaller* change:

* **the transfer**: `Work.FlowerGlue.critHeight_eq_of_fatouUnique` — two root arcs at the *same*
  root-parabolic data `d` have the same critical height, from the corrected uniqueness
  (`Work.FlowerGlue.critHeightAt_eq_of_tendsto`) in the packaged form `Work.FQC.FatouUnique`.
  In particular the height computed with the repaired flower and with any other flower agree;
* **the restatement, without touching `Work.Final`**: `Work.FlowerGlue.RootArcFix` — the same
  `Sigma`-type as `Work.Final.RootArc` but with a `ParabolicFlowerFix` (which *is* a
  `ParabolicFlower`, so it coerces, and `RootArcFix.toRootArc` recovers the final vocabulary for
  free).  `Work.FlowerGlue.ofRootParabolicFix` is the arc whose flower is the repaired one (so
  that "root's arc and PARIMPL/ELRig use ONE flower" needs only that definition at the call
  site), and `Work.FlowerGlue.rootArcFixHeightZero_iff` shows that FQC's export
  `Work.FinalFix.RootArcHeightZero` is *equivalent* to its `RootArcFix`-flavoured version
  (`hU : FatouUnique` supplies the height transfer in one direction);
* `Work.FlowerGlue.RootArcFixHeightZero.of_FQC_critHeight` — the `RootArcFix`-flavoured form of
  `Work.FinalFix.RootArcHeightZero.of_FQC_critHeight`, i.e. FQC's height-`0` parameter read off
  the **repaired** flower: this is the form in which the seed should be instantiated once the
  petal input comes from `Work.FlowerGlue.exists_petalInput_small`.

## Documented choice

The *smaller* change is the second one (one `def`, no edit anywhere else): the height-transfer
route would require `Work.Final.ofRootParabolic` (and hence `Work.Final.RootArc`) to be changed,
which ripples through `FinalFix`, `PARIMPL`, `ELRig` and `GATE2`.  Using
`Work.FlowerGlue.ofRootParabolicFix` at the `root` field of `Work.Final.FinalInputs` gives root's
arc *the repaired flower*, and by the transfer theorem above this costs nothing: the critical
height it computes is the same number as before (given `hU`).
-/

open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)
open Work.FQC (EcalleData critHeightAt FatouUnique)

noncomputable section

/-! ## 1. The height transfer -/

/-- The content of `Work.FQC.FatouUnique`, as a plain proposition (so that it can be passed
around and instantiated without the structure wrapper). -/
def HasHeightTransfer : Prop :=
  ∀ {c : ℂ} (d : RootParabolic c) (E E' : EcalleData d), critHeightAt d E = critHeightAt d E'

theorem fatouUnique_iff_hasHeightTransfer : FatouUnique ↔ HasHeightTransfer :=
  ⟨fun h => h.eq, fun h => ⟨h⟩⟩

theorem hasHeightTransfer_of_fatouUnique (hU : FatouUnique) : HasHeightTransfer :=
  fatouUnique_iff_hasHeightTransfer.mp hU

/-- **The height bridge `Work.Final.RootArc ↔ Work.FQC`** (the `Final` area's
`critHeight_eq_FQC`): the critical height of a root arc is the `FQC` critical height of its
flower's Écalle data. -/
theorem critHeight_FQC_apply {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.Final.RootArc.critHeight (⟨d, fl⟩ : Work.Final.RootArc c)
      = critHeightAt d (EcalleData.ofFlower d fl) :=
  Work.Final.critHeight_eq_FQC d fl

/-- **Two flowers of the same root-parabolic data give the same critical height** — the
flower-coherence statement of ledger §6, from the corrected uniqueness. -/
theorem critHeight_eq_of_fatouUnique {c : ℂ} (d : RootParabolic c)
    (fl fl' : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hU : FatouUnique) :
    Work.Final.RootArc.critHeight (⟨d, fl⟩ : Work.Final.RootArc c)
      = Work.Final.RootArc.critHeight (⟨d, fl'⟩ : Work.Final.RootArc c) := by
  rw [critHeight_FQC_apply d fl, critHeight_FQC_apply d fl']
  exact hU.eq d _ _

/-- **The height transfer to the repaired flower**: the root arc whose flower is the
`FatouCoordFix` one has the same critical height as the root arc with any other flower. -/
theorem critHeight_eq_of_fix {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁)
    (fl' : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hU : FatouUnique) :
    Work.Final.RootArc.critHeight
        (⟨d, (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)⟩ :
          Work.Final.RootArc c)
      = Work.Final.RootArc.critHeight (⟨d, fl'⟩ : Work.Final.RootArc c) :=
  critHeight_eq_of_fatouUnique d _ fl' hU

/-! ## 2. The repaired-flower root arc -/

/-- The root arc whose flower is the **repaired** one (`FatouCoordFix`), coerced to the
`ParabolicFlower` that `Work.Final.RootArc` stores.  Every field of `Work.Final.RootArc` is
available, and the repaired flower's extra fields (`Pg`, `φa_shift`, the measurability of
`Pg.indicator φa`, the `g`-invariance) are recovered through
`Work.FlowerGlue.rootFixFlower` below. -/
noncomputable def ofRootParabolicFix {c : ℂ} (d : RootParabolic c) : Work.Final.RootArc c :=
  ⟨d, ↑(Classical.choice (Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix (F c)
      ((Tantibar c)^[5]) d.z₁
      (Work.FQC.differentiable_F c) (Work.FQC.differentiableAt_star_comp_g c)
      (Work.FQC.g_comp_g c) (Work.FQC.F_fix c d) (Work.FQC.deriv_F_eq_one c d) d.simple
      d.per_half))⟩

/-- The repaired flower of a root-parabolic parameter, in the `ParabolicFlowerFix` vocabulary. -/
noncomputable def rootFixFlower {c : ℂ} (d : RootParabolic c) :
    Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁ :=
  Classical.choice (Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix (F c)
    ((Tantibar c)^[5]) d.z₁
    (Work.FQC.differentiable_F c) (Work.FQC.differentiableAt_star_comp_g c)
    (Work.FQC.g_comp_g c) (Work.FQC.F_fix c d) (Work.FQC.deriv_F_eq_one c d) d.simple d.per_half)

/-- `Work.FlowerGlue.ofRootParabolicFix` is the coerced version of
`Work.FlowerGlue.rootFixFlower` — so the "one flower" used by root's arc is available in both
vocabularies. -/
theorem ofRootParabolicFix_fl {c : ℂ} (d : RootParabolic c) :
    (ofRootParabolicFix d).fl
      = (rootFixFlower d : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) := rfl

/-- The Abel equation of the arc's flower, when the arc is the repaired one. -/
theorem ofRootParabolicFix_φa_shift {c : ℂ} (d : RootParabolic c) {z : ℂ}
    (hz : z ∈ (rootFixFlower d).Pa) :
    (rootFixFlower d).φa (F c z) = (rootFixFlower d).φa z + 1 :=
  (rootFixFlower d).φa_shift z hz

/-- The `g`-invariant half-petal of the repaired arc's flower. -/
theorem ofRootParabolicFix_Pg_mapsTo_g {c : ℂ} (d : RootParabolic c) {z : ℂ}
    (hz : z ∈ (rootFixFlower d).Pg) : (Tantibar c)^[5] z ∈ (rootFixFlower d).Pg :=
  (rootFixFlower d).mapsTo_g_Pg hz

/-- **The critical height of the repaired arc** is the `FQC` critical height of its (repaired)
flower's Écalle data. -/
theorem ofRootParabolicFix_critHeight_eq {c : ℂ} (d : RootParabolic c) :
    Work.Final.RootArc.critHeight (ofRootParabolicFix d)
      = critHeightAt d (EcalleData.ofFlower d
          (rootFixFlower d : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)) :=
  Work.Final.critHeight_eq_FQC d _

/-- **The repaired arc computes the same height** as `Work.Final.ofRootParabolic` (given `hU`). -/
theorem ofRootParabolicFix_critHeight_eq_ofRootParabolic {c : ℂ} (d : RootParabolic c)
    (hU : FatouUnique) :
    Work.Final.RootArc.critHeight (ofRootParabolicFix d) = Work.Final.RootArc.critHeight (Work.Final.ofRootParabolic d) :=
  critHeight_eq_of_fatouUnique d _ _ hU

/-! ## 3. The repaired-flower form of FQC's export -/

/-- The root-arc data with the **repaired** flower, in the `Sigma`-form of `Work.Final.RootArc`
(so that `Work.FinalFix.RootArcHeightZero` can be restated without touching the `Final` area). -/
abbrev RootArcFix (c : ℂ) : Type :=
  Sigma (fun d : RootParabolic c =>
    Work.FatouCoordFix.ParabolicFlowerFix (F c) ((Tantibar c)^[5]) d.z₁)

namespace RootArcFix

/-- The `Final`-vocabulary root arc of a repaired one. -/
def toRootArc {c : ℂ} (A : RootArcFix c) : Work.Final.RootArc c :=
  ⟨A.1, ↑A.2⟩

/-- The reversed direction: the repaired flower of a root-parabolic parameter. -/
noncomputable def ofRootParabolic {c : ℂ} (d : RootParabolic c) : RootArcFix c :=
  ⟨d, rootFixFlower d⟩

theorem toRootArc_ofRootParabolic {c : ℂ} (d : RootParabolic c) :
    (ofRootParabolic d).toRootArc = ofRootParabolicFix d := rfl

end RootArcFix

/-- FQC's export, read off the **repaired** flower. -/
def RootArcFixHeightZero : Prop :=
  ∃ c : ℂ, ∃ A : RootArcFix c, Work.Final.RootArc.critHeight A.toRootArc = 0

/-- The `RootArcFix`-flavoured export implies the `Final` one (no transfer needed). -/
theorem rootArcHeightZero_of_rootArcFixHeightZero (h : RootArcFixHeightZero) :
    Work.FinalFix.RootArcHeightZero := by
  obtain ⟨c, A, hA⟩ := h
  exact ⟨c, A.toRootArc, hA⟩

/-- Conversely, the `Final` export implies the `RootArcFix`-flavoured one **given the height
transfer** (`hU : FatouUnique`): pass to the repaired flower at the same root-parabolic data. -/
theorem rootArcFixHeightZero_of_rootArcHeightZero (hU : FatouUnique)
    (h : Work.FinalFix.RootArcHeightZero) : RootArcFixHeightZero := by
  obtain ⟨c, A, hA⟩ := h
  refine ⟨c, RootArcFix.ofRootParabolic A.d, ?_⟩
  rw [RootArcFix.toRootArc_ofRootParabolic]
  have h1 : Work.Final.RootArc.critHeight (ofRootParabolicFix A.d)
      = critHeightAt A.d (EcalleData.ofFlower A.d
          (rootFixFlower A.d : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) A.d.z₁)) :=
    ofRootParabolicFix_critHeight_eq A.d
  have h2 : Work.Final.RootArc.critHeight A
      = critHeightAt A.d (EcalleData.ofFlower A.d A.fl) :=
    critHeight_FQC_apply A.d A.fl
  calc Work.Final.RootArc.critHeight (ofRootParabolicFix A.d)
      = critHeightAt A.d (EcalleData.ofFlower A.d (rootFixFlower A.d :
          Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) A.d.z₁)) := h1
    _ = critHeightAt A.d (EcalleData.ofFlower A.d A.fl) := hU.eq A.d _ _
    _ = Work.Final.RootArc.critHeight A := h2.symm
    _ = 0 := hA

/-- **The two forms of FQC's export are equivalent**, given the height transfer. -/
theorem rootArcFixHeightZero_iff (hU : FatouUnique) :
    RootArcFixHeightZero ↔ Work.FinalFix.RootArcHeightZero :=
  ⟨rootArcHeightZero_of_rootArcFixHeightZero, rootArcFixHeightZero_of_rootArcHeightZero hU⟩

/-- **FQC's height-`0` parameter, with the repaired flower.**  This is the `RootArcFix`-flavoured
form of `Work.FinalFix.RootArcHeightZero.of_FQC_critHeight`: from FQC's export
(`∃ c, ∃ d : RootParabolic c, Work.FQC.critHeight d = 0`) it produces the root-arc data whose
flower is the *repaired* one and whose critical height vanishes.  The height transfer (`hU`) is
the only input beyond `Work.FinalFix.RootArcHeightZero`. -/
theorem RootArcFixHeightZero.of_FQC_critHeight {c₀ : ℂ} (d₀ : RootParabolic c₀)
    (hU : FatouUnique) (h : Work.FQC.critHeight d₀ = 0) : RootArcFixHeightZero :=
  rootArcFixHeightZero_of_rootArcHeightZero hU
    (Work.FinalFix.RootArcHeightZero.of_FQC_critHeight d₀ hU h)

/-- The same, from the existential form of FQC's export. -/
theorem RootArcFixHeightZero.of_FQC_exists (hU : FatouUnique)
    (h : ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, Work.FQC.critHeight d₀ = 0) :
    RootArcFixHeightZero :=
  rootArcFixHeightZero_of_rootArcHeightZero hU
    (Work.FinalFix.RootArcHeightZero.of_FQC_exists hU h)

/-- **The whole `FQC` seed chain, with the repaired flower.**  From the seed data of
`Work.FQC.exists_critHeight_zero_of` (a root-parabolic parameter with its flower, the petal input —
which `Work.FlowerGlue.exists_petalInput_small` provides for the repaired flower —, the phase
normalisation, the petal-direction input and the height uniqueness) this produces FQC's export in
its `RootArcFix` form, i.e. root-arc data whose flower is the **repaired** one.  This is the one
theorem that replaces the three-step chain `Work.FQC.exists_critHeight_zero_of` →
`Work.FinalFix.RootArcHeightZero.of_FQC_exists` → `rootArcFixHeightZero_of_rootArcHeightZero` at
the call site. -/
theorem RootArcFixHeightZero.of_seed {c₁ : ℂ} (d₁ : RootParabolic c₁)
    (fl : Work.FatouCoord.ParabolicFlower (F c₁) ((Tantibar c₁)^[5]) d₁.z₁)
    (hpetal : Work.FQC.PetalInput d₁ fl)
    (hphase : Work.FQC.saw ((fl.φa (Work.FQC.phasePoint d₁ fl)).re) = 1 / 2)
    (hsimple : ∀ t : ℝ, Work.FQC.SimpleTransfer d₁ fl hpetal.Pg t)
    (hU : FatouUnique) : RootArcFixHeightZero :=
  RootArcFixHeightZero.of_FQC_exists hU
    (Work.FQC.exists_critHeight_zero_of d₁ fl hpetal hphase hsimple hU)

end

end Work.FlowerGlue
