/-
# `Work.FQCInputs.HeightShift` — the height-shift theorem with MNS's phase normalisation
# discharged

`Work.FQC.heightShift` (module `Submission/Work/FQC/Height.lean`) produces, for every real `h`,
a root-parabolic parameter of critical Écalle height `h`, from the four inputs of
`Submission/Work/FQC/NOTES.md` §4:

* `hpetal : PetalInput d fl` (home area `FatouCoordFix`);
* `hphase : saw ((fl.φa (phasePoint d fl)).re) = 1/2` — **MNS's phase normalisation**;
* `hsimple : ∀ t, SimpleTransfer d fl hpetal.Pg t` — the petal-direction input;
* `hU : FatouUnique`.

The present file discharges `hphase`, using the renormalised flower of `Defs.lean`: for
`s = phaseShift d fl = 1/4 - Re (φa (tap))` the flower `shiftFlower s fl` satisfies

* the normalisation `saw ((fl'.φa (phasePoint d fl')).re) = 1/2` (`phase_normalised`);
* the same petal, the same petal input (`petalShift`) and the same critical Écalle height
  (`critHeightAt_shiftFlower`).

The remaining input is the *shift-invariant* form of the petal-direction input,
`SimpleTransferPetal d` (`SimpleTransfer.lean`): the transported parabolic point is simple for
*every* flower of `d` equipped with a petal input (equivalently: for every choice of Fatou
coordinate).  That is exactly the shape of the classical statement (the multiplicity of a
parabolic germ is a topological invariant), and it is what makes the renormalisation free of
charge.  `SimpleTransferPetal` is *proved* from the single classical local input
`LeauFatouInput` by `simpleTransferPetal_of_leauFatou`, so that `heightShift_leauFatou` below
discharges **both** `hphase` and `hsimple` modulo the local theory of parabolic germs.

* `Work.FQCInputs.heightShift_normalised` — FQC's theorem with `hphase` discharged;
* `Work.FQCInputs.exists_critHeight_zero_normalised` — the `h = 0` case (the `FinalInputs`
  fields `c₀`, `arc`, `critHeight_zero`);
* `Work.FQCInputs.exists_phase_normalised_data` — the renormalisation package;
* `Work.FQCInputs.height_after_normalised` — the transported height shift `+ t/2` for the
  renormalised flower, i.e. MNS's Theorem 3.2 in the form used by the drive.
-/
import Mathlib
import Submission.Work.FQC.Height
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQCInputs.SimpleTransfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The renormalisation package -/

/-- **The renormalisation package.**  Every flower admits a real shift `s` such that

* MNS's phase normalisation holds at the tap point;
* the critical Écalle height is unchanged;
* the petal input transports (the fundamental domain itself is unchanged).

This is the sense in which the normalisation of the phase is *a choice of the Fatou
coordinate*: the height, being `Im φa`, is invariant. -/
theorem exists_phase_normalised_data {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    ∃ s : ℝ,
      Work.FQC.saw (((shiftFlower s fl).φa
          (Work.FQC.phasePoint d (shiftFlower s fl))).re) = 1 / 2 ∧
      Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl))
        = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) ∧
      (petalShift hpetal s).Pg = hpetal.Pg :=
  ⟨phaseShift d fl, phase_normalised d fl, critHeightAt_shiftFlower d (phaseShift d fl) fl, rfl⟩

/-! ## 2. The height-shift theorem without the phase hypothesis -/

/-- **The height-shift theorem, with MNS's phase normalisation discharged.**

For every root-parabolic parameter `d` carrying a flower, a petal input and the *shift-invariant*
petal-direction input (and Fatou uniqueness), every real number is the critical Écalle height of
some root-parabolic parameter — the conclusion of `Work.FQC.heightShift`, but with the phase
hypothesis replaced by the renormalised flower of `Work.FQCInputs.shiftFlower`. -/
theorem heightShift_normalised {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl)
    (hall : SimpleTransferPetal d) (hU : Work.FQC.FatouUnique) (h : ℝ) :
    ∃ c₂ : ℂ, ∃ d₂ : RootParabolic c₂, Work.FQC.critHeight d₂ = h :=
  Work.FQC.heightShift d (shiftFlower (phaseShift d fl) fl)
    (petalShift hpetal (phaseShift d fl)) (phase_normalised d fl)
    (fun t => hall.transfer (shiftFlower (phaseShift d fl) fl)
      (petalShift hpetal (phaseShift d fl)) t) hU h

/-- The `h = 0` case: the parabolic arc has a parameter of critical Écalle height zero — the
`FinalInputs` fields `c₀`, `arc`, `critHeight_zero`, with the phase normalisation discharged. -/
theorem exists_critHeight_zero_normalised {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl)
    (hall : SimpleTransferPetal d) (hU : Work.FQC.FatouUnique) :
    ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, Work.FQC.critHeight d₀ = 0 :=
  heightShift_normalised d fl hpetal hall hU 0

/-! ## 4. The height-shift theorem with the phase normalisation discharged

MNS's Theorem 3.2 with MNS's phase normalisation *discharged*: the caller supplies the
petal-direction input for the renormalised flower (equivalently, by `SimpleTransferPetal d`, for
every flower) — the remaining inputs are then the petal input and Fatou uniqueness.
-/

/-- **The height-shift theorem, with the phase normalisation discharged and the petal-direction
input in the explicit "shifted flower" form.**  This is `Work.FQC.heightShift` with `hphase`
removed and with `hsimple` stated at the renormalised flower `shiftFlower (phaseShift d fl) fl` —
the flower for which the phase at the tap point is exactly `1/4`. -/
theorem heightShift_shifted {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl)
    (hsimple : ∀ t : ℝ,
      Work.FQC.SimpleTransfer d (shiftFlower (phaseShift d fl) fl)
        (petalShift hpetal (phaseShift d fl)).Pg t)
    (hU : Work.FQC.FatouUnique) (h : ℝ) :
    ∃ c₂ : ℂ, ∃ d₂ : RootParabolic c₂, Work.FQC.critHeight d₂ = h :=
  Work.FQC.heightShift d (shiftFlower (phaseShift d fl) fl)
    (petalShift hpetal (phaseShift d fl)) (phase_normalised d fl) hsimple hU h

/-- The `h = 0` case of `heightShift_shifted`: the `FinalInputs` fields `c₀`, `arc`,
`critHeight_zero`, with MNS's phase normalisation discharged. -/
theorem exists_critHeight_zero_shifted {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl)
    (hsimple : ∀ t : ℝ,
      Work.FQC.SimpleTransfer d (shiftFlower (phaseShift d fl) fl)
        (petalShift hpetal (phaseShift d fl)).Pg t)
    (hU : Work.FQC.FatouUnique) :
    ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, Work.FQC.critHeight d₀ = 0 :=
  heightShift_shifted d fl hpetal hsimple hU 0

/-! ## 5. The transported height shift for the renormalised flower

MNS's Theorem 3.2 in the form used by the drive: after the deformation with the renormalised
flower, the critical Écalle height of the transported parameter is shifted by exactly `t/2`.
This is `Work.FQC.height_after_pg` at the renormalised flower, whose phase is normalised by
construction, combined with the height invariance `critHeightAt_shiftFlower`. -/

/-- **The transported critical Écalle height of the renormalised flower.**  For any conjugacy
`θ = principal (muQC d fl' P t)` of `T_c` to `T_{c₂}` fixing `0` and any root-parabolic
`d₂ : RootParabolic c₂` with `d₂.z₁ = θ z₁`, there is Écalle data of `d₂` of critical height
`critHeightAt d (EcalleData.ofFlower d fl) + t/2`.

Everything FQC uses is invariant under the shift: the hypothesis `hphase` of
`Work.FQC.height_after_pg` is discharged for the renormalised flower, and the height of `d` is
the same as before the renormalisation. -/
theorem height_after_normalised {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) {c₂ : ℂ} (d₂ : RootParabolic c₂)
    (hconj : ∀ z : ℂ,
      Work.MRMT.Found.principal (Work.FQC.muQC d (shiftFlower (phaseShift d fl) fl)
        (petalShift hpetal (phaseShift d fl)).Pg t) (Tantibar c z)
      = Tantibar c₂ (Work.MRMT.Found.principal (Work.FQC.muQC d (shiftFlower (phaseShift d fl) fl)
        (petalShift hpetal (phaseShift d fl)).Pg t) z))
    (h0 : (Work.MRMT.Found.principal (Work.FQC.muQC d (shiftFlower (phaseShift d fl) fl)
        (petalShift hpetal (phaseShift d fl)).Pg t)) 0 = 0) :
    ∃ E₂ : Work.FQC.EcalleData d₂,
      Work.FQC.critHeightAt d₂ E₂
        = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) + t / 2 := by
  obtain ⟨E₂, hE₂⟩ := Work.FQC.height_after_pg d (shiftFlower (phaseShift d fl) fl)
    (petalShift hpetal (phaseShift d fl)) t d₂ hconj h0 (phase_normalised d fl)
  exact ⟨E₂, by rw [hE₂, critHeightAt_shiftFlower]⟩

end Work.FQCInputs

end
