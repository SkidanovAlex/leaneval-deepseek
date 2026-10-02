/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.Final.RootArc
import Submission.Work.FinalFix.FQCRoot
import Submission.Work.FinalFix.RootExport
import Submission.Work.FQC.Seed
import Submission.Work.FlowerGlue.FatouUniqueProof

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.SameWitness` — the two choices of the flower are the same term

`Work.Final.ofRootParabolic d = ⟨d, Classical.choice (Work.Final.exists_flower d)⟩` and
`Work.FQC.flowerOf d = Classical.choice (exists_parabolicFlower …)` are two `Classical.choice`s
out of two *proofs of the same proposition* — `Nonempty (ParabolicFlower (F c) ((T_c)^5) d.z₁)`,
which is a `Prop`.  Hence the two proofs are equal (`Subsingleton.elim`) and so are their choices:
**`Work.FlowerGlue.flowerOf_eq_ofRootParabolic_fl`**.

Consequently the bridge lemma of `Work.FinalFix.FQCRoot` — the identity
`(ofRootParabolic d₀).critHeight = critHeightAt d₀ (ofFlower d₀ (ofRootParabolic d₀).fl)` — is
`rfl`-level, and `RootArcHeightZero` follows from FQC's export `∃ c₀ d₀, critHeight d₀ = 0`
**without** the primitive `Work.FQC.FatouUnique`
(`Work.FlowerGlue.RootArcHeightZero_of_FQC_critHeight`, `…_of_FQC_exists`).
-/

open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)
open Work.FQC (EcalleData critHeightAt critHeight)

noncomputable section

variable {c : ℂ}

/-- **The flower chosen by `Work.Final.ofRootParabolic` is the flower chosen by
`Work.FQC.flowerOf`.**  Both are `Classical.choice` applied to a proof of the *same* `Nonempty`
proposition, so they agree by proof irrelevance. -/
theorem flowerOf_eq_ofRootParabolic_fl (d : RootParabolic c) :
    Work.FQC.flowerOf d = (Work.Final.ofRootParabolic d).fl :=
  congrArg Classical.choice (Subsingleton.elim _ _)

/-- The critical height of the root arc `Work.Final.ofRootParabolic d` is the `FQC` critical
height of `d` — with no uniqueness input (`Work.Final.critHeight_eq_FQC` plus the choice
identification above). -/
theorem critHeight_ofRootParabolic_eq_critHeight (d : RootParabolic c) :
    (Work.Final.ofRootParabolic d).critHeight = Work.FQC.critHeight d := by
  have h2 : (Work.Final.ofRootParabolic d).critHeight
      = critHeightAt d (EcalleData.ofFlower d (Work.Final.ofRootParabolic d).fl) :=
    Work.Final.critHeight_eq_FQC d (Work.Final.ofRootParabolic d).fl
  rw [h2, ← flowerOf_eq_ofRootParabolic_fl d]
  rfl

/-- **The `root` field of `FinalInputs` from FQC's export, without `FatouUnique`.**  This is
`Work.FinalFix.RootArcHeightZero.of_FQC_critHeight` with the primitive `hU : FatouUnique` removed:
the only use of `hU` there was exactly the identification supplied by
`flowerOf_eq_ofRootParabolic_fl`. -/
theorem RootArcHeightZero_of_FQC_critHeight {c₀ : ℂ} (d₀ : RootParabolic c₀)
    (h : Work.FQC.critHeight d₀ = 0) : Work.FinalFix.RootArcHeightZero := by
  refine ⟨c₀, Work.Final.ofRootParabolic d₀, ?_⟩
  rw [critHeight_ofRootParabolic_eq_critHeight]
  exact h

/-- The same, from the existential form of FQC's seed theorem. -/
theorem RootArcHeightZero_of_FQC_exists
    (h : ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, Work.FQC.critHeight d₀ = 0) :
    Work.FinalFix.RootArcHeightZero := by
  obtain ⟨c₀, d₀, hd⟩ := h
  exact RootArcHeightZero_of_FQC_critHeight d₀ hd

/-! ## 3. The `root` field of `FinalInputs`, unconditionally -/

/-- **The `root` field of `Work.Final.FinalInputs` from the FQC seed data — with no hypothesis
beyond the seed's.**  This is `Work.FQC.exists_critHeight_zero_of` (the MNS deformation) with
`hU := Work.FlowerGlue.fatouUnique`, transported to the `Final` vocabulary by
`RootArcHeightZero_of_FQC_exists` above.  The seed data are a root-parabolic parameter, a flower
of its characteristic parabolic point, the petal input, MNS's phase normalisation and the
petal-direction input. -/
theorem RootArcHeightZero_of_seed {c₁ : ℂ} (d₁ : RootParabolic c₁)
    (fl : Work.FatouCoord.ParabolicFlower (F c₁) ((Tantibar c₁)^[5]) d₁.z₁)
    (hpetal : Work.FQC.PetalInput d₁ fl)
    (hphase : Work.FQC.saw ((fl.φa (Work.FQC.phasePoint d₁ fl)).re) = 1 / 2)
    (hsimple : ∀ t : ℝ, Work.FQC.SimpleTransfer d₁ fl hpetal.Pg t) :
    Work.FinalFix.RootArcHeightZero :=
  RootArcHeightZero_of_FQC_exists
    (Work.FQC.exists_critHeight_zero_of d₁ fl hpetal hphase hsimple fatouUnique)

end

end Work.FlowerGlue
