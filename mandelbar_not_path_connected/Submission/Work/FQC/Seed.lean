/-
# `Work.FQC.Seed` — the arc has a parameter of critical Écalle height zero

This is the piece of `Work.Final.FinalInputs` owned by this area: the fields `c₀`, `arc` and
`critHeight_zero`.  Combining

* `Work.FSeed.exists_rootParabolic` (a root-parabolic seed exists, from the classical input bundle
  `Work.FSeed.FSeedInput`), and
* `Work.FQC.heightShift` with the prescribed height `0` (MNS Theorem 3.2),

gives a root-parabolic parameter whose critical Écalle height vanishes.  The bridge between
`Work.FQC.critHeight` and the root-arc height of the `Final` area is
`Work.Final.critHeight_eq_FQC`, so `FinalInputs.critHeight_zero` is
`Work.FQC.exists_critHeight_zero_of` transported along that identification.
-/
import Mathlib
import Submission.Work.FQC.Flower
import Submission.Work.FQC.Height

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- **The height-zero parameter of the parabolic arc.**  Given a root-parabolic seed together with
the inputs of the deformation at that seed (the petal structure, MNS's phase normalisation, the
petal-direction input and the uniqueness of the Fatou coordinate), there is a root-parabolic
parameter whose critical Écalle height is `0`. -/
theorem exists_critHeight_zero_of {c₁ : ℂ} (d₁ : RootParabolic c₁)
    (fl : Work.FatouCoord.ParabolicFlower (F c₁) ((Tantibar c₁)^[5]) d₁.z₁)
    (hpetal : PetalInput d₁ fl)
    (hphase : saw ((fl.φa (phasePoint d₁ fl)).re) = 1 / 2)
    (hsimple : ∀ t : ℝ, SimpleTransfer d₁ fl hpetal.Pg t)
    (hU : FatouUnique) :
    ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, critHeight d₀ = 0 :=
  heightShift d₁ fl hpetal hphase hsimple hU 0

/-- The same, from the existential form of the seed: a root-parabolic parameter carrying the
inputs of the deformation.  `Work.FSeed.exists_rootParabolic` provides the root-parabolic part
(the flower and the inputs being exports of `FatouCoord` / `FatouCoordFix`). -/
theorem exists_critHeight_zero
    (h : ∃ (c₁ : ℂ) (d₁ : RootParabolic c₁)
        (fl : Work.FatouCoord.ParabolicFlower (F c₁) ((Tantibar c₁)^[5]) d₁.z₁)
        (hpetal : PetalInput d₁ fl),
        saw ((fl.φa (phasePoint d₁ fl)).re) = 1 / 2 ∧
          (∀ t : ℝ, SimpleTransfer d₁ fl hpetal.Pg t) ∧ FatouUnique) :
    ∃ c₀ : ℂ, ∃ d₀ : RootParabolic c₀, critHeight d₀ = 0 := by
  obtain ⟨c₁, d₁, fl, hpetal, hphase, hsimple, hU⟩ := h
  exact exists_critHeight_zero_of d₁ fl hpetal hphase hsimple hU

end Work.FQC

end
