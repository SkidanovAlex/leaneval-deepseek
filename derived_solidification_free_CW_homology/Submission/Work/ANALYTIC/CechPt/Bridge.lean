import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.CechPt.Setup
import Submission.Work.ANALYTIC.CechPt.Nerve
import Submission.Work.ANALYTIC.CechPt.cech_descent

/-!
# Bridging the Čech descent statement to the cochain complex `cechComplex`

`Work.ANALYTIC.CechPt.cech_descent` proves that for an epimorphism `β : X ⟶ Y` of light
condensed sets with `X` light profinite the augmentation `ε` of the *chain* complex
`AlternatingFaceMapComplex.obj (ℤ[X^•_Y])` is a quasi-isomorphism.  This module transfers that
statement to the cochain complex `cechComplex β` (concentrated in degrees `≤ 0`) used everywhere
else:

* `quasiIso_cechAug` : `QuasiIso (cechAug β)`;
* `solidEquiv_cechAug` : `SolidEquiv (Q.map (cechAug β))` — a quasi-isomorphism is an
  isomorphism of the derived category, hence a solid-equivalence.
-/

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

variable {X : LightProfinite.{0}} {Y : LightCondSet.{0}} (β : LightProfinite.toCondensed X ⟶ Y)

/-- The chain-level augmentation of the Čech nerve, as a morphism of `ℕ`-graded chain complexes. -/
noncomputable abbrev cechEps :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (cechNerve β ⋙ free ℤ) ⟶
      (ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
      (Arrow.augmentedCechNerve (Arrow.mk β)))

/-- `cechComplex β` is the extension of the chain complex `ℤ[X^•_Y]` along `down ℕ ↪ up ℤ`. -/
theorem cechComplex_eq_extend :
    cechComplex β = (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).obj
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechNerve β ⋙ free ℤ)) := rfl

/-- The Čech augmentation is a quasi-isomorphism of cochain complexes. -/
theorem quasiIso_cechAug (hβ : Epi β) : QuasiIso (cechAug β) := by
  have hε : QuasiIso (cechEps β) := cech_descent β hβ
  have hmap : QuasiIso ((ComplexShape.embeddingDownNat.extendFunctor LightCondAb).map
      (cechEps β)) := HomologicalComplex.quasiIso_extendMap_iff _ _ |>.mpr hε
  have hiso : QuasiIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      ((free ℤ).obj Y) 0 0 (by simp)).hom := inferInstance
  rw [cechAug]
  exact (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)).comp_mem _ _ hmap hiso

end Work.ANALYTIC.CechPt
