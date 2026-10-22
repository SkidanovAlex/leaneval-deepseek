/-
AREA RESOL — the functorial resolution of a light condensed abelian group by atoms.

We use the zero-preserving cover `redCoverFunctor` of `Submission/Work/RESOL/ReducedCover.lean`
(given by a skeleton of the light profinite sets) and apply Mathlib's `LeftResolution`
construction to it, with `ι = 𝟭 LightCondAb`.  This produces a functor
`X : LightCondAb ⤳ ChainComplex LightCondAb ℕ` whose values are functorial resolutions by
atomic sums.

Main results:
* `skelI`, `skelS`, `skelS_retract` : a small skeleton of the light profinite sets;
* `cov`, `covMap` : the zero-preserving atom cover and its epimorphism;
* `LR` : the `LeftResolution` structure;
* `X` : the resolution functor;
* `isZero_X_of_isZero`, `augmentation`, `isAtomicSum_X`, `quasiIso_augmentation` :
  the properties of `X` used for the resolution theorem.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.ReducedCover

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

/-! ## A skeleton of the light profinite sets -/

/-- The index type of a small skeleton of the light profinite sets. -/
noncomputable def skelI : Type := Classical.choose exists_atomSkeleton

/-- The small skeleton of the light profinite sets. -/
noncomputable def skelS : skelI → LightProfinite.{0} :=
  Classical.choose (Classical.choose_spec exists_atomSkeleton)

/-- Every light profinite set is a retract of a skeleton element. -/
theorem skelS_retract (X : LightProfinite.{0}) :
    ∃ (i : skelI) (e : X ⟶ skelS i) (r : skelS i ⟶ X), e ≫ r = 𝟙 X :=
  Classical.choose_spec (Classical.choose_spec exists_atomSkeleton) X

/-! ## The cover and the resolution -/

/-- The zero-preserving atom cover. -/
abbrev cov : LightCondAb ⥤ LightCondAb := redCoverFunctor skelS

/-- The natural epimorphism from the atom cover. -/
abbrev covMap : cov ⟶ 𝟭 LightCondAb := redCoverNat skelS

instance cov_preservesZeroMorphisms : cov.PreservesZeroMorphisms :=
  redCoverFunctor_preservesZeroMorphisms skelS

theorem isAtomicSum_cov (M : LightCondAb) : IsAtomicSum (cov.obj M) :=
  isAtomicSum_redCover skelS M

theorem epi_covMap (M : LightCondAb) : Epi (covMap.app M) :=
  epi_redCoverMap skelS skelS_retract M

theorem isZero_cov_zero : IsZero (cov.obj 0) :=
  isZero_redCover_zero skelS

/-- The left resolution structure on light condensed abelian groups given by the atom cover. -/
noncomputable def LR : CategoryTheory.Abelian.LeftResolution (𝟭 LightCondAb) where
  F := cov
  π := (Functor.rightUnitor cov).hom ≫ covMap
  epi_π_app M := by
    rw [NatTrans.comp_app]
    haveI := epi_covMap M
    infer_instance

/-- The functorial resolution of a light condensed abelian group by a chain complex of atoms. -/
abbrev X : LightCondAb ⥤ ChainComplex LightCondAb ℕ := LR.chainComplexFunctor

/-! ## Properties of the resolution -/

/-- The first term of the resolution of `M` is the atom cover of `M`. -/
abbrev XZeroIso (M : LightCondAb) : (X.obj M).X 0 ≅ cov.obj M := LR.chainComplexXZeroIso M

end Work.RESOL
