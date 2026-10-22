import Submission.Work.REFL.Basic
import Submission.Work.REFL.pre_app_points
import Submission.Work.REFL.isSolid_iff_solidW
import Submission.Work.REFL.pointwise_colimit_isSheaf
import Submission.Work.REFL.sections_filtered
import Submission.Work.REFL.atoms_presentable
import Submission.Work.REFL.test_objects_presentable
import Submission.Work.REFL.solid_iff_testMap
import Submission.Work.REFL.presentability

/-!
# AREA REFL — solid objects are reflective (main results)

This module assembles the area.  The main result is: the inclusion of light solid abelian groups
into light condensed abelian groups has a left adjoint (holes 1–3 of the challenge,
`Submission.Blueprint.ReflProp`).

The proof is the following chain, all of whose ingredients live in this directory:

* `Work.REFL.isSolid_iff_solidW` : `isSolid` is the property of objects local for the small family
  `solidW` of test morphisms `(1−S) ⊗ id_{ℤ[S]}` (RC Prop. 3.2.5);
* `Work.REFL.test_objects_presentable`, `Work.REFL.atoms_presentable`,
  `Work.REFL.sections_filtered`, `Work.REFL.pointwise_colimit_isSheaf` : the domains and
  codomains of the test morphisms are finitely presentable;
* `MorphismProperty.isRightAdjoint_ι_isLocal` (Mathlib) : the orthogonal reflection construction
  applied to the small family `solidW` produces the left adjoint.

The single input which is not proved in this file is `PointwiseColimitIsSheaf` (filtered colimits
of light condensed abelian groups are computed pointwise); everything else is unconditional, and
`refl_prop_of` derives the full statement from it.  In particular, `refl_prop` itself is
unconditional.

## Interface for callers

Import `Submission.Work.REFL.Main` (or the alias `Submission.Work.Refl.Main`).  Then:

* `Work.REFL.refl_prop : Submission.Blueprint.ReflProp` — the top theorem (holes 1–3);
* `Work.REFL.instIsRightAdjoint : isSolid.ι.IsRightAdjoint` — the same, as a global instance, so
  that `isSolid.ι.leftAdjoint` (hole 1), `Adjunction.ofIsRightAdjoint isSolid.ι` (hole 3) and
  `isSolid.ι.leftAdjoint.Additive` (hole 2) elaborate by instance search;
* `Work.REFL.isSolid_iff_solidW` (RC Prop. 3.2.5, skeleton form) and
  `Work.REFL.bijective_testMap_of_isSolid`, `Work.REFL.precompTestMapEquiv` (all-`S` form,
  in `solid_iff_testMap.lean`);
* the intermediate `Prop`s `Work.REFL.PointwiseColimitIsSheaf`, `Work.REFL.SectionsFiltered`,
  `Work.REFL.AtomsPresentable`, `Work.REFL.TestObjectsPresentable`, together with the proofs
  `Work.REFL.pointwise_colimit_isSheaf`, `Work.REFL.sections_filtered`,
  `Work.REFL.atoms_presentable`, `Work.REFL.test_objects_presentable` and the assembly steps
  `Work.REFL.refl_prop_aux`, `Work.REFL.refl_prop_of`;
* `Submission/Work/REFL/presentability.lean` contains the unconditional consequences
  `Work.REFL.sections_preserves_filtered_colimits`, `Work.REFL.zfree_isCardinalPresentable` and
  `Work.REFL.tmul_P_zfree_isCardinalPresentable` (with `_apply` unfoldings);
* `Submission/Work/REFL/pointwise_colimit_isSheaf2.lean` and
  `pointwise_colimit_isSheaf3.lean` contain two further, independent proofs of
  `Work.REFL.PointwiseColimitIsSheaf` (as `pointwise_colimit_isSheaf2`/`3`); they are redundant
  with `pointwise_colimit_isSheaf` and are kept only as cross-checks.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

set_option linter.style.haveILetI false

/-- **The assembly step.** If the test objects `P ⊗ ℤ[S]` are finitely presentable and solidity
is the property of being local for the small family `solidW`, then the inclusion of solid objects
into light condensed abelian groups is a right adjoint.

The proof is Mathlib's orthogonal reflection construction
`MorphismProperty.isRightAdjoint_ι_isLocal`, which requires the index family `solidW` to be small,
its domains and codomains to be `ℵ₀`-presentable (`= compact`), `LightCondAb` to be locally small
and to have small colimits; the latter two are supplied by the Grothendieck abelian structure. -/
theorem refl_prop_aux (hT : TestObjectsPresentable) (hI : IsSolidIsLocalStatement) :
    Submission.Blueprint.ReflProp := by
  haveI : HasColimitsOfSize.{0, 0} LightCondAb := IsGrothendieckAbelian.hasColimits LightCondAb
  change isSolid.ι.IsRightAdjoint
  have hloc : solidW.isLocal = isSolid := funext fun M => propext (hI M).symm
  rw [← hloc]
  refine MorphismProperty.isRightAdjoint_ι_isLocal.{0} solidW (Cardinal.aleph0 : Cardinal.{0})
    (fun X Y f hf => ?_) (C := LightCondAb)
  obtain ⟨i, hi⟩ := (MorphismProperty.ofHoms_iff _ f).mp hf
  obtain ⟨h₁, h₂, -⟩ := (Arrow.mk_eq_mk_iff _ _).mp hi
  subst h₁
  subst h₂
  exact ⟨hT (testSpace i), hT (testSpace i)⟩

/-- **AREA REFL, holes 1–3, modulo "filtered colimits of sheaves are computed pointwise".**
Given `PointwiseColimitIsSheaf`, the whole chain gives that the inclusion of solid objects in
light condensed abelian groups is a right adjoint. -/
theorem refl_prop_of (hP : PointwiseColimitIsSheaf) : Submission.Blueprint.ReflProp :=
  refl_prop_aux
    (test_objects_presentable (atoms_presentable (sections_filtered hP)))
    (isSolid_iff_solidW pre_app_points)

/-- **AREA REFL, holes 1–3.** The inclusion of light solid abelian groups into light condensed
abelian groups has a left adjoint (solidification), obtained from the orthogonal reflection
construction applied to the small family `solidW` of test morphisms. -/
theorem refl_prop : Submission.Blueprint.ReflProp :=
  refl_prop_of pointwise_colimit_isSheaf

/-- The same statement, made available as an instance so that downstream files can write
`isSolid.ι.leftAdjoint`, `Adjunction.ofIsRightAdjoint isSolid.ι`, etc. without passing the
hypothesis explicitly. -/
instance instIsRightAdjoint : isSolid.ι.IsRightAdjoint := refl_prop

end Work.REFL
