import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs
import Submission.Work.ANALYTIC.CechPt.Nerve
import Submission.Work.ANALYTIC.CechPt.cechProj_beta_eq

/-!
# The level model of the Čech complex: the face maps and the comparison map

`cechTerm p` (`CechTermDefs`) is the `p`-th term of the Čech nerve of the binary expansion
`beta : C = {0,1}^ℕ ⟶ [0,1]`, presented as the light profinite set of `(p+1)`-tuples of points
of the Cantor set with a common binary expansion.  This module provides the two ingredients that
identify the Čech complex `cechComplex beta` with the simplicial object `p ↦ ℤ[cechTerm p]`:

* `cechFace p i : cechTerm (p+1) ⟶ cechTerm p`, the `i`-th face map (delete the `i`-th
  coordinate), together with the projection formula `cechFace_cechProj`;
* `cechCompare p : ℤ[cechTerm p] ⟶ C^•_[0,1](p)`, the comparison map to the `p`-th term of the
  Čech nerve of `beta` induced by the coordinate projections, together with the projection
  formula `cechCompare_π` and the base formula `cechCompare_base`.
-/

open CategoryTheory Limits LightProfinite LightCondensed
open scoped Simplicial

noncomputable section

namespace Work.ANALYTIC.CechPt

set_option linter.style.haveILetI false

/-- The `i`-th face map of `cechTerm`: delete the `i`-th coordinate. -/
noncomputable def cechFace (p : ℕ) (i : Fin (p + 2)) : cechTerm (p + 1) ⟶ cechTerm p :=
  haveI : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : CompactSpace ↥(cechCover (p + 1)) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover (p + 1)).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover (p + 1)) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover (p + 1)) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  CompHausLike.ofHom _ ⟨fun x => (⟨fun j => x.1 (Fin.succAbove i j),
      mem_cechCover.mpr (fun j k => mem_cechCover.mp x.2 (Fin.succAbove i j)
        (Fin.succAbove i k))⟩ : ↥(cechCover p)), by
      apply Continuous.subtype_mk
      exact continuous_pi fun j =>
        (continuous_apply (Fin.succAbove i j)).comp continuous_subtype_val⟩

lemma cechFace_apply (p : ℕ) (i : Fin (p + 2)) (x : ↥(cechTerm (p + 1))) (j : Fin (p + 1)) :
    ((cechFace p i) x).1 j = x.1 (Fin.succAbove i j) := by
  haveI : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : CompactSpace ↥(cechCover (p + 1)) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover (p + 1)).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover (p + 1)) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover (p + 1)) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  show ((ConcreteCategory.hom (CompHausLike.ofHom _
    (⟨fun x => (⟨fun j => x.1 (Fin.succAbove i j),
      mem_cechCover.mpr (fun j k => mem_cechCover.mp x.2 (Fin.succAbove i j)
        (Fin.succAbove i k))⟩ : ↥(cechCover p)),
      by apply Continuous.subtype_mk
         exact continuous_pi fun j =>
           (continuous_apply (Fin.succAbove i j)).comp continuous_subtype_val⟩))) x).1 j
    = x.1 (Fin.succAbove i j)
  rw [CompHausLike.hom_ofHom]
  rfl

/-- The face maps of `cechTerm` drop the corresponding coordinates: the `j`-th projection of
`cechFace p i` is the `(Fin.succAbove i j)`-th projection. -/
lemma cechFace_cechProj (p : ℕ) (i : Fin (p + 2)) (j : Fin (p + 1)) :
    cechFace p i ≫ cechProj p j = cechProj (p + 1) (Fin.succAbove i j) := by
  apply ConcreteCategory.ext
  apply ContinuousMap.ext
  intro x
  rw [ConcreteCategory.comp_apply]
  change (cechProj p j) (cechFace p i x) = (cechProj (p + 1) (Fin.succAbove i j)) x
  rw [cechProj_apply, cechProj_apply]
  exact cechFace_apply p i x j

/-- The comparison map from the `p`-th term of the nerve, presented as `cechTerm p`, to the
`p`-th term of the Čech nerve of `beta`, induced by the coordinate projections. -/
noncomputable def cechCompare (p : ℕ) :
    LightProfinite.toCondensed (cechTerm p) ⟶
      (cechNerve beta).obj (Opposite.op ⦋p⦌) :=
  WidePullback.lift (lightProfiniteToLightCondSet.map (cechProj p 0) ≫ beta)
    (fun j => lightProfiniteToLightCondSet.map (cechProj p j))
    (fun j => cechProj_beta_eq p j)

/-- The `j`-th projection of the comparison map. -/
lemma cechCompare_π (p : ℕ) (j : Fin (p + 1)) :
    cechCompare p ≫ WidePullback.π (fun _ : Fin (p + 1) => beta) j =
      lightProfiniteToLightCondSet.map (cechProj p j) :=
  WidePullback.lift_π _ _ _ _ j

/-- The base of the comparison map. -/
lemma cechCompare_base (p : ℕ) :
    cechCompare p ≫ WidePullback.base (fun _ : Fin (p + 1) => beta) =
      lightProfiniteToLightCondSet.map (cechProj p 0) ≫ beta :=
  WidePullback.lift_base _ _ _ (fun j => cechProj_beta_eq p j)

end Work.ANALYTIC.CechPt
