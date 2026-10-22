import Mathlib
import Submission.Work.ANALYTIC.CechPt.Setup
import Submission.Work.ANALYTIC.CechPt.Nerve
import Submission.Work.ANALYTIC.CechPt.binaryExp_epi

/-!
# The terms of the Čech nerve of the binary expansion as light profinite sets

For a map `β : X ⟶ Y` of light condensed sets, the `p`-th term of the Čech nerve of `β` is the
wide pullback of `p + 1` copies of `X` over `Y`.  For `β` the binary expansion
`C = {0,1}^ℕ ⟶ [0,1]` this wide pullback is the light condensed set of `(p+1)`-tuples of points
of the Cantor set with the same binary expansion, i.e. the light condensed set associated to the
closed subspace

`Z_p = {x : Fin (p+1) → C // ∀ i j, binExp (x i) = binExp (x j)}`

of `C^{p+1}`.  This module defines that closed subspace (`cechCover`), endows it with the
structure of a light profinite set (`cechTerm`) and defines the coordinate projections
(`cechProj`).
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

open _root_.LightCondensed

/-- The closed set of pairs of coordinates of `C^{p+1}` with the same binary expansion. -/
def cechRel (p : ℕ) (i j : Fin (p + 1)) : Set (Fin (p + 1) → ↥cantor) :=
  {x | binExp (x i) = binExp (x j)}

/-- The closed subspace of `C^{p+1}` of tuples of points of the Cantor set with the same binary
expansion.  Its light condensed set is the `p`-th term of the Čech nerve of `beta`. -/
def cechCover (p : ℕ) : Set (Fin (p + 1) → ↥cantor) :=
  ⋂ i, ⋂ j, cechRel p i j

lemma mem_cechCover {p : ℕ} {x : Fin (p + 1) → ↥cantor} :
    x ∈ cechCover p ↔ ∀ i j : Fin (p + 1), binExp (x i) = binExp (x j) := by
  simp [cechCover, cechRel]

lemma isClosed_cechCover (p : ℕ) : IsClosed (cechCover p) := by
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact binExp_continuous.comp (continuous_apply i)
  · exact binExp_continuous.comp (continuous_apply j)

/-- The `p`-th term of the Čech nerve of `beta`, as a light profinite set. -/
def cechTerm (p : ℕ) : LightProfinite.{0} :=
  haveI : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  ↧↥(cechCover p)

/-- The `j`-th coordinate projection of `cechTerm p`. -/
def cechProj (p : ℕ) (j : Fin (p + 1)) : cechTerm p ⟶ cantor :=
  haveI : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  CompHausLike.ofHom _ ⟨fun x => x.1 j, (continuous_apply j).comp continuous_subtype_val⟩

lemma cechProj_apply (p : ℕ) (j : Fin (p + 1)) (x : ↥(cechTerm p)) :
    cechProj p j x = x.1 j := by
  haveI : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  haveI : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  haveI : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  show (ConcreteCategory.hom (CompHausLike.ofHom _
    ⟨fun x => x.1 j, (continuous_apply j).comp continuous_subtype_val⟩)) x = x.1 j
  rw [CompHausLike.hom_ofHom]
  rfl

/-- The defining property of a point of `cechTerm p`. -/
lemma cechTerm_apply_eq (p : ℕ) (x : ↥(cechTerm p)) (i j : Fin (p + 1)) :
    binExp (x.1 i) = binExp (x.1 j) :=
  mem_cechCover.mp x.2 i j

end Work.ANALYTIC.CechPt
