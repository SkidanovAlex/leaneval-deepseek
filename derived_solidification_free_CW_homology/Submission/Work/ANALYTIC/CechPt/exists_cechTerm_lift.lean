import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs

open CategoryTheory Limits LightProfinite

namespace Work.ANALYTIC.CechPt

/-- **The universal property of the terms of the Čech nerve of the binary expansion.**

Let `S` be a light profinite set and, for each `i ∈ Fin (p+1)`, let `u i : S ⟶ C` be a map to the
Cantor set, such that all the `u i` have the same binary expansion pointwise.  Then the tuple
`(u i)_i` of maps factors through the closed subspace

`cechTerm p = {x : Fin (p+1) → C // ∀ i j, binExp (x i) = binExp (x j)} ⊆ C^{p+1}`

of the Čech nerve, i.e. there is a map `u' : S ⟶ cechTerm p` whose `j`-th coordinate projection is
`u j`. -/
theorem exists_cechTerm_lift (p : ℕ) (S : LightProfinite.{0})
    (u : Fin (p + 1) → (S ⟶ Work.ANALYTIC.CechPt.cantor))
    (hu : ∀ (s : ↥S) (i j : Fin (p + 1)),
      Work.ANALYTIC.CechPt.binExp (u i s) = Work.ANALYTIC.CechPt.binExp (u j s)) :
    ∃ (u' : S ⟶ Work.ANALYTIC.CechPt.cechTerm p),
      ∀ j, CategoryTheory.CategoryStruct.comp u' (Work.ANALYTIC.CechPt.cechProj p j) = u j := by
  -- the instances needed to view `cechCover p` as a light profinite set
  have : CompactSpace ↥(cechCover p) :=
    isCompact_iff_compactSpace.mp (isClosed_cechCover p).isCompact
  have : TotallyDisconnectedSpace ↥(cechCover p) := Subtype.totallyDisconnectedSpace
  have : SecondCountableTopology ↥(cechCover p) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  -- `s ↦ (u i s)_i`, which lands in the closed subspace `cechCover p` by `hu`
  refine ⟨CompHausLike.ofHom _ ⟨fun s => (⟨fun j => u j s,
    mem_cechCover.mpr (fun i j => hu s i j)⟩ : ↥(cechCover p)), ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    exact continuous_pi (fun j => (ConcreteCategory.hom (u j)).continuous)
  · intro j
    ext s
    rfl

end Work.ANALYTIC.CechPt
