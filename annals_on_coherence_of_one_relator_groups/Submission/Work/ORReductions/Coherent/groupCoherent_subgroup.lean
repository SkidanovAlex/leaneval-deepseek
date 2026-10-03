import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.Coherent

/-- **Coherence passes to subgroups.**  If `G` is coherent (all its finitely generated
subgroups are finitely presented), then so is any subgroup `H ≤ G`.

Given a finitely generated subgroup `K ≤ H`, regard `K` as a subgroup of `G` via the
inclusion `H.subtype`.  Its image `K.map H.subtype` is again finitely generated (the image
of a finite generating set under a homomorphism generates the image), so by coherence of `G`
it is finitely presented.  Finally `K ≃* K.map H.subtype` through the inclusion, and
finite presentability is an isomorphism invariant; hence `K` is finitely presented. -/
theorem groupCoherent_subgroup {G : Type*} [Group G] (H : Subgroup G) :
    Group.Coherent G → Group.Coherent H := by
  intro hG K hK
  classical
  -- The image of `K` in `G` is finitely generated.
  have hmap : (K.map H.subtype).FG := by
    obtain ⟨S, hS⟩ := Subgroup.isMulFG_iff.mp hK
    refine Subgroup.isMulFG_iff.mpr ⟨S.image H.subtype, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hS]
  -- Coherence of `G` makes that image finitely presented.
  have hfp : Group.IsFinitelyPresented (K.map H.subtype) := hG _ hmap
  -- Transport along `K ≃* K.map H.subtype`.
  exact Group.IsFinitelyPresented.equiv
    (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).symm
    (h := hfp)

end Work.ORReductions.Coherent
