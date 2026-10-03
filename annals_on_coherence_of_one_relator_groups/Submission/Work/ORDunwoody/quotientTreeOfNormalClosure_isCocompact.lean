import Mathlib
import Submission.Work.ORDunwoody.QuotientTreeDefs
import Submission.Work.ORDunwoody.Lemmas.isCocompact_iff_transversal
import Submission.Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff
import Submission.Work.ORBassSerre.QuotientTree.finite_orbitQuotient_quotient

namespace Work.ORDunwoody

universe u

open Work.ORBassSerre

theorem quotientTreeOfNormalClosure_isCocompact {H : Type u} [Group H] {W : Type u} [MulAction H W]
    (S' : Work.ORDunwoody.GTree H W) (K : Subgroup H) [K.Normal] (E : Set H)
    (hEll : ∀ g ∈ E, ∃ v : W, g • v = v) (hgen : Subgroup.normalClosure E = K)
    (hc : S'.IsCocompact) :
    (Work.ORDunwoody.quotientTreeOfNormalClosure S' K E hEll hgen).IsCocompact := by
  classical
  letI : Quiver W := Work.ORDunwoody.Lemmas.graphQuiver S'.graph
  letI : Quiver.HasInvolutiveReverse W :=
    Work.ORDunwoody.Lemmas.graphQuiverHasInvolutiveReverse S'.graph
  letI : Work.ORBassSerre.GraphAction H W := Work.ORDunwoody.Lemmas.graphQuiverAction S'
  let T : Work.ORDunwoody.GTree (H ⧸ K) (Work.ORBassSerre.orbitV ↥K W) :=
    Work.ORDunwoody.quotientTreeOfNormalClosure S' K E hEll hgen
  change T.IsCocompact
  refine ⟨Work.ORBassSerre.QuotientTree.finite_orbitQuotient_quotient K hc.1, ?_⟩
  haveI : Finite (MulAction.orbitRel.Quotient H S'.AdjPair) := hc.2
  obtain ⟨s, hs⟩ := Work.ORDunwoody.Lemmas.exists_finset_of_finite_orbitQuotient
    (G := H) (V := S'.AdjPair)
  -- the map on oriented edges induced by the quotient map
  let φ : S'.AdjPair → T.AdjPair := fun p =>
    ⟨(Quotient.mk'' p.1.1, Quotient.mk'' p.1.2),
      ⟨Work.ORBassSerre.orbitArrow (Classical.choice
        ((Work.ORDunwoody.Lemmas.nonempty_hom_iff_adj S'.graph p.1.1 p.1.2).mpr p.2))⟩⟩
  refine Work.ORDunwoody.Lemmas.finite_orbitQuotient_of_exists_finset (G := H ⧸ K)
    (s.image φ) ?_
  intro p
  obtain ⟨⟨A, B⟩, hAB⟩ := p
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Work.ORBassSerre.QuotientTree.orbitQuiver_nonempty_hom_iff K A B).mp hAB
  obtain ⟨h, hh⟩ := hs ⟨(a, b),
    (Work.ORDunwoody.Lemmas.nonempty_hom_iff_adj S'.graph a b).mp hab⟩
  refine ⟨QuotientGroup.mk' K h, Finset.mem_image.mpr ⟨h • ⟨(a, b), _⟩, hh, ?_⟩⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (Quotient.mk'' (h • a) : Work.ORBassSerre.orbitV ↥K W) = QuotientGroup.mk' K h • A
    rw [← ha, Work.ORBassSerre.quotient_smul_mk]
  · show (Quotient.mk'' (h • b) : Work.ORBassSerre.orbitV ↥K W) = QuotientGroup.mk' K h • B
    rw [← hb, Work.ORBassSerre.quotient_smul_mk]

end Work.ORDunwoody
