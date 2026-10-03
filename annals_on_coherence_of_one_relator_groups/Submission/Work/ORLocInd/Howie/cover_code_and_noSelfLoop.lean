import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.span_noSelfLoop

universe u

namespace Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The underlying arrow of the base graph of an arrow of the cyclic cover. -/
def coverUnder {L : Labelling V} (f : Quiver.Total (CoverVertex L)) : Quiver.Total V := f.hom.1

/-- Taking underlying arrows commutes with the total reverse. -/
theorem coverUnder_totalReverse {L : Labelling V} (f : Quiver.Total (CoverVertex L)) :
    coverUnder (Quiver.totalReverse f) = Quiver.totalReverse (coverUnder f) := rfl

/-- The underlying arrow of the reverse of an arrow of the cover is the total reverse of the
underlying arrow. -/
theorem coverUnder_reverse {L : Labelling V} {p q : CoverVertex L} (f : p ⟶ q) :
    (Quiver.reverse f).1 = Quiver.totalReverse f.1 := rfl

/-- The level of an arrow of the cyclic cover, read off from the subtype data. -/
theorem cover_hom_level {L : Labelling V} {p q : CoverVertex L} (f : p ⟶ q) :
    q.level = p.level + L.toFun f.1 := f.2.2.2

theorem cover_code_and_noSelfLoop {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) :
    (∀ f : Quiver.Total (Work.ORLocInd.Howie.CoverVertex L),
        Work.ORLocInd.Howie.coverEdgeOf P L τ (Quiver.totalReverse f) =
          Work.ORLocInd.Howie.coverEdgeOf P L τ f) ∧
      (∀ (u : Work.ORLocInd.Howie.CoverVertex L) (f : u ⟶ u), Quiver.reverse f ≠ f) := by
  refine ⟨?_, ?_⟩
  · intro f
    have hA : coverEdgeOf P L τ (Quiver.totalReverse f)
        = toLex (P.edgeOf (Quiver.totalReverse (coverUnder f)),
            f.right.level + τ (Quiver.totalReverse (coverUnder f))) := rfl
    have hB : coverEdgeOf P L τ f
        = toLex (P.edgeOf (coverUnder f), f.left.level + τ (coverUnder f)) := rfl
    have hlev : f.right.level = f.left.level + L.toFun (coverUnder f) := f.hom.2.2.2
    rw [hA, hB]
    show toLex (P.edgeOf (Quiver.totalReverse (coverUnder f)),
        f.right.level + τ (Quiver.totalReverse (coverUnder f)))
      = toLex (P.edgeOf (coverUnder f), f.left.level + τ (coverUnder f))
    rw [toLex_inj, Prod.mk.injEq]
    refine ⟨P.edgeOf_reverse (coverUnder f), ?_⟩
    rw [hlev, hτ (coverUnder f)]
    ring
  · intro u f h
    refine totalReverse_ne_self P.noSelfLoop f.1 ?_
    have h' := congrArg (fun x : u ⟶ u => x.1) h
    rwa [coverUnder_reverse f] at h'

end Work.ORLocInd.Howie
