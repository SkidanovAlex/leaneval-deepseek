import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.rootAmaDefs

namespace Work.ORLocInd.CohenLyndon

/-- The two maps `rootIsoAmaFwd` and `rootIsoAmaBwd` are mutually inverse, one of the two
compositions: the backward map is a left inverse of the forward map.

Both maps send the generators of `F(RootIdx α t)` to the vertices of the amalgam, and the vertex
maps of `Ama t p` retract them: `Ama.ofZ` followed by `rootIsoAmaBwd` is the subtype inclusion of
`rootZ` (so lands back on `z`), and likewise for `Ama.ofK` and `rootK`.  Since the generators
`Sum.inr () = z` and `Sum.inl a` (which lies in `rootK` via `FreeGroup.of a`) are a generating set
of the free group, `FreeGroup.ext_hom` reduces the claim to these two computations. -/
theorem rootAmaBwdComp {α : Type*} [DecidableEq α] (t : α) (p : ℤ) :
    (rootIsoAmaBwd t p).comp (rootIsoAmaFwd t p) =
      MonoidHom.id (FreeGroup (RootIdx α t)) := by
  apply FreeGroup.ext_hom
  intro s
  match s with
  | Sum.inl a => simp
  | Sum.inr u =>
    cases u
    show (rootIsoAmaBwd t p) ((rootIsoAmaFwd t p) (rootLetter t)) = rootLetter t
    rw [rootIsoAmaFwd_ofInr, rootIsoAmaBwd_ofZ]

end Work.ORLocInd.CohenLyndon
