/-
# The `pathSum` of a side-restricted labelling on a path avoiding the bridge

Let `P` be a graph presentation, `e` an arrow of `Γ` and `c` a vertex.  Write
`S = {y | y is joined to c by a path of Γ avoiding the code of e}` (the set of vertices reached
from `c` without crossing the unoriented edge `e`), and let `restrictSide P e S L` be the labelling
which agrees with `L` on the arrows with both endpoints in `S` and avoids the code of `e`, and
vanishes elsewhere.

If `p` is a path avoiding the code of `e` and `pathSum L.toFun p = 0`, then also
`pathSum (restrictSide P e S L).toFun p = 0`.

The point is that along a path avoiding the code of `e`, membership in `S` is *constant*: an arrow
whose code is not the code of `e` survives the deletion of the edge `e`, so it can be used in both
directions to extend an avoiding path by one arrow.  Hence either every vertex of `p` lies in `S` —
and the restricted labelling agrees with `L` on every arrow of `p`, so the sums are equal — or no
vertex of `p` lies in `S` — and every arrow of `p` gets the label `0`.

This is the key computation which lets one push a labelling vanishing on the relators of `P` through
the bridge construction of Howie's Case 2.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.Case2Labelling

open Quiver

namespace Work.ORLocInd.Howie.C2

theorem pathSum_restrictSide_reach_eq_zero_of_avoids {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V) (c : V)
    (L : Work.ORLocInd.Howie.Labelling V)
    {a b : V} (p : Quiver.Path a b) (hav : Work.ORLocInd.Howie.Avoids P e p)
    (h0 : Work.ORLocInd.Howie.pathSum L.toFun p = 0) :
    Work.ORLocInd.Howie.pathSum
      (Work.ORLocInd.Howie.restrictSide P e
        (fun y => ∃ q : Quiver.Path c y, Work.ORLocInd.Howie.Avoids P e q) L).toFun p = 0 := by
  classical
  -- `S` is the set of vertices joined to `c` by a path avoiding the code of `e`.
  set S : V → Prop := fun y => ∃ q : Quiver.Path c y, Avoids P e q
  -- Along a single arrow avoiding the code of `e`, membership in `S` is constant: the arrow and
  -- its reverse both survive the deletion of `e`, so they extend an avoiding path in either
  -- direction.
  have hS : ∀ g : Quiver.Total V, P.edgeOf g ≠ P.edgeOf e → (S g.left ↔ S g.right) := by
    intro g hg
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r.cons g.hom, (avoids_cons_iff P e r g.hom).mpr ⟨hr, hg⟩⟩
    · rintro ⟨r, hr⟩
      exact ⟨r.cons (Quiver.reverse g.hom),
        (avoids_cons_iff P e r (Quiver.reverse g.hom)).mpr
          ⟨hr, (edgeOf_reverse_mk_ne P e g.hom).mpr hg⟩⟩
  -- Hence membership in `S` is constant along a whole path avoiding the code of `e`.
  have key : ∀ {x y : V} (q : Quiver.Path x y), Avoids P e q → (S x ↔ S y) := by
    intro x y q
    induction q with
    | nil => intro _; exact Iff.rfl
    | cons q f ih =>
        intro h
        obtain ⟨hq, hf⟩ := (avoids_cons_iff P e q f).mp h
        exact (ih hq).trans (hS (Quiver.Total.mk _ _ f) hf)
  -- The main computation, by induction on the path.
  have main : ∀ {x y : V} (q : Quiver.Path x y), Avoids P e q →
      (S x → pathSum (restrictSide P e S L).toFun q = pathSum L.toFun q) ∧
      (¬ S x → pathSum (restrictSide P e S L).toFun q = 0) := by
    intro x y q
    induction q with
    | nil => intro _; exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons q f ih =>
        intro h
        obtain ⟨hq, hf⟩ := (avoids_cons_iff P e q f).mp h
        obtain ⟨ihpos, ihneg⟩ := ih hq
        constructor
        · -- the path is inside `S`: the restricted labelling agrees with `L` everywhere
          intro hx
          have hb : S _ := (key q hq).mp hx
          have hc : S _ := (hS (Quiver.Total.mk _ _ f) hf).mp hb
          rw [pathSum_cons, pathSum_cons, ihpos hx,
            restrictSide_apply_of _ _ _ _ _ ⟨hb, hc, hf⟩]
        · -- the path is outside `S`: every arrow gets the label `0`
          intro hx
          have hb : ¬ S _ := fun hh => hx ((key q hq).mpr hh)
          rw [pathSum_cons, ihneg hx,
            restrictSide_apply_not _ _ _ _ _ (fun hh => hb hh.1), add_zero]
  rcases main p hav with ⟨hpos, hneg⟩
  by_cases h : S a
  · rw [hpos h, h0]
  · exact hneg h

end Work.ORLocInd.Howie.C2
