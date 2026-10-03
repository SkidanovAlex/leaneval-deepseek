/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The expansion map represents the class map of the coedge basis

`coedgeExpand W c u w` (`Submission/Work/OROneRel/coverCoedgeDefs.lean`) replaces every letter
`(e,b)` of the word of `w : FreeGroup (coverBetaEdge W c u)` by the loop word `edgeWord W c e` of the
edge `e` (reversed for `b = false`).  Reading the loop word of the edge `e = (x,i)`,

  `wordOf (W i) ++ [(x,true)] ++ wordOf ((W (i + c x))⁻¹)`,

it telescopes to `W i * x * (W (i + c x))⁻¹ = coverClassAt W c e`, the loop class of `e`; hence
`coedgeExpand` is a word-level realisation of the class map `coedgeToClasses W c u`, and the two
agree in `F α`:

  `FreeGroup.mk (coedgeExpand W c u w) = coedgeToClasses W c u w`.

This is `mk_expand`.  The proof is the telescoping identity `mk_edgeWord` for one edge, the
compatibility of the signed word with the sign `mk_edgeWordSigned`, and the generic
`flatten`/`prod` calculus `mk_flatten_expand` together with `FreeGroup.lift_mk`.
-/
import Mathlib
import Submission.Work.OROneRel.coverCoedgeDev

namespace Work.OROneRel

universe u

/-- **Telescoping of the loop word of an edge.**  The word of the loop of the edge `e = (x,i)` based
at level `0` represents the loop class `W i * x * (W (i + c x))⁻¹ = coverClassAt W c e` of the edge
in `F α`. -/
theorem mk_edgeWord {α : Type u} (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    FreeGroup.mk (edgeWord W c e) = coverClassAt W c e := by
  have h1 : wordOf ((W (e.2 + c e.1))⁻¹)
      = FreeGroup.invRev (wordOf (W (e.2 + c e.1))) := wordOf_inv _
  simp only [edgeWord, coverClassAt, gaugeMap_of, mk_append, mk_wordOf, mk_singleton_true, h1,
    mk_invRev]

/-- The signed loop word of an edge represents the loop class with the sign of the traversal. -/
theorem mk_edgeWordSigned {α : Type u} (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    FreeGroup.mk (edgeWordSigned W c e b) =
      bif b then coverClassAt W c e else (coverClassAt W c e)⁻¹ := by
  cases b
  · simp only [edgeWordSigned, cond_false, mk_invRev, mk_edgeWord]
  · simp only [edgeWordSigned, cond_true, mk_edgeWord]

/-- **The `flatten`/`prod` calculus of the expansion.**  If the word attached to a signed letter
`(e,b)` represents `g e` (with the sign `b`), then the concatenation of these words over a word `L`
in the letters represents the image of `FreeGroup.mk L` under the homomorphism `FreeGroup.lift g`. -/
theorem mk_flatten_expand {α : Type u} {β : Type u} (f : β × Bool → List (α × Bool))
    (g : β → FreeGroup α)
    (h : ∀ p : β × Bool, FreeGroup.mk (f p) = bif p.2 then g p.1 else (g p.1)⁻¹)
    (L : List (β × Bool)) :
    FreeGroup.mk (L.map f).flatten = FreeGroup.lift g (FreeGroup.mk L) := by
  rw [mk_flatten_map, FreeGroup.lift_mk]
  exact congrArg List.prod
    (List.map_congr_left (l := L) (f := fun p => FreeGroup.mk (f p))
      (g := fun p => bif p.2 then g p.1 else (g p.1)⁻¹) (fun a _ => h a))

theorem mk_expand {α : Type u} (c : α → ℤ) (u : FreeGroup α) (W : ℤ → FreeGroup α)
    (w : FreeGroup (coverBetaEdge W c u)) :
    FreeGroup.mk (coedgeExpand W c u w) = coedgeToClasses W c u w := by
  have hpt : ∀ p : coverBetaEdge W c u × Bool,
      FreeGroup.mk (edgeWordSigned W c p.1.1 p.2) =
        bif p.2 then coverClassAt W c p.1.1 else (coverClassAt W c p.1.1)⁻¹ :=
    fun p => mk_edgeWordSigned W c p.1.1 p.2
  have key : FreeGroup.mk (((FreeGroup.toWord w).map
        (fun p : coverBetaEdge W c u × Bool => edgeWordSigned W c p.1.1 p.2)).flatten)
      = FreeGroup.lift (fun e : coverBetaEdge W c u => coverClassAt W c e.1)
          (FreeGroup.mk (FreeGroup.toWord w)) :=
    mk_flatten_expand (fun p : coverBetaEdge W c u × Bool => edgeWordSigned W c p.1.1 p.2)
      (fun e : coverBetaEdge W c u => coverClassAt W c e.1) hpt (FreeGroup.toWord w)
  calc FreeGroup.mk (coedgeExpand W c u w)
      = FreeGroup.mk (((FreeGroup.toWord w).map
          (fun p : coverBetaEdge W c u × Bool => edgeWordSigned W c p.1.1 p.2)).flatten) := rfl
    _ = FreeGroup.lift (fun e : coverBetaEdge W c u => coverClassAt W c e.1)
          (FreeGroup.mk (FreeGroup.toWord w)) := key
    _ = FreeGroup.lift (fun e : coverBetaEdge W c u => coverClassAt W c e.1) w := by
          rw [FreeGroup.mk_toWord]
    _ = coedgeToClasses W c u w := rfl

end Work.OROneRel
