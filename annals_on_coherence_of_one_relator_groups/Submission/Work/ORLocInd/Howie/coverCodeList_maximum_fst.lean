import Mathlib
import Submission.Work.ORLocInd.Howie.CoverCode

namespace Work.ORLocInd.Howie

/-! ## The first coordinate of a lexicographic maximum

The codes of the arrows of the lift are elements of `Lex (α × ℤ)` (`α = P.α`), and the level `ℤ`
is only a *tie-breaker*: the lexicographic order compares the codes of the projected edges first.
Consequently the first coordinate of the maximum of a nonempty list of codes is the maximum of the
first coordinates.  This is the content of `list_maximum_map_fst`, which is a purely
order-theoretic statement about `List.maximum` and `Lex (α × β)`.
-/

/-- The first coordinate of the maximum of a list of lexicographically ordered pairs, written as a
`WithBot`-valued element, is the maximum of the list of first coordinates.

(`List.maximum` of the empty list is `⊥`, so the hypothesis forces the list to be nonempty.) -/
theorem list_maximum_map_fst {α β : Type*} [LinearOrder α] [LinearOrder β]
    {l : List (Lex (α × β))} {c : Lex (α × β)} (h : l.maximum = ↑c) :
    ((ofLex c).1 : WithBot α) = (l.map (fun x => (ofLex x).1)).maximum := by
  obtain ⟨hmem, hmax⟩ := List.maximum_eq_coe_iff.mp h
  have key : ∀ a ∈ l.map (fun x => (ofLex x).1), a ≤ (ofLex c).1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    exact Prod.Lex.monotone_fst y c (hmax y hy)
  have hmem' : (ofLex c).1 ∈ l.map (fun x => (ofLex x).1) := List.mem_map_of_mem hmem
  exact ((List.maximum_eq_coe_iff (l := l.map fun x => (ofLex x).1)
    (m := (ofLex c).1)).mpr ⟨hmem', key⟩).symm

/-- The code of an arrow of the lift, read in the first coordinate, is the code `P.edgeOf` of its
projection.  Consequently the first coordinate of the *maximum* of the code list
`coverCodeList P L τ p n` is the maximum `pathMax P.edgeOf p` of the projected path, independently
of the levels. -/
theorem coverCodeList_maximum_fst {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (τ : Quiver.Total V → ℤ) {a : V} (p : Quiver.Path a a) (n : ℤ)
    {c : Work.ORLocInd.Howie.CoverCode P}
    (h : (Work.ORLocInd.Howie.coverCodeList P L τ p n).maximum = ↑c) :
    ((ofLex c).1 : WithBot P.α) = Work.ORLocInd.Howie.pathMax P.edgeOf p := by
  rw [pathMax_eq_maximum, ← coverCodeList_map_fst P L τ p n]
  exact list_maximum_map_fst h

end Work.ORLocInd.Howie
