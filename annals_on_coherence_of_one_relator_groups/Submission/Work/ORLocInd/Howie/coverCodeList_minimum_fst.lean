/-
# The first coordinate of the minimum of a code list

`coverCodeList P L τ p n` is the list of codes (`CoverCode P = Lex (P.α × ℤ)`) of the arrows of
the lift of the path `p`.  Its order is lexicographic: the first coordinate is the unoriented edge
of the projected arrow, and the second coordinate only breaks ties.

Consequently the first coordinate of the *minimum* of the list is the minimum of the first
coordinates, which by `coverCodeList_map_fst` is `pathMin P.edgeOf p`.  That is the statement
proved here (the companion fact for `maximum`/`pathMax` is `coverCodeList_maximum_fst`).

The combinatorial input is the elementary fact that the first coordinate of the lexicographic
minimum of a list of pairs is the minimum of the first coordinates, proved here as
`lex_min_eq_coe_fst` from Mathlib's characterisation `List.minimum_eq_coe_iff`
("the minimum is the unique element of the list which is below every element").
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverCode

set_option autoImplicit false

namespace Work.ORLocInd.Howie

/-- The first coordinate of the lexicographic minimum of a list of pairs is the minimum of the
first coordinates: if `c` is the lexicographic minimum of `l : List (Lex (α × β))`, then
`c.1` is the minimum of `l.map Prod.fst`. -/
private theorem lex_min_eq_coe_fst {α β : Type*} [LinearOrder α] [LinearOrder β]
    {l : List (Lex (α × β))} {c : α × β}
    (h : l.minimum = ↑(toLex c)) :
    (l.map (fun x => (ofLex x).1)).minimum = ((c.1 : α) : WithTop α) := by
  obtain ⟨hc, hmin⟩ := List.minimum_eq_coe_iff.mp h
  refine List.minimum_eq_coe_iff.mpr ⟨List.mem_map.mpr ⟨toLex c, hc, rfl⟩, ?_⟩
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  have hcx : toLex c ≤ x := hmin x hx
  rcases (Prod.Lex.toLex_le_toLex.mp hcx) with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq

/-- The first coordinate of the minimum of the code list of a lifted path is `pathMin` of the
path. -/
theorem coverCodeList_minimum_fst {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (τ : Quiver.Total V → ℤ) {a : V} (p : Quiver.Path a a) (n : ℤ)
    {c : Work.ORLocInd.Howie.CoverCode P}
    (h : (Work.ORLocInd.Howie.coverCodeList P L τ p n).minimum = ↑c) :
    ((ofLex c).1 : WithTop P.α) = Work.ORLocInd.Howie.pathMin P.edgeOf p := by
  have hgen := lex_min_eq_coe_fst (l := coverCodeList P L τ p n) (c := ofLex c) h
  rw [← hgen, pathMin_eq_minimum, ← coverCodeList_map_fst P L τ p n]
  rfl

end Work.ORLocInd.Howie
