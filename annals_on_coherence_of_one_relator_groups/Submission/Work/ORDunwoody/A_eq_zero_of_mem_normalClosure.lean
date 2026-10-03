/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The word-level integral vanishes on the kernel of the presentation

`Dunwoody/AlphaWord.lean` defines the word-level integral

    A τ a w = Σ_{s ∈ faceSteps D a w} stepHit τ s        (in `ZMod 2`)

of a word `w` over `Fin P.n × Bool` read at the base point `a`, and shows that it is additive over
concatenation (`A_append`), that it vanishes on a defining relator read at any base point
(`A_toWord`, which is `alpha_faceWalk`), and that it vanishes on the cancelling pair
`x · swapLetter x` (`A_pair`).

Those three facts say exactly that `A τ ·` is invariant under the two moves generating `WordRel`,
the word-level homotopy relation of the Cayley complex
(`Submission.Work.ORDunwoody.Cayley.Words`): deleting a cancelling pair (a backtrack), and
inserting the boundary word of a defining relator.  Since `WordRel P u v` is by definition the
equivalence closure of those moves, `A τ a u = A τ a v` for every `WordRel P`-related pair of
words and every base point `a` (`A_eq_of_wordRel`).

Simple connectedness of the Cayley complex, in the word-level form
`wordRel_of_mem_normalClosure`, says that a word whose class in `FreeGroup (Fin P.n)` lies in the
normal closure of the relators is `WordRel`-equivalent to the empty word.  Combining the two gives
the statement of this file: the word-level integral vanishes on the kernel of the presentation.
This is what makes the crossing equation `σ (a * genE x) = σ a + A τ a [x]` solvable on the Cayley
graph of `G` with respect to the positive generators, and hence the side function of a track well
defined.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaWord
import Submission.Work.ORDunwoody.A_pair
import Submission.Work.ORDunwoody.Cayley.wordRel_of_mem_normalClosure

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

section Aux

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-- **Reading a cancelling pair returns to the starting point**: the letter `swapLetter x` is the
inverse of `x`, so the word `x · swapLetter x` moves the base point by `genE x · (genE x)⁻¹`. -/
theorem endPt_swapLetter (a : G) (x : Fin P.n × Bool) :
    endPt P a [x, swapLetter x] = a := by
  simp only [endPt_cons, endPt_nil, CayV.genE_swap]
  group

/-- **`A` is unchanged when a cancelling pair is deleted.**  The pair itself contributes `0`
(`A_pair`), and its deletion does not move the base point of the rest of the word
(`endPt_swapLetter`). -/
theorem A_pair_append (τ : Track D) (a : G) (x : Fin P.n × Bool) (v : List (Fin P.n × Bool)) :
    A τ a ([x, swapLetter x] ++ v) = A τ a v := by
  rw [A_append, A_pair, endPt_swapLetter, zero_add]

/-- **`A` is unchanged when a defining relator is inserted.**  A relator read at any base point
contributes `0` (`A_toWord`) and returns to the base point it was read at (`endPt_toWord_eq`), so
the insertion is invisible to `A`. -/
theorem A_toWord_append (τ : Track D) {r : FreeGroup (Fin P.n)} (hr : r ∈ P.rel) (a : G)
    (v : List (Fin P.n × Bool)) :
    A τ a (FreeGroup.toWord r ++ v) = A τ a v := by
  rw [A_append, A_toWord τ hr, endPt_toWord_eq P hr, zero_add]

/-- **`A` is unchanged by the deletion of a cancelling pair anywhere in a word** (the `red` move of
`WordRel`, in the exact shape in which that move is stated). -/
theorem A_red_step (τ : Track D) (a : G) (u v : List (Fin P.n × Bool)) (x : Fin P.n × Bool) :
    A τ a (u ++ [x, swapLetter x] ++ v) = A τ a (u ++ v) := by
  rw [List.append_assoc, A_append τ a u ([x, swapLetter x] ++ v), A_append τ a u v,
    A_pair_append τ (endPt P a u) x v]

/-- **`A` is unchanged by the insertion of a defining relator anywhere in a word** (the `face` move
of `WordRel`, in the exact shape in which that move is stated). -/
theorem A_face_step (τ : Track D) {r : FreeGroup (Fin P.n)} (hr : r ∈ P.rel) (a : G)
    (u v : List (Fin P.n × Bool)) :
    A τ a (u ++ FreeGroup.toWord r ++ v) = A τ a (u ++ v) := by
  rw [List.append_assoc, A_append τ a u (FreeGroup.toWord r ++ v), A_append τ a u v,
    A_toWord_append τ hr (endPt P a u) v]

/-- **The word-level integral is invariant under the word-level homotopy relation.**  Both moves
generating `WordRel` — the deletion of a cancelling pair (`A_red_step`) and the insertion of a
relator (`A_face_step`) — are invisible to `A τ ·` at every base point, and `WordRel` is the
equivalence closure of those moves. -/
theorem A_eq_of_wordRel (τ : Track D) {u v : List (Fin P.n × Bool)} (h : WordRel P u v) (a : G) :
    A τ a u = A τ a v := by
  have hle : WordStep P ≤ fun u v : List (Fin P.n × Bool) => ∀ b : G, A τ b u = A τ b v := by
    intro u v huv
    cases huv with
    | red u' v' x => exact fun b => A_red_step τ b u' v' x
    | face u' v' r hr => exact fun b => (A_face_step τ hr b u' v').symm
  haveI : IsEquiv (List (Fin P.n × Bool)) (fun u v => ∀ b : G, A τ b u = A τ b v) :=
    { refl := fun u b => rfl
      symm := fun u v huv b => (huv b).symm
      trans := fun u v w huv hvw b => (huv b).trans (hvw b) }
  exact Relation.EqvGen.eqvGen_le hle u v h a

end Aux

/-- **The word-level integral vanishes on the kernel of the presentation.**  A word representing an
element of the normal closure of the relators is `WordRel`-equivalent to the empty word
(`wordRel_of_mem_normalClosure`), `A` is `WordRel`-invariant (`A_eq_of_wordRel`), and
`A τ a [] = 0`. -/
theorem A_eq_zero_of_mem_normalClosure {G : Type u} [Group G] {V : Type u} [MulAction G V]
    [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V}
    {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (τ : Work.ORDunwoody.Dunwoody.Track D) (a : G) {w : List (Fin P.n × Bool)}
    (h : FreeGroup.mk w ∈ Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin P.n)))) :
    Work.ORDunwoody.Dunwoody.A τ a w = 0 := by
  have hw : Cayley.WordRel P w [] := Cayley.wordRel_of_mem_normalClosure P h
  simpa using A_eq_of_wordRel τ hw a

end Work.ORDunwoody
