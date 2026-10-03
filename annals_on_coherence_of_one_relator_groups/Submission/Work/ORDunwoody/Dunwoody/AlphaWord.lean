/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The word-level integral `A τ a w`

`DESIGN_N13.md` §10 records the proof of

    (W1)  alpha τ (closed walk in `graph`) = 0,

which is what makes the counting side function of a track well defined.  Its engine is the
*word-level integral*: for a word `w` over `Fin P.n × Bool` read at the base point `a`,

    A τ a w := the sum of the contributions `stepHit τ` of the directed steps of `w`,

which by `Work.ORDunwoody.alpha_faceWalk_aux` is `alpha τ` of the boundary walk of `w`:

    A τ a w = alpha τ (faceWalk D a w).

`A` is additive over concatenation of words (`A_append`, from `faceSteps_append`) and is invariant
under the two moves generating `WordRel` (`A_pair` for the deletion of an adjacent pair
`x · swapLetter x`, and `A_face` = `Work.ORDunwoody.alpha_faceWalk` for the insertion of a
relator), hence vanishes on every word whose class in `FreeGroup (Fin P.n)` lies in
`ker π = normalClosure P.rel`.  That vanishing is what lets one *solve* the crossing equation
`σ (a * genE x) = σ a + A τ a [x]` on the Cayley graph of `G` w.r.t. the positive generators, and
the solution is the side function of the track.
-/
import Mathlib
import Submission.Work.ORDunwoody.alpha_faceWalk

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## Reading a concatenation of words -/

/-- Reading `u ++ v` at `a` is reading `u` at `a` and then `v` at the point reached. -/
theorem endPt_append (u v : List (Fin P.n × Bool)) (a : G) :
    endPt P a (u ++ v) = endPt P (endPt P a u) v := by
  induction u generalizing a with
  | nil => rw [List.nil_append, endPt_nil]
  | cons x u ih => rw [List.cons_append, endPt_cons, ih, endPt_cons]

/-- The steps of `u ++ v` are the steps of `u` followed by the steps of `v` read at the point
reached. -/
theorem faceSteps_append (D : GeoData T t₀ P) (a : G) (u v : List (Fin P.n × Bool)) :
    faceSteps D a (u ++ v) = faceSteps D a u ++ faceSteps D (endPt P a u) v := by
  induction u generalizing a with
  | nil => simp
  | cons x u ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | true =>
          simp only [List.cons_append, faceSteps_true, List.append_assoc, endPt_cons]
          rw [ih (a * CayV.genE P (j, true))]
      | false =>
          simp only [List.cons_append, faceSteps_false, List.append_assoc, endPt_cons]
          rw [ih (a * (CayV.genE P (j, true))⁻¹)]
          simp only [CayV.genE_true, CayV.genE_false]

/-! ## The word-level integral -/

/-- **The word-level integral of `phi τ`**: the sum of the contributions of the directed steps of
the word `w` read at the base point `a`. -/
noncomputable def A (τ : Track D) (a : G) (w : List (Fin P.n × Bool)) : ZMod 2 :=
  ((faceSteps D a w).map (stepHit τ)).sum

@[simp] theorem A_nil (τ : Track D) (a : G) : A τ a [] = 0 := rfl

/-- **`A` is the integral of `phi τ` over the boundary walk.** -/
theorem A_eq_alpha (τ : Track D) (a : G) (w : List (Fin P.n × Bool)) :
    A τ a w = alpha τ (faceWalk D a w) :=
  (alpha_faceWalk_aux τ a w).symm

/-- **`A` is additive over concatenation of words.** -/
theorem A_append (τ : Track D) (a : G) (u v : List (Fin P.n × Bool)) :
    A τ a (u ++ v) = A τ a u + A τ (endPt P a u) v := by
  unfold A
  rw [faceSteps_append, List.map_append, List.sum_append]

/-- **A relator read at any base point contributes nothing** (`Work.ORDunwoody.alpha_faceWalk`). -/
theorem A_toWord (τ : Track D) {r : FreeGroup (Fin P.n)} (hr : r ∈ P.rel) (a : G) :
    A τ a (FreeGroup.toWord r) = 0 := by
  rw [A_eq_alpha]
  exact alpha_faceWalk ⟨r, hr⟩ a τ

end Work.ORDunwoody.Dunwoody
