/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The word-level homotopy relation of the Cayley complex

A path in the Cayley quiver of a finite presentation `P` starting at a vertex is determined by
its word in `Fin P.n × Bool` (the arrows are *labelled* by the generators-with-sign, and the
arrow with a given label out of a given vertex is unique).  Consequently the homotopy relation
of the Cayley 2-complex can be expressed directly on words:

* `WordStep P w v` — one elementary move: delete (or insert) an adjacent inverse pair
  (`red`), or insert (or delete) the boundary word of a defining relator (`face`), anywhere in
  the word;
* `WordRel P` — its equivalence closure.

The mathematical content is that a word whose image in the free group lies in the kernel
`ker π = normalClosure rel` is `WordRel` to the empty word: the Cayley 2-complex is simply
connected.  This is proved in `Submission.Work.ORDunwoody.Cayley.wordRel_of_mem_normalClosure`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Foundations.Presentation
import Submission.Work.ORDunwoody.Cayley.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Cayley

variable {G : Type u} [Group G]

/-- **An elementary move of the word-level homotopy relation of the Cayley complex.**

* `red u v x`: delete an adjacent inverse pair `x · x⁻¹` (a backtrack);
* `face u v r hr`: insert the boundary word of the defining relator `r` at any position.

Both moves are used in both directions, via `WordRel = EqvGen WordStep`. -/
inductive WordStep (P : FinPresentation G) :
    List (Fin P.n × Bool) → List (Fin P.n × Bool) → Prop
  | red (u v : List (Fin P.n × Bool)) (x : Fin P.n × Bool) :
      WordStep P (u ++ [x, swapLetter x] ++ v) (u ++ v)
  | face (u v : List (Fin P.n × Bool)) (r : FreeGroup (Fin P.n)) (hr : r ∈ P.rel) :
      WordStep P (u ++ v) (u ++ FreeGroup.toWord r ++ v)

/-- **The word-level homotopy relation of the Cayley complex**: the equivalence closure of the
elementary moves `WordStep`. -/
def WordRel (P : FinPresentation G) : List (Fin P.n × Bool) → List (Fin P.n × Bool) → Prop :=
  Relation.EqvGen (WordStep P)

namespace WordRel

variable {P : FinPresentation G}

theorem refl (w : List (Fin P.n × Bool)) : WordRel P w w := Relation.EqvGen.refl w

theorem symm {u v : List (Fin P.n × Bool)} (h : WordRel P u v) : WordRel P v u :=
  Relation.EqvGen.symm _ _ h

theorem trans {u v w : List (Fin P.n × Bool)} (h₁ : WordRel P u v) (h₂ : WordRel P v w) :
    WordRel P u w := Relation.EqvGen.trans _ _ _ h₁ h₂

theorem step {u v : List (Fin P.n × Bool)} (h : WordStep P u v) : WordRel P u v :=
  Relation.EqvGen.rel _ _ h

/-- **`WordStep` is stable under adding a common prefix and suffix.** -/
theorem step_append {u v : List (Fin P.n × Bool)} (h : WordStep P u v)
    (a b : List (Fin P.n × Bool)) : WordStep P (a ++ u ++ b) (a ++ v ++ b) := by
  cases h with
  | red u' v' x =>
      have h1 : a ++ (u' ++ [x, swapLetter x] ++ v') ++ b
          = (a ++ u') ++ [x, swapLetter x] ++ (v' ++ b) := by simp [List.append_assoc]
      have h2 : a ++ (u' ++ v') ++ b = (a ++ u') ++ (v' ++ b) := by simp [List.append_assoc]
      rw [h1, h2]
      exact WordStep.red _ _ x
  | face u' v' r hr =>
      have h1 : a ++ (u' ++ v') ++ b = (a ++ u') ++ (v' ++ b) := by simp [List.append_assoc]
      have h2 : a ++ (u' ++ FreeGroup.toWord r ++ v') ++ b
          = (a ++ u') ++ FreeGroup.toWord r ++ (v' ++ b) := by simp [List.append_assoc]
      rw [h1, h2]
      exact WordStep.face _ _ r hr

theorem step_prepend {u v : List (Fin P.n × Bool)} (h : WordStep P u v)
    (a : List (Fin P.n × Bool)) : WordStep P (a ++ u) (a ++ v) := by
  simpa using step_append h a []

theorem step_append_right {u v : List (Fin P.n × Bool)} (h : WordStep P u v)
    (b : List (Fin P.n × Bool)) : WordStep P (u ++ b) (v ++ b) := by
  simpa using step_append h [] b

theorem append_right {u u' : List (Fin P.n × Bool)} (h : WordRel P u u')
    (v : List (Fin P.n × Bool)) : WordRel P (u ++ v) (u' ++ v) := by
  have hle : WordStep P ≤ (fun a b : List (Fin P.n × Bool) => WordRel P (a ++ v) (b ++ v)) :=
    fun _ _ hab => step (step_append_right hab v)
  haveI : IsEquiv (List (Fin P.n × Bool))
      (fun a b : List (Fin P.n × Bool) => WordRel P (a ++ v) (b ++ v)) :=
    { refl := fun a => WordRel.refl _
      symm := fun _ _ hab => hab.symm
      trans := fun _ _ _ hab hbc => hab.trans hbc }
  exact Relation.EqvGen.eqvGen_le hle u u' h

theorem prepend_left {u u' : List (Fin P.n × Bool)} (h : WordRel P u u')
    (v : List (Fin P.n × Bool)) : WordRel P (v ++ u) (v ++ u') := by
  have hle : WordStep P ≤ (fun a b : List (Fin P.n × Bool) => WordRel P (v ++ a) (v ++ b)) :=
    fun _ _ hab => step (step_prepend hab v)
  haveI : IsEquiv (List (Fin P.n × Bool))
      (fun a b : List (Fin P.n × Bool) => WordRel P (v ++ a) (v ++ b)) :=
    { refl := fun a => WordRel.refl _
      symm := fun _ _ hab => hab.symm
      trans := fun _ _ _ hab hbc => hab.trans hbc }
  exact Relation.EqvGen.eqvGen_le hle u u' h

theorem append {u u' v v' : List (Fin P.n × Bool)} (h₁ : WordRel P u u')
    (h₂ : WordRel P v v') : WordRel P (u ++ v) (u' ++ v') :=
  (append_right h₁ v).trans (prepend_left h₂ u')

/-- The empty word is related to the boundary word of every defining relator. -/
theorem face_nil {r : FreeGroup (Fin P.n)} (hr : r ∈ P.rel) :
    WordRel P (FreeGroup.toWord r) [] := by
  have h := step (WordStep.face (P := P) ([] : List (Fin P.n × Bool))
    ([] : List (Fin P.n × Bool)) r hr)
  simpa using h.symm

end WordRel

end Work.ORDunwoody.Cayley
