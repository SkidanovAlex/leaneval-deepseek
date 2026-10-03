/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The word-level integral is invariant under reversing the word

`Dunwoody/AlphaWord.lean` defines the word-level integral

    A τ a w = Σ_{s ∈ faceSteps D a w} stepHit τ s        (in `ZMod 2`)

of a word `w` over `Fin P.n × Bool` read at the base point `a`.  Reading `w` at `a` and then
reading the *reversed, sign-swapped* word `w.reverse.map swapLetter` at the endpoint traverses
exactly the same boundary walk backwards, so the two integrals agree:

    A τ a w = A τ (endPt P a w) (w.reverse.map swapLetter).

This is what makes the word-level integral independent of the *direction* in which a closed word
is read, complementing its additivity (`A_append`), its vanishing on relators (`A_toWord`) and on
cancelling pairs (`A_pair`).

The proof has three steps.

* `faceSteps_revSwap`: reading the reversed word traverses the reversed steps, each one traversed
  the other way (`op`), so the step lists are related by `List.reverse` and `List.map op`;
* `stepHit_op` (`A_aux`): the contribution of a step is unchanged by reversal, because the cochain
  `phi τ` is symmetric (`phi_comm`);
* a `List.sum` computation.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaWord
import Submission.Work.ORDunwoody.A_aux
import Submission.Work.ORDunwoody.A_endPt_rev
import Submission.Work.ORDunwoody.A_negSteps_rev
import Submission.Work.ORDunwoody.A_posSteps_rev

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## Reading one letter -/

/-- Reading `x :: w` at `a` is reading the single letter `x` at `a` and then `w` at the point
reached. -/
theorem faceSteps_cons (D : GeoData T t₀ P) (a : G) (x : Fin P.n × Bool)
    (w : List (Fin P.n × Bool)) :
    faceSteps D a (x :: w) = faceSteps D a [x] ++ faceSteps D (a * CayV.genE P x) w := by
  obtain ⟨j, b⟩ := x
  cases b with
  | true => simp [faceSteps_true, faceSteps_false]
  | false =>
      rw [genE_false_eq P j]
      simp [faceSteps_true, faceSteps_false]

/-- **Reading one letter, and the same letter backwards from the point reached, traverse the same
directed step the other way.** -/
theorem faceSteps_single (D : GeoData T t₀ P) (a : G) (x : Fin P.n × Bool) :
    faceSteps D (a * CayV.genE P x) [Cayley.swapLetter x] =
      (faceSteps D a [x]).reverse.map op := by
  obtain ⟨j, b⟩ := x
  cases b with
  | true =>
      simp only [Cayley.swapLetter, Bool.not_true, faceSteps_true, faceSteps_false,
        faceSteps_nil, List.append_nil]
      rw [A_negSteps_rev (D := D) (a * CayV.genE P (j, true)) j]
      rw [show a * CayV.genE P (j, true) * (CayV.genE P (j, true))⁻¹ = a by group]
  | false =>
      simp only [Cayley.swapLetter, Bool.not_false, faceSteps_true, faceSteps_false,
        faceSteps_nil, List.append_nil]
      rw [genE_false_eq P j, A_posSteps_rev (D := D) (a * (CayV.genE P (j, true))⁻¹) j]
      rw [show a * (CayV.genE P (j, true))⁻¹ * CayV.genE P (j, true) = a by group]

/-! ## Reading a whole word backwards -/

/-- **The steps of the reversed, sign-swapped word read at the endpoint are the reversed steps of
the word, each traversed the other way.** -/
theorem faceSteps_revSwap (D : GeoData T t₀ P) (a : G) (w : List (Fin P.n × Bool)) :
    faceSteps D (endPt P a w) (w.reverse.map Cayley.swapLetter) =
      (faceSteps D a w).reverse.map op := by
  induction w generalizing a with
  | nil => simp
  | cons x w ih =>
      have hrev : (x :: w).reverse.map Cayley.swapLetter =
          w.reverse.map Cayley.swapLetter ++ [Cayley.swapLetter x] := by
        rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      have h1 : faceSteps D (endPt P a (x :: w))
            (w.reverse.map Cayley.swapLetter ++ [Cayley.swapLetter x]) =
          (faceSteps D (a * CayV.genE P x) w).reverse.map op ++
            faceSteps D (a * CayV.genE P x) [Cayley.swapLetter x] := by
        rw [endPt_cons, faceSteps_append, A_endPt_rev (a * CayV.genE P x) w,
          ih (a * CayV.genE P x)]
      have h2 : (faceSteps D a (x :: w)).reverse.map op =
          (faceSteps D (a * CayV.genE P x) w).reverse.map op ++
            faceSteps D (a * CayV.genE P x) [Cayley.swapLetter x] := by
        rw [faceSteps_cons, List.reverse_append, List.map_append, ← faceSteps_single]
      rw [hrev, h1, h2]

/-! ## The requested statement -/

theorem A_reverse {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (τ : Work.ORDunwoody.Dunwoody.Track D) (a : G) (w : List (Fin P.n × Bool)) :
    Work.ORDunwoody.Dunwoody.A τ a w =
      Work.ORDunwoody.Dunwoody.A τ (Work.ORDunwoody.Dunwoody.endPt P a w)
        (w.reverse.map Work.ORDunwoody.Cayley.swapLetter) := by
  unfold A
  rw [faceSteps_revSwap, List.map_map]
  have hfun : (stepHit τ ∘ op) = stepHit τ := funext fun s => stepHit_op τ s
  rw [hfun, List.map_reverse, List.sum_reverse]

end Work.ORDunwoody
