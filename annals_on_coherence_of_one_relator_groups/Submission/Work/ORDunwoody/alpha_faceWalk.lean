/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# `alpha τ` kills the boundary walk of a face

`Dunwoody/Alpha.lean` defines the counting cochain `phi τ` on the edges of the 1-skeleton of
`Λ''` and its integral `alpha τ` over a walk; `Work.ORDunwoody.alphaFaceWalkDefs` records the
contribution `stepHit τ s` of a *directed step* `s` of a boundary walk.  The present file proves
the computation announced in `DESIGN_N13.md` §9.5 (3b):

    alpha τ (boundary walk of a face) = #{ visits of that face lying in τ }   (in `ZMod 2`),

and, with `Work.ORDunwoody.even_visits_of_track` (the visits of a face in a track come in pairs),
the requested statement

    alpha τ (faceWalk D c (toWord r)) = 0 .

The three inputs of the computation are

* `alpha_faceWalk_aux` (proved here by induction on the word): the integral over the boundary
  walk of the word `w` read at `a` is the sum of the contributions of the steps of `w`;
* `Work.ORDunwoody.alpha_steps`: the integral over a walk that is the concatenation of the
  vertex lists of a *chain* of directed steps is the sum of the contributions `stepHit τ` of the
  steps (plus the integral of what remains after the chain);
* `Work.ORDunwoody.posSteps_facts` / `Work.ORDunwoody.negSteps_facts`: the steps of one letter
  of the word form such a chain, from the current base point to the next one;
* `Work.ORDunwoody.sum_stepHit`: the contribution of a step is `[m ∈ τ]` for the pattern point
  `m` of the step, so the total is — in `ZMod 2` — the number of steps whose pattern point lies
  in `τ`, i.e. the number of visits of the face in `τ`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Alpha
import Submission.Work.ORDunwoody.even_visits_of_track
import Submission.Work.ORDunwoody.faceVisits_eq_faceAux
import Submission.Work.ORDunwoody.faceAux_eq_faceSteps
import Submission.Work.ORDunwoody.faceWalk_getLast
import Submission.Work.ORDunwoody.alphaFaceWalkDefs
import Submission.Work.ORDunwoody.alpha_steps
import Submission.Work.ORDunwoody.sum_stepHit
import Submission.Work.ORDunwoody.posSteps_facts
import Submission.Work.ORDunwoody.negSteps_facts

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

/-! ## The integral over the boundary walk of a word -/

/-- **The integral of `phi τ` over the boundary walk of a word is the sum of the contributions of
its directed steps.**  The boundary walk of `w` read at `a` is the initial old vertex `(a, ∗)`
followed by the vertex lists of the steps of `w` (`faceWalk_eq`, `faceAux_eq_flatMap_verts`); the
steps of each letter form a chain (`posSteps_facts`, `negSteps_facts`), so `alpha_steps` computes
the integral one letter at a time. -/
theorem alpha_faceWalk_aux {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (τ : Track D) :
    ∀ (a : G) (w : List (Fin P.n × Bool)),
      alpha τ (faceWalk D a w) = ((faceSteps D a w).map (stepHit τ)).sum := by
  intro a w
  induction w generalizing a with
  | nil =>
      rw [faceWalk_eq, faceAux_nil, faceSteps_nil, List.map_nil, List.sum_nil, alpha_singleton]
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b with
      | true =>
          have hf := posSteps_facts (D := D) a j
          rw [faceWalk_eq, faceAux_true, edgeTailPos_eq_flatMap_verts,
            faceAux_eq_flatMap_verts, faceSteps_true]
          rw [alpha_steps τ (posSteps D a j) (a, Sum.inl ())
            (a * CayV.genE P (j, true), Sum.inl ())
            ((faceSteps D (a * CayV.genE P (j, true)) w).flatMap DStep.verts)
            hf.1 hf.2.1 hf.2.2.1 (fun h => absurd h hf.2.2.2)]
          rw [List.map_append, List.sum_append, ← faceAux_eq_flatMap_verts, ← faceWalk_eq]
          exact congrArg (fun z => _ + z) (ih (a * CayV.genE P (j, true)))
      | false =>
          have hf := negSteps_facts (D := D) a j
          rw [faceWalk_eq, faceAux_false, edgeTailNeg_eq_flatMap_verts,
            faceAux_eq_flatMap_verts, faceSteps_false]
          rw [alpha_steps τ (negSteps D a j) (a, Sum.inl ())
            (a * (CayV.genE P (j, true))⁻¹, Sum.inl ())
            ((faceSteps D (a * (CayV.genE P (j, true))⁻¹) w).flatMap DStep.verts)
            hf.1 hf.2.1 hf.2.2.1 (fun h => absurd h hf.2.2.2)]
          rw [List.map_append, List.sum_append, ← faceAux_eq_flatMap_verts, ← faceWalk_eq]
          exact congrArg (fun z => _ + z) (ih (a * (CayV.genE P (j, true))⁻¹))

/-! ## The requested statement -/

/-- **`alpha τ` of the boundary walk of a face of `Λ''` vanishes.**  The integral is (in `ZMod 2`)
the number of visits of the face lying in the track `τ` (`alpha_faceWalk_aux`, `sum_stepHit`), and
that number is even (`even_visits_of_track`): the visits of a face in a track come in pairs. -/
theorem alpha_faceWalk {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G)
    (τ : Work.ORDunwoody.Dunwoody.Track D) :
    Work.ORDunwoody.Dunwoody.alpha τ
      (Work.ORDunwoody.Dunwoody.faceWalk D c (FreeGroup.toWord r.1)) = 0 := by
  haveI : DecidableEq (Track D) := Classical.decEq _
  have hvis : faceVisits D c (FreeGroup.toWord r.1) =
      (faceSteps D c (FreeGroup.toWord r.1)).filterMap DStep.mid? := by
    rw [faceVisits_eq_faceAux, faceAux_eq_faceSteps]
  rw [alpha_faceWalk_aux τ c (FreeGroup.toWord r.1),
    sum_stepHit τ (faceSteps D c (FreeGroup.toWord r.1)), ← hvis,
    ZMod.natCast_eq_zero_iff]
  exact even_iff_two_dvd.mp (even_visits_of_track r c τ)

end Work.ORDunwoody
