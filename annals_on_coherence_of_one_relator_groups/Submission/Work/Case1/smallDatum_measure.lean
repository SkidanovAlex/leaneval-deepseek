/-
# The measure of the small model

`Work.Case1.SmallDatum.smallDatum` transports a datum `D` of a groupoid presentation `P` on `V` to
the small presentation `SmallPres.smallPresentation S P D hrel` on the skeleton `S.Vx` of `V`
(`Submission/Work/Case1/Skeleton.lean`, `Submission/Work/Case1/SmallDatum.lean`).

This file proves that the transport preserves the two numerical invariants of the datum:

* `L(∆)`, the total length of the paths `γ_j`, `δ_{j,k}` and `α_{j,k}` of the datum, and
* `M(∆)`, the number of distinct vertices visited by the datum,

so that the induction measure `2 * L(∆) + 2 - M(∆)` is preserved as well.

The proof pushes the encoding `S.enc` — a prefunctor which is injective on objects and on arrows —
through the lists defining `L` and `M`.  The path-level inputs are
`PrefunctorAux.mapPath_length` (`(S.enc.mapPath p).length = p.length`) and
`PrefunctorAux.mapPath_vertices` (`(S.enc.mapPath p).vertices = p.vertices.map S.encObj`), together
with the fact that the casting of a path along an equality of its endpoints leaves its length and
its vertex list unchanged (`PathCast.cast_length`, `PathCast.cast_vertices`); the list-level inputs
are the auxiliary lemmas below, which handle the `List.attach`-indexed list of the terms of the
datum (`SmallDatum.smallTerms`) and the `List.dedup` counting the distinct visited vertices.
-/
import Mathlib
import Submission.Work.Case1.SmallDatum
import Submission.Work.Case1.SmallPresentation
import Submission.Work.ORLocInd.Howie.Datum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

/-! ## Auxiliary lemmas on lists -/

namespace SmallDatumMeasure

/-- Mapping a `List.flatMap` over a list indexed by `List.attach`: if the attached terms are first
mapped by `F` and then flattened by `H`, and `H (F t)` is the image under `g` of a list `G` of the
underlying term `t.1`, then the flattening is the image under `g` of the flattening of `G`. -/
theorem flatMap_attach_map {α β γ δ : Type*} (l : List α) (F : {a // a ∈ l} → β)
    (H : β → List δ) (G : α → List γ) (g : γ → δ)
    (h : ∀ t : {a // a ∈ l}, H (F t) = (G t.1).map g) :
    (l.attach.map F).flatMap H = (l.flatMap G).map g := by
  rw [List.flatMap_map, List.flatMap_congr (fun t _ => h t), ← List.flatMap_map,
    List.attach_map_val, List.flatMap_map, List.map_flatMap]

/-- Summing over a list indexed by `List.attach`: if the value attached to `t` is the value of a
function of `t.1`, the two sums agree. -/
theorem sum_attach_map {α : Type*} (l : List α) (F : {a // a ∈ l} → ℕ) (G : α → ℕ)
    (h : ∀ t : {a // a ∈ l}, F t = G t.1) : (l.attach.map F).sum = (l.map G).sum := by
  rw [List.map_congr_left (fun t _ => h t), List.attach_map_val]

/-- Deduplicating a mapped list does not change its length. -/
theorem dedup_map_length {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) : (l.map f).dedup.length = l.dedup.length := by
  rw [List.dedup_map_of_injective hf, List.length_map]

/-! ## The generators of the small datum -/

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u}

/-- The length of the transported generator is the length of the original one. -/
theorem smallGamma_length (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (j : Fin n) : (((SmallDatum.smallGamma S P D j).1).length) = (((D.γ j).1).length) := by
  simp only [SmallDatum.smallGamma, SmallTransfer.encVG_apply, PrefunctorAux.mapPath_length]

/-- The vertex list of the transported generator is the image of the vertex list of the original
one. -/
theorem smallGamma_vertices (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (j : Fin n) :
    (((SmallDatum.smallGamma S P D j).1).vertices) = (((D.γ j).1).vertices).map S.encObj := by
  rw [SmallDatum.smallGamma, SmallTransfer.encVG_apply, PrefunctorAux.mapPath_vertices]

/-! ## The terms of the small datum -/

/-- The weight of a transported term is the weight of the term: encoding a path does not change its
length, and the relator of the transported term is the encoding of the relator of the term. -/
theorem smallTerm_weight (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    RelatorTerm.weight (SmallDatum.smallTerm S P D hrel t ht) = RelatorTerm.weight t := by
  rw [RelatorTerm.weight, RelatorTerm.weight]
  congr 1
  · rw [show (SmallDatum.smallTerm S P D hrel t ht).δ =
        (S.enc.mapPath t.δ).cast rfl
          (SmallDatum.smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm from rfl,
      PathCast.cast_length, PrefunctorAux.mapPath_length]
  · rw [show (SmallDatum.smallTerm S P D hrel t ht).i =
        ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht)) from rfl,
      SmallDatum.smallPath_eq S P D hrel t ht, PathCast.cast_length,
      PrefunctorAux.mapPath_length]

/-- The visited vertices of a transported term are the images of the visited vertices of the
term. -/
theorem smallTerm_visitedList (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    RelatorTerm.visitedList (SmallDatum.smallTerm S P D hrel t ht) =
      (RelatorTerm.visitedList t).map S.encObj := by
  rw [RelatorTerm.visitedList, RelatorTerm.visitedList, List.map_append]
  congr 1
  · rw [show (SmallDatum.smallTerm S P D hrel t ht).δ =
        (S.enc.mapPath t.δ).cast rfl
          (SmallDatum.smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm from rfl,
      PathCast.cast_vertices, PrefunctorAux.mapPath_vertices]
  · rw [show (SmallDatum.smallTerm S P D hrel t ht).i =
        ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht)) from rfl,
      SmallDatum.smallPath_eq S P D hrel t ht, PathCast.cast_vertices,
      PrefunctorAux.mapPath_vertices]

/-! ## The pieces of `L` and `M` -/

/-- The length of the `j`-th generator of the transported datum. -/
theorem smallDatum_gamma_length (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    (((SmallDatum.smallDatum S P D hrel).γ j).1).length = (((D.γ j).1).length) := by
  show (((SmallDatum.smallGamma S P D j).1).length) = (((D.γ j).1).length)
  exact smallGamma_length S P D j

/-- The vertices of the `j`-th generator of the transported datum. -/
theorem smallDatum_gamma_vertices (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    (((SmallDatum.smallDatum S P D hrel).γ j).1).vertices =
      (((D.γ j).1).vertices).map S.encObj := by
  show (((SmallDatum.smallGamma S P D j).1).vertices) = (((D.γ j).1).vertices).map S.encObj
  exact smallGamma_vertices S P D j

/-- The total weight of the `j`-th list of terms of the transported datum. -/
theorem smallDatum_terms_weight (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    (((SmallDatum.smallDatum S P D hrel).terms j).map RelatorTerm.weight).sum
      = ((D.terms j).map RelatorTerm.weight).sum := by
  rw [show (SmallDatum.smallDatum S P D hrel).terms j = SmallDatum.smallTerms S P D hrel j from rfl,
    SmallDatum.smallTerms, List.map_map]
  exact sum_attach_map (D.terms j)
    (fun t => RelatorTerm.weight (SmallDatum.smallTerm S P D hrel t.1 t.2))
    (fun t => RelatorTerm.weight t) (fun t => smallTerm_weight S P D hrel t.1 t.2)

/-- The vertices visited by the `j`-th list of terms of the transported datum. -/
theorem smallDatum_terms_visited (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    (((SmallDatum.smallDatum S P D hrel).terms j).flatMap RelatorTerm.visitedList)
      = ((D.terms j).flatMap RelatorTerm.visitedList).map S.encObj := by
  rw [show (SmallDatum.smallDatum S P D hrel).terms j = SmallDatum.smallTerms S P D hrel j from rfl,
    SmallDatum.smallTerms]
  exact flatMap_attach_map (D.terms j) (fun t => SmallDatum.smallTerm S P D hrel t.1 t.2)
    RelatorTerm.visitedList RelatorTerm.visitedList S.encObj
    (fun t => smallTerm_visitedList S P D hrel t.1 t.2)

/-- The vertices visited by the transported datum are the images of those visited by the datum. -/
theorem smallDatum_visitedList (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) :
    (SmallDatum.smallDatum S P D hrel).visitedList = D.visitedList.map S.encObj := by
  rw [Datum.visitedList, Datum.visitedList]
  simp only [List.map_append, List.map_cons, List.map_nil]
  congr 1
  congr 1
  · rw [List.map_flatMap]
    exact List.flatMap_congr (fun j _ => smallDatum_gamma_vertices S P D hrel j)
  · rw [List.map_flatMap]
    exact List.flatMap_congr (fun j _ => smallDatum_terms_visited S P D hrel j)

end SmallDatumMeasure

theorem smallDatum_measure {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {W : Type u} (S : Work.Case1.Skel V W) (P : Work.ORLocInd.Howie.Presentation V) {v : V}
    {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) :
    (Work.Case1.SmallDatum.smallDatum S P D hrel).L = D.L ∧
      (Work.Case1.SmallDatum.smallDatum S P D hrel).M = D.M := by
  constructor
  · rw [Datum.L, Datum.L]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      exact SmallDatumMeasure.smallDatum_gamma_length S P D hrel j
    · apply Finset.sum_congr rfl
      intro j _
      exact SmallDatumMeasure.smallDatum_terms_weight S P D hrel j
  · rw [Datum.M, Datum.M, SmallDatumMeasure.smallDatum_visitedList S P D hrel,
      SmallDatumMeasure.dedup_map_length (Skel.encObj_injective S) D.visitedList]

end Work.Case1
