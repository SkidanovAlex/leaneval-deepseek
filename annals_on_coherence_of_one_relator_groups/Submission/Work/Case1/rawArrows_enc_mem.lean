/-
# The arrows of the small datum are the encodings of the arrows of the datum

The arrows occurring in the datum `D` (`Datum.rawArrows D`, `Submission/Work/ORLocInd/Howie/Span.lean`,
`Submission/Work/ORLocInd/Howie/Datum.lean`) are

* the arrows of the generators `γ_j`,
* the arrows of the paths `δ_{j,k}` of the terms of `D`, and
* the arrows of the relator paths `α_{j,k}` of the terms of `D`.

The transport of `D` to the small presentation of a skeleton `S`
(`Submission/Work/Case1/SmallDatum.lean`) sends each of these to its encoding:
`(smallDatum S P D hrel).γ j` is `S.enc` of `D.γ j` (a `VertexGroup`, i.e. its underlying path is
`S.enc.mapPath (D.γ j).1`), the `δ` of the transported term is the (cast) encoding of `δ`, and the
relator path of the transported term is the encoding of the relator path of `t.i` (the reindexing
`relInvOf` of the relator indices is inverted by `SmallPres.rel_relInvOf`).

This file records the resulting statement: the encoding of an arrow of `D` is an arrow of the small
datum.  (It is the "arrows are used" half of the transport of the datum; the vertex half is
`Submission/Work/Case1/smallDatum_visitedList.lean`.)
-/
import Mathlib
import Submission.Work.Case1.SmallDatum
import Submission.Work.Case1.SmallPresentation
import Submission.Work.Case1.Skeleton

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

/-! ## The three kinds of arrows of a datum -/

/-- The encoding of an arrow of a generator `γ_j` is an arrow of the transported generator. -/
private theorem totalMap_mem_smallGamma_arrowList {V : Type v} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u} (S : Skel V W) (P : Presentation V)
    {v : V} {n : ℕ} (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n)
    {e : Quiver.Total V} (he : e ∈ (D.γ j).1.arrowList) :
    PrefunctorAux.totalMap S.enc e ∈ ((SmallDatum.smallDatum S P D hrel).γ j).1.arrowList := by
  rw [show (SmallDatum.smallDatum S P D hrel).γ j = SmallTransfer.encVG S v (D.γ j) from rfl,
    SmallTransfer.encVG_apply, PrefunctorAux.mapPath_arrowList]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- The encoding of an arrow of a path `δ` of a term is an arrow of the path `δ` of the transported
term. -/
private theorem totalMap_mem_smallTerm_delta {V : Type v} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u} (S : Skel V W) (P : Presentation V)
    {v : V} {n : ℕ} (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n}
    {t : RelatorTerm P v} (ht : t ∈ D.terms j) {e : Quiver.Total V} (he : e ∈ t.δ.arrowList) :
    PrefunctorAux.totalMap S.enc e ∈ (SmallDatum.smallTerm S P D hrel t ht).δ.arrowList := by
  show PrefunctorAux.totalMap S.enc e ∈ ((S.enc.mapPath t.δ).cast rfl
    (SmallDatum.smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm).arrowList
  rw [PathCast.cast_arrowList, PrefunctorAux.mapPath_arrowList]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- The encoding of an arrow of the relator path `α` of a term is an arrow of the relator path of the
transported term (the reindexing of the relator indices by `SmallPres.relInvOf` is inverted by
`SmallPres.rel_relInvOf`). -/
private theorem totalMap_mem_smallTerm_path {V : Type v} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u} (S : Skel V W) (P : Presentation V)
    {v : V} {n : ℕ} (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n}
    {t : RelatorTerm P v} (ht : t ∈ D.terms j) {e : Quiver.Total V}
    (he : e ∈ (P.path t.i).arrowList) :
    PrefunctorAux.totalMap S.enc e
      ∈ ((SmallPres.smallPresentation S P D hrel).path (SmallDatum.smallTerm S P D hrel t ht).i).arrowList := by
  show PrefunctorAux.totalMap S.enc e ∈ (S.enc.mapPath (P.path (SmallPres.rel P D
    (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht))))).arrowList
  rw [SmallPres.rel_relInvOf (SmallPres.term_i_mem_rels ht), PrefunctorAux.mapPath_arrowList]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- A transported term is one of the transported terms of its index. -/
private theorem smallTerm_mem_smallTerms {V : Type v} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u} (S : Skel V W) (P : Presentation V)
    {v : V} {n : ℕ} (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n}
    {t : RelatorTerm P v} (ht : t ∈ D.terms j) :
    SmallDatum.smallTerm S P D hrel t ht ∈ (SmallDatum.smallDatum S P D hrel).terms j := by
  show SmallDatum.smallTerm S P D hrel t ht
    ∈ (D.terms j).attach.map (fun t => SmallDatum.smallTerm S P D hrel t.1 t.2)
  exact List.mem_map.mpr ⟨⟨t, ht⟩, List.mem_attach _ _, rfl⟩

/-- **The arrows of the small datum**.  Every arrow used by the datum `D` is carried by the encoding
into an arrow used by the transported datum `smallDatum S P D hrel`. -/
theorem rawArrows_enc_mem {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {W : Type u} (S : Work.Case1.Skel V W) (P : Work.ORLocInd.Howie.Presentation V) {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    {e : Quiver.Total V} (he : e ∈ Work.ORLocInd.Howie.Datum.rawArrows D) :
    Work.Case1.PrefunctorAux.totalMap S.enc e ∈
      Work.ORLocInd.Howie.Datum.rawArrows (Work.Case1.SmallDatum.smallDatum S P D hrel) := by
  rw [Datum.rawArrows, List.mem_append] at he
  rw [Datum.rawArrows, List.mem_append]
  rcases he with he | he
  · -- the arrows of the generators
    left
    obtain ⟨j, -, hej⟩ := List.mem_flatMap.mp he
    exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      totalMap_mem_smallGamma_arrowList S P D hrel j hej⟩
  · -- the arrows of the paths of the terms
    right
    obtain ⟨j, -, hej⟩ := List.mem_flatMap.mp he
    refine List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩
    obtain ⟨t, ht, het⟩ := List.mem_flatMap.mp hej
    refine List.mem_flatMap.mpr ⟨SmallDatum.smallTerm S P D hrel t ht,
      smallTerm_mem_smallTerms S P D hrel ht, ?_⟩
    rcases List.mem_append.mp het with h | h
    · exact List.mem_append.mpr (Or.inl (totalMap_mem_smallTerm_delta S P D hrel ht h))
    · exact List.mem_append.mpr (Or.inr (totalMap_mem_smallTerm_path S P D hrel ht h))

end Work.Case1
