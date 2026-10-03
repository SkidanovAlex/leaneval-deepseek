/-
# The datum of the small model

Given a graph `V`, a groupoid presentation `P`, a datum `D` in `P` and a skeleton `S` of `V`
(`Submission/Work/Case1/Skeleton.lean`), this file transports the datum to the small
presentation `smallPresentation S P D hrel` of `Submission/Work/Case1/SmallPresentation.lean`:

* the generators `γ_j` are the encodings of the generators of `D` (`smallGamma`);
* the relators of the transported terms are the encoded relators of the terms of `D`, indexed by
  their position in the sorted list `rels P D` (`smallTerm`);
* the identity `W_j(γ) = ∏ δ α δ⁻¹` is transported along the encoding of paths
  (`encVG_loop_smallTerm` + the universal property of `FreeGroup.lift`).

Every property of the transported datum (`measure`, `usedArrowsList`, `UsedRelator`, connectivity,
the vanishing statement) is proved in companion files and assembled into `exists_smallDatum`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.mem_visitedList_of_mem_usedArrowsList
import Submission.Work.Case1.SmallPresentation
import Submission.Work.Case1.SmallTransfer

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

namespace SmallDatum

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u}

/-! ## The skeleton of a datum -/

/-- If the graph is connected from `v` and the datum uses every arrow, then every vertex of the
graph is visited by the datum. -/
theorem mem_visitedList_of_conn {P : Presentation V} {v : V} {n : ℕ} (D : Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList) : ∀ x : V, x ∈ D.visitedList := by
  intro x
  obtain ⟨p⟩ := hconn x
  induction p with
  | nil => exact D.mem_visitedList_base
  | cons p e ih =>
      exact (mem_visitedList_of_mem_usedArrowsList D (hpair (Quiver.Total.mk _ _ e))).2

/-- **The skeleton of a datum**: the vertices and arrows used by the datum, indexed by `Fin`'s.
The type `W : Type u` fixes the universe in which the small graph is built. -/
noncomputable def smallSkel {P : Presentation V} {v : V} {n : ℕ} (D : Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList) (W : Type u) : Skel V W := by
  classical
  exact
    { M := (D.visitedList.dedup).length
      fv := List.Nodup.getEquivOfForallMemList (D.visitedList.dedup)
        (List.nodup_dedup (D.visitedList))
        (fun x => List.mem_dedup.mpr (mem_visitedList_of_conn D hconn hpair x))
      k := (D.usedArrowsList.dedup).length
      fa := List.Nodup.getEquivOfForallMemList (D.usedArrowsList.dedup)
        (List.nodup_dedup (D.usedArrowsList)) (fun e => List.mem_dedup.mpr (hpair e)) }

/-! ## The generators -/

/-- The generator `γ_j` of the transported datum: the encoding of the generator of `D`. -/
noncomputable def smallGamma (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (j : Fin n) : VertexGroup (S.encObj v) :=
  SmallTransfer.encVG S v (D.γ j)

/-! ## The terms -/

/-- The base vertex of the transported term is the encoding of the base vertex of the original. -/
theorem smallBase_eq (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) (t : RelatorTerm P v) (ht : t.i ∈ SmallPres.rels P D) :
    (SmallPres.smallPresentation S P D hrel).base (ULift.up (SmallPres.relInvOf P D t.i ht)) =
      S.encObj (P.base t.i) :=
  congrArg (fun c => S.encObj (P.base c)) (SmallPres.rel_relInvOf ht)

/-- A term of the datum, transported to the small presentation. -/
noncomputable def smallTerm (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    RelatorTerm (SmallPres.smallPresentation S P D hrel) (S.encObj v) where
  i := ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht))
  sign := t.sign
  δ := (S.enc.mapPath t.δ).cast rfl
    (smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm
  reduced := (PathCast.cast_isReduced _ _ _).mpr
    (PrefunctorAux.mapPath_isReduced S.enc S.encObj_injective (fun _ _ => S.enc_map_injective)
      t.reduced)

/-- The relator path of the transported term is the encoding of the relator path of the original,
up to the casting of its endpoints. -/
theorem smallPath_eq (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n} (t : RelatorTerm P v) (ht : t ∈ D.terms j) :
    (SmallPres.smallPresentation S P D hrel).path
        (ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht))) =
      (S.enc.mapPath (P.path t.i)).cast
        (smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm
        (smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm := by
  have hrel' := SmallPres.rel_relInvOf (SmallPres.term_i_mem_rels ht)
  have hheq : HEq (P.path (SmallPres.rel P D (SmallPres.relInvOf P D t.i
      (SmallPres.term_i_mem_rels ht)))) (P.path t.i) := by
    rw [hrel']
  have hc : (P.path t.i).cast ((congrArg P.base hrel').symm) ((congrArg P.base hrel').symm) =
      P.path (SmallPres.rel P D (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht))) :=
    (Quiver.Path.cast_eq_iff_heq _ _ _ _).mpr hheq.symm
  have h2 := congrArg (fun p => S.enc.mapPath p) hc
  rw [PrefunctorAux.mapPath_cast (F := S.enc) (p := P.path t.i)
    (h1 := (congrArg P.base hrel').symm) (h2 := (congrArg P.base hrel').symm)] at h2
  show S.enc.mapPath (P.path (SmallPres.rel P D (SmallPres.relInvOf P D t.i
      (SmallPres.term_i_mem_rels ht)))) = _
  exact h2.symm

/-- The terms of the transported datum: the terms of `D`, transported. -/
noncomputable def smallTerms (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    List (RelatorTerm (SmallPres.smallPresentation S P D hrel) (S.encObj v)) :=
  (D.terms j).attach.map (fun t => smallTerm S P D hrel t.1 t.2)

/-! ## The loop of a transported term is the encoding of the loop of the term -/

/-- The encoding of the loop of a term is the loop of the transported term. -/
theorem encVG_loop_smallTerm (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    SmallTransfer.encVG S v (RelatorTerm.loop t) =
      RelatorTerm.loop (smallTerm S P D hrel t ht) := by
  rw [RelatorTerm.loop, RelatorTerm.loop]
  apply Subtype.ext
  show S.enc.mapPath (Work.ORLocInd.Howie.pmul t.δ
      (Work.ORLocInd.Howie.pmul t.signedPath t.δ.reverse)) =
    Work.ORLocInd.Howie.pmul (smallTerm S P D hrel t ht).δ
      (Work.ORLocInd.Howie.pmul (smallTerm S P D hrel t ht).signedPath
        (smallTerm S P D hrel t ht).δ.reverse)
  rw [PrefunctorAux.mapPath_pmul S.enc S.encObj_injective (fun _ _ => S.enc_map_injective) t.δ _,
    PrefunctorAux.mapPath_pmul S.enc S.encObj_injective (fun _ _ => S.enc_map_injective)
      t.signedPath t.δ.reverse,
    PrefunctorAux.mapPath_reverse S.enc t.δ]
  have hdel : (smallTerm S P D hrel t ht).δ =
      (S.enc.mapPath t.δ).cast rfl
        (smallBase_eq S P D hrel t (SmallPres.term_i_mem_rels ht)).symm := rfl
  have hpath : (smallTerm S P D hrel t ht).signedPath =
      (if t.sign = true then ((SmallPres.smallPresentation S P D hrel).path
          (ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht)))).reverse
        else (SmallPres.smallPresentation S P D hrel).path
          (ULift.up (SmallPres.relInvOf P D t.i (SmallPres.term_i_mem_rels ht)))) := by
    rw [RelatorTerm.signedPath]
    rfl
  rw [hdel, hpath, RelatorTerm.signedPath]
  by_cases hs : t.sign = true
  · rw [if_pos hs, if_pos hs, PrefunctorAux.mapPath_reverse S.enc (P.path t.i),
      smallPath_eq S P D hrel t ht, PathCast.cast_reverse]
    exact (PathCast.cast_conj_loop _ _ _).symm
  · rw [if_neg hs, if_neg hs, smallPath_eq S P D hrel t ht]
    exact (PathCast.cast_conj_loop _ _ _).symm

/-! ## The transported datum -/

/-- **The datum of the small model**: the datum `D` of `P` transported to the small presentation
`smallPresentation S P D hrel` of a skeleton `S` of `V`. -/
noncomputable def smallDatum (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) :
    Datum (SmallPres.smallPresentation S P D hrel) (S.encObj v) n where
  γ := smallGamma S P D
  W := D.W
  terms := smallTerms S P D hrel
  heq := fun j => by
    have h1 : FreeGroup.lift (smallGamma S P D) (D.W j)
        = SmallTransfer.encVG S v (FreeGroup.lift D.γ (D.W j)) := by
      refine (FreeGroup.lift_unique ((SmallTransfer.encVG S v).comp (FreeGroup.lift D.γ)) ?_
        (x := D.W j)).symm
      intro a
      show (SmallTransfer.encVG S v) (FreeGroup.lift D.γ (FreeGroup.of a)) = smallGamma S P D a
      rw [FreeGroup.lift_apply_of]
      rfl
    have hterms : ((D.terms j).map RelatorTerm.loop).map (⇑(SmallTransfer.encVG S v)) =
        (smallTerms S P D hrel j).map RelatorTerm.loop := by
      rw [List.map_map]
      show (D.terms j).map (fun t => SmallTransfer.encVG S v (RelatorTerm.loop t)) =
        ((D.terms j).attach.map (fun t => smallTerm S P D hrel t.1 t.2)).map RelatorTerm.loop
      rw [List.map_map]
      show (D.terms j).map (fun t => SmallTransfer.encVG S v (RelatorTerm.loop t)) =
        (D.terms j).attach.map (fun t => RelatorTerm.loop (smallTerm S P D hrel t.1 t.2))
      rw [← List.attach_map_val (l := D.terms j)
        (f := fun t => SmallTransfer.encVG S v (RelatorTerm.loop t))]
      exact List.map_congr_left (fun t _ => encVG_loop_smallTerm S P D hrel t.1 t.2)
    rw [h1, D.heq j, map_list_prod, hterms]

/-! ## Connectivity and the decoding of the generators -/

/-- The small graph is connected as soon as the original one is (the encoding of a path from `v` to
`S.decObj x` is a path from `S.encObj v` to `x`). -/
theorem smallDatum_reachable (S : Skel V W) {v : V} (hconn : ∀ x : V, Nonempty (Quiver.Path v x)) :
    ∀ x : S.Vx, Nonempty (Quiver.Path (S.encObj v) x) := by
  intro x
  obtain ⟨p⟩ := hconn (S.decObj x)
  exact ⟨(S.enc.mapPath p).cast rfl (Skel.encObj_decObj S x)⟩

/-- The decoding of the transported generator is the original generator. -/
theorem smallDatum_decode_gamma (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) (j : Fin n) :
    SmallTransfer.decode S v ((smallDatum S P D hrel).γ j) = D.γ j :=
  SmallTransfer.decode_encVG S v (D.γ j)

end SmallDatum

end Work.Case1
