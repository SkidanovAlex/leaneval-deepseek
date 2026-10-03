/-
# Transporting a datum to the span of the presentation (Howie 2000, step 1)

Howie's first step in the proof of Theorem 3.1 replaces the graph `Γ` by the smallest subgraph
`Γ₀` containing all the paths of a datum `∆`, and the relators `R` by the relators occurring in
`∆`.  This file constructs the datum `∆₀` of the resulting sub-presentation
(`spanPresentation D`) and proves the properties needed for the reduction.

Target statement: `Work.ORLocInd.Howie.exists_spanDatum`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.erase_pmul
import Submission.Work.ORLocInd.Howie.erase_isReduced
import Submission.Work.ORLocInd.Howie.erase_pathToSpan
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.Howie

open _root_.Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Presentation V} {v : V} {n : ℕ}

/-! ## The base vertex of the span -/

/-- The base vertex `v` of the datum, as a vertex of the span. -/
abbrev spanV (D : Datum P v n) : SpanVertex D := ⟨v, D.mem_visitedList_base⟩

/-! ## Erasure of the span and its properties -/

/-- Erasure commutes with reversal of paths. -/
theorem erase_reverse (D : Datum P v n) {u w : SpanVertex D} (p : Quiver.Path u w) :
    erase D w p.reverse = (erase D u p).reverse := by
  rw [← erasePrefunctor_mapPath D w p.reverse, ← erasePrefunctor_mapPath D u p]
  exact Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse (erasePrefunctor D) p

/-- Erasure is injective on paths of the span. -/
theorem erase_injective (D : Datum P v n) (u w : SpanVertex D) :
    Function.Injective (fun p : Quiver.Path u w => erase D u p) := by
  intro p q h
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons q f => exact absurd h.symm (Quiver.Path.cons_ne_nil (erase D u q) _)
  | cons p' e ih =>
    cases q with
    | nil => exact absurd h (Quiver.Path.cons_ne_nil (erase D u p') _)
    | cons q' f =>
      change erase D u (Quiver.Path.cons p' e) = erase D u (Quiver.Path.cons q' f) at h
      rw [erase_cons, erase_cons] at h
      have hbc : _ = _ := Quiver.Path.obj_eq_of_cons_eq_cons h
      have hbceq : _ = _ := Subtype.ext hbc
      subst hbceq
      have hpq : erase D u p' = erase D u q' :=
        eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
      rw [ih hpq]
      have hhom : HEq e.1.hom f.1.hom :=
        (Quiver.Hom.cast_heq e.2.1 e.2.2.1 e.1.hom).symm.trans
          ((Quiver.Path.hom_heq_of_cons_eq_cons h).trans
            (Quiver.Hom.cast_heq f.2.1 f.2.2.1 f.1.hom))
      have hef : e.1 = f.1 :=
        Quiver.Total.ext (e.2.1.trans f.2.1.symm) (e.2.2.1.trans f.2.2.1.symm) hhom
      exact congrArg (fun x => Quiver.Path.cons q' x) (Subtype.ext hef)

/-- Erasure of a path of the span, as a map of vertex groups. -/
noncomputable def eraseVG (D : Datum P v n) (u : SpanVertex D) :
    VertexGroup u →* VertexGroup u.1 where
  toFun x := ⟨erase D u x.1, isReduced_erase D x.1 x.2⟩
  map_one' := Subtype.ext (by
    show erase D u (1 : VertexGroup u).1 = (1 : VertexGroup u.1).1
    rw [VertexGroup.coe_one, VertexGroup.coe_one]
    exact erase_nil D u)
  map_mul' x y := Subtype.ext (by
    show erase D u ((x * y : VertexGroup u)).1 = pmul (erase D u x.1) (erase D u y.1)
    rw [VertexGroup.coe_mul]
    exact erase_pmul D x.1 y.1)

@[simp] theorem eraseVG_apply (D : Datum P v n) (u : SpanVertex D) (x : VertexGroup u) :
    (eraseVG D u x).1 = erase D u x.1 := rfl

/-- `eraseVG` is injective. -/
theorem eraseVG_injective (D : Datum P v n) (u : SpanVertex D) :
    Function.Injective (eraseVG D u) := by
  intro x y h
  apply Subtype.ext
  exact erase_injective D u u (congrArg Subtype.val h)

/-- The erasure of the span path of a relator of `P` occurring in the datum is the relator. -/
theorem erase_spanPath (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    erase D (spanBase D i) (spanPath D i) = P.path i.1 :=
  erase_pathToSpan D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
    (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)

/-- Projection of a total arrow of the span to a total arrow of the ambient graph. -/
def totalProj (D : Datum P v n) (f : Quiver.Total (SpanVertex D)) : Quiver.Total V := f.hom.1

@[simp] theorem totalProj_apply (D : Datum P v n) (f : Quiver.Total (SpanVertex D)) :
    totalProj D f = f.hom.1 := rfl

/-- Two total arrows of the span with the same underlying arrow of `Γ` are equal. -/
theorem spanTotal_ext {D : Datum P v n} {f g : Quiver.Total (SpanVertex D)}
    (h : f.hom.1 = g.hom.1) : f = g := by
  obtain ⟨fl, fr, fh⟩ := f
  obtain ⟨gl, gr, gh⟩ := g
  have hleft : fl = gl := Subtype.ext (fh.2.1.symm.trans ((congrArg Quiver.Total.left h).trans gh.2.1))
  have hright : fr = gr := Subtype.ext (fh.2.2.1.symm.trans ((congrArg Quiver.Total.right h).trans gh.2.2.1))
  subst hleft
  subst hright
  exact congrArg (Quiver.Total.mk fl fr) (Subtype.ext h)

/-! ## The transported datum: generators, terms, datum -/

/-- The generator `γ_j` of the datum, as a closed path of the span. -/
noncomputable def spanGamma (D : Datum P v n) (j : Fin n) : VertexGroup (spanV D) :=
  ⟨pathToSpan D v D.mem_visitedList_base (D.γ j).1 D.mem_visitedList_base (inSpan_gamma D j),
    (erase_isReduced D _).mp (by
      show (erase D (spanV D)
        (pathToSpan D v D.mem_visitedList_base (D.γ j).1 D.mem_visitedList_base
          (inSpan_gamma D j))).IsReduced
      rw [show erase D (spanV D)
          (pathToSpan D v D.mem_visitedList_base (D.γ j).1 D.mem_visitedList_base
            (inSpan_gamma D j)) = (D.γ j).1 from
        erase_pathToSpan D (D.γ j).1 D.mem_visitedList_base D.mem_visitedList_base
          (inSpan_gamma D j)]
      exact (D.γ j).2)⟩

/-- The erasure of the transported generator is the original generator. -/
theorem eraseVG_spanGamma (D : Datum P v n) (j : Fin n) :
    eraseVG D (spanV D) (spanGamma D j) = D.γ j := by
  apply Subtype.ext
  show erase D (spanV D)
      (pathToSpan D v D.mem_visitedList_base (D.γ j).1 D.mem_visitedList_base
        (inSpan_gamma D j)) = (D.γ j).1
  exact erase_pathToSpan D (D.γ j).1 D.mem_visitedList_base D.mem_visitedList_base
    (inSpan_gamma D j)

/-- A term of the datum, transported to the span. -/
noncomputable def spanTerm (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) : RelatorTerm (spanPresentation D) (spanV D) where
  i := ⟨t.i, usedRelator_of_mem_terms ht⟩
  sign := t.sign
  δ := pathToSpan D v D.mem_visitedList_base t.δ
        (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)) (inSpan_delta D ht)
  reduced := (erase_isReduced D _).mp (by
    show (erase D (spanV D)
      (pathToSpan D v D.mem_visitedList_base t.δ
        (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht))
          (inSpan_delta D ht))).IsReduced
    rw [show erase D (spanV D)
        (pathToSpan D v D.mem_visitedList_base t.δ
          (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht))
            (inSpan_delta D ht)) = t.δ from
      erase_pathToSpan D t.δ D.mem_visitedList_base
        (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)) (inSpan_delta D ht)]
    exact t.reduced)

/-- The terms of the transported datum: the terms of `D`, transported. -/
noncomputable def spanTerms (D : Datum P v n) (j : Fin n) :
    List (RelatorTerm (spanPresentation D) (spanV D)) :=
  (D.terms j).attach.map (fun t => spanTerm D t.1 t.2)

/-- The `signedPath` of a term with matching index and sign, after transport. -/
theorem erase_signedPath_of (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) (sign : Bool) :
    erase D ((spanPresentation D).base i)
      (if sign then ((spanPresentation D).path i).reverse else (spanPresentation D).path i)
    = (if sign then (P.path i.1).reverse else P.path i.1) := by
  cases sign with
  | false => exact erase_spanPath D i
  | true =>
    show erase D ((spanPresentation D).base i) ((spanPresentation D).path i).reverse
      = (P.path i.1).reverse
    rw [erase_reverse]
    rw [show erase D ((spanPresentation D).base i) ((spanPresentation D).path i) = P.path i.1 from
      erase_spanPath D i]
    rfl

/-- A term of the datum and its transport have the same signed relator path, after erasure. -/
theorem erase_signedPath_spanTerm (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    erase D ((spanPresentation D).base (spanTerm D t ht).i)
      (RelatorTerm.signedPath (spanTerm D t ht)) = RelatorTerm.signedPath t := by
  rw [RelatorTerm.signedPath, RelatorTerm.signedPath]
  exact erase_signedPath_of D (spanTerm D t ht).i t.sign

/-- Erasing the loop of a transported term gives the loop of the original term. -/
theorem eraseVG_loop_spanTerm (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    eraseVG D (spanV D) (RelatorTerm.loop (spanTerm D t ht)) = RelatorTerm.loop t := by
  apply Subtype.ext
  show erase D (spanV D)
      (pmul (spanTerm D t ht).δ
        (pmul (RelatorTerm.signedPath (spanTerm D t ht)) (spanTerm D t ht).δ.reverse))
    = pmul t.δ (pmul (RelatorTerm.signedPath t) t.δ.reverse)
  rw [erase_pmul D (spanTerm D t ht).δ
    (pmul (RelatorTerm.signedPath (spanTerm D t ht)) (spanTerm D t ht).δ.reverse)]
  rw [erase_pmul D (RelatorTerm.signedPath (spanTerm D t ht)) (spanTerm D t ht).δ.reverse]
  rw [show erase D (spanV D) (spanTerm D t ht).δ = t.δ from
    erase_pathToSpan D t.δ D.mem_visitedList_base
      (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)) (inSpan_delta D ht)]
  rw [erase_signedPath_spanTerm D t ht]
  rw [erase_reverse]
  rw [show erase D (spanV D) (spanTerm D t ht).δ = t.δ from
    erase_pathToSpan D t.δ D.mem_visitedList_base
      (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)) (inSpan_delta D ht)]
  rfl

/-- The list of loops of the transported terms is the list of loops of the original terms. -/
theorem map_eraseVG_loop_spanTerms (D : Datum P v n) (j : Fin n) :
    (spanTerms D j).map (fun t => eraseVG D (spanV D) (RelatorTerm.loop t))
      = (D.terms j).map RelatorTerm.loop := by
  show ((D.terms j).attach.map (fun t => spanTerm D t.1 t.2)).map
      (fun t => eraseVG D (spanV D) (RelatorTerm.loop t)) = _
  rw [List.map_map]
  rw [show (D.terms j).attach.map
        ((fun t => eraseVG D (spanV D) (RelatorTerm.loop t)) ∘ fun t => spanTerm D t.1 t.2)
      = (D.terms j).attach.map
        (fun t => eraseVG D (spanV D) (RelatorTerm.loop (spanTerm D t.1 t.2))) from rfl]
  rw [show (D.terms j).attach.map
        (fun t => eraseVG D (spanV D) (RelatorTerm.loop (spanTerm D t.1 t.2)))
      = (D.terms j).attach.map (fun t => RelatorTerm.loop t.1) from
    List.map_congr_left (fun t _ => eraseVG_loop_spanTerm D t.1 t.2)]
  exact List.attach_map_val

/-- The transported datum. -/
noncomputable def spanDatum (D : Datum P v n) : Datum (spanPresentation D) (spanV D) n where
  γ := spanGamma D
  W := D.W
  terms := spanTerms D
  heq := fun j => by
    have hL : eraseVG D (spanV D) (FreeGroup.lift (spanGamma D) (D.W j))
        = FreeGroup.lift D.γ (D.W j) :=
      FreeGroup.lift_unique
        ((eraseVG D (spanV D)).comp (FreeGroup.lift (spanGamma D)))
        (fun a => by
          show eraseVG D (spanV D) (FreeGroup.lift (spanGamma D) (FreeGroup.of a)) = D.γ a
          rw [FreeGroup.lift_apply_of]
          exact eraseVG_spanGamma D a)
        (x := D.W j)
    refine eraseVG_injective D (spanV D) ?_
    rw [hL, D.heq j, map_list_prod, List.map_map]
    exact congrArg List.prod (map_eraseVG_loop_spanTerms D j).symm

/-! ## The transported datum uses every arrow of the span -/

/-- The arrow list of a transported generator projects to the arrow list of the original. -/
theorem map_proj_spanGamma (D : Datum P v n) (j : Fin n) :
    ((spanGamma D j).1.arrowList).map (totalProj D) = (D.γ j).1.arrowList :=
  pathToSpan_arrowList D (D.γ j).1 D.mem_visitedList_base D.mem_visitedList_base
    (inSpan_gamma D j)

/-- The arrow list of the span path of a relator projects to the arrow list of the relator. -/
theorem map_proj_spanPath (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    ((spanPath D i).arrowList).map (totalProj D) = (P.path i.1).arrowList :=
  pathToSpan_arrowList D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
    (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)

/-- The arrow list of the `δ` of a transported term projects to that of the original term. -/
theorem map_proj_spanTerm_delta (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    ((spanTerm D t ht).δ.arrowList).map (totalProj D) = t.δ.arrowList :=
  pathToSpan_arrowList D t.δ D.mem_visitedList_base
    (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)) (inSpan_delta D ht)

/-- The arrow list of the relator path of a transported term projects to that of the original. -/
theorem map_proj_spanTerm_path (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    (((spanPresentation D).path (spanTerm D t ht).i).arrowList).map (totalProj D)
      = (P.path t.i).arrowList := by
  rw [show (spanPresentation D).path (spanTerm D t ht).i = spanPath D (spanTerm D t ht).i from rfl]
  exact map_proj_spanPath D (spanTerm D t ht).i

/-- The arrow list of the paths of a transported term projects to that of the original term. -/
theorem map_proj_spanTerm (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    ((spanTerm D t ht).δ.arrowList
        ++ ((spanPresentation D).path (spanTerm D t ht).i).arrowList).map (totalProj D)
      = t.δ.arrowList ++ (P.path t.i).arrowList := by
  rw [List.map_append, map_proj_spanTerm_delta D t ht, map_proj_spanTerm_path D t ht]

/-- The term part of the raw arrows of the transported datum projects to that of `D`. -/
theorem map_proj_termPart (D : Datum P v n) (j : Fin n) :
    List.map (totalProj D)
        (List.flatMap (fun t => t.δ.arrowList ++ ((spanPresentation D).path t.i).arrowList)
          (spanTerms D j))
      = List.flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList) (D.terms j) := by
  show List.map (totalProj D)
        (List.flatMap (fun t => t.δ.arrowList ++ ((spanPresentation D).path t.i).arrowList)
          ((D.terms j).attach.map (fun t => spanTerm D t.1 t.2)))
      = List.flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList) (D.terms j)
  rw [List.map_flatMap, List.flatMap_map]
  rw [List.flatMap_subtype
    (f := fun t : {t // t ∈ D.terms j} =>
      List.map (totalProj D) ((spanTerm D t.1 t.2).δ.arrowList
        ++ ((spanPresentation D).path (spanTerm D t.1 t.2).i).arrowList))
    (g := fun t : RelatorTerm P v => t.δ.arrowList ++ (P.path t.i).arrowList)
    (hf := fun x h => by rw [map_proj_spanTerm D x h])]
  rw [List.unattach_attach]

/-- The raw arrows of the transported datum project to the raw arrows of `D`. -/
theorem map_proj_rawArrows (D : Datum P v n) :
    (spanDatum D).rawArrows.map (totalProj D) = D.rawArrows := by
  show (List.flatMap (fun j => (spanGamma D j).1.arrowList) (List.finRange n) ++
    List.flatMap (fun j => List.flatMap
      (fun t => t.δ.arrowList ++ ((spanPresentation D).path t.i).arrowList) (spanTerms D j))
      (List.finRange n)).map (totalProj D)
    = (List.flatMap (fun j => (D.γ j).1.arrowList) (List.finRange n) ++
    List.flatMap (fun j => List.flatMap
      (fun t => t.δ.arrowList ++ (P.path t.i).arrowList) (D.terms j)) (List.finRange n))
  rw [List.map_append, List.map_flatMap, List.map_flatMap]
  congr 1
  · exact List.flatMap_congr (fun j _ => map_proj_spanGamma D j)
  · exact List.flatMap_congr (fun j _ => map_proj_termPart D j)

/-- The projection of the reversal of a total arrow is the reversal of the projection. -/
theorem map_proj_totalReverse (D : Datum P v n) (f : Quiver.Total (SpanVertex D)) :
    totalProj D (Quiver.totalReverse f) = Quiver.totalReverse (totalProj D f) := rfl

/-- The used arrows of the transported datum project onto the used arrows of `D`. -/
theorem map_proj_usedArrowsList (D : Datum P v n) :
    (spanDatum D).usedArrowsList.map (totalProj D) = D.usedArrowsList := by
  show ((spanDatum D).rawArrows ++ (spanDatum D).rawArrows.map Quiver.totalReverse).map
      (totalProj D)
    = (D.rawArrows ++ D.rawArrows.map Quiver.totalReverse)
  rw [List.map_append, List.map_map, map_proj_rawArrows]
  rw [show (totalProj D) ∘ (Quiver.totalReverse) = (Quiver.totalReverse) ∘ (totalProj D) from
    funext (map_proj_totalReverse D)]
  rw [← List.map_map, map_proj_rawArrows]

/-- The transported datum uses every arrow of the span. -/
theorem mem_usedArrowsList_spanDatum (D : Datum P v n) (e : Quiver.Total (SpanVertex D)) :
    e ∈ (spanDatum D).usedArrowsList := by
  have he : e.hom.1 ∈ (spanDatum D).usedArrowsList.map (totalProj D) := by
    rw [map_proj_usedArrowsList]
    exact e.hom.2.2.2
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  rw [spanTotal_ext hfe] at hf
  exact hf

/-- The transported datum uses every relator of the span. -/
theorem usedRelator_spanDatum (D : Datum P v n) (i : (spanPresentation D).ι) :
    UsedRelator (spanDatum D) i := by
  obtain ⟨j, t, ht, hi⟩ := i.2
  refine ⟨j, spanTerm D t ht, ?_, ?_⟩
  · show spanTerm D t ht ∈ (D.terms j).attach.map (fun t => spanTerm D t.1 t.2)
    exact List.mem_map.mpr ⟨⟨t, ht⟩, List.mem_attach (D.terms j) ⟨t, ht⟩, rfl⟩
  · exact Subtype.ext hi

/-! ## The erasure maps the relator normal closure of the span into that of `P` -/

/-- Erasure carries the relator normal closure of the span into the relator normal closure of
`P`. -/
theorem map_eraseVG_relatorNormalClosure (D : Datum P v n) :
    (spanPresentation D).relatorNormalClosure (spanV D)
      ≤ Subgroup.comap (eraseVG D (spanV D)) (P.relatorNormalClosure v) := by
  show Subgroup.normalClosure ((spanPresentation D).relatorSet (spanV D))
      ≤ Subgroup.comap (eraseVG D (spanV D)) (P.relatorNormalClosure v)
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨i, δ, hδ, rfl⟩
  show eraseVG D (spanV D)
      (⟨pmul δ (pmul ((spanPresentation D).path i) δ.reverse), pmul_isReduced _ _⟩ :
        VertexGroup (spanV D)) ∈ P.relatorNormalClosure v
  have hx : eraseVG D (spanV D)
        (⟨pmul δ (pmul ((spanPresentation D).path i) δ.reverse), pmul_isReduced _ _⟩ :
          VertexGroup (spanV D))
      = (⟨pmul (erase D (spanV D) δ) (pmul (P.path i.1) (erase D (spanV D) δ).reverse),
          pmul_isReduced _ _⟩ : VertexGroup v) := by
    apply Subtype.ext
    show erase D (spanV D) (pmul δ (pmul ((spanPresentation D).path i) δ.reverse))
        = pmul (erase D (spanV D) δ) (pmul (P.path i.1) (erase D (spanV D) δ).reverse)
    rw [erase_pmul D δ (pmul ((spanPresentation D).path i) δ.reverse),
      erase_pmul D ((spanPresentation D).path i) δ.reverse]
    rw [show erase D ((spanPresentation D).base i) ((spanPresentation D).path i) = P.path i.1 from
      erase_spanPath D (show {i : P.ι // UsedRelator D i} from i)]
    rw [erase_reverse]
    rfl
  rw [hx]
  exact Subgroup.subset_normalClosure
    ⟨i.1, erase D (spanV D) δ, isReduced_erase D δ hδ, rfl⟩

/-! ## The target -/

theorem exists_spanDatum {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) :
    ∃ D₀ : Work.ORLocInd.Howie.Datum (Work.ORLocInd.Howie.spanPresentation D)
        (⟨v, D.mem_visitedList_base⟩ : Work.ORLocInd.Howie.SpanVertex D) n,
      D₀.W = D.W ∧
      (∀ e : Quiver.Total (Work.ORLocInd.Howie.SpanVertex D), e ∈ D₀.usedArrowsList) ∧
      (∀ i : (Work.ORLocInd.Howie.spanPresentation D).ι,
          Work.ORLocInd.Howie.UsedRelator D₀ i) ∧
      ((∀ j, D₀.γ j ∈ (Work.ORLocInd.Howie.spanPresentation D).relatorNormalClosure
          ⟨v, D.mem_visitedList_base⟩) →
        ∀ j, D.γ j ∈ P.relatorNormalClosure v) := by
  refine ⟨spanDatum D, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact mem_usedArrowsList_spanDatum D
  · exact usedRelator_spanDatum D
  · intro h j
    have h1 : eraseVG D (spanV D) ((spanDatum D).γ j) ∈ P.relatorNormalClosure v :=
      map_eraseVG_relatorNormalClosure D (h j)
    rw [show (spanDatum D).γ j = spanGamma D j from rfl] at h1
    rw [eraseVG_spanGamma D j] at h1
    exact h1

end Work.ORLocInd.Howie
