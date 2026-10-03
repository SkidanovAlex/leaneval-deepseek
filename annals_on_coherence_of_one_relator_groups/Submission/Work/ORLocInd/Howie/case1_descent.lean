/-
# Howie's Case 1: the cyclic-cover descent

This file implements Howie's Case 1 of the proof of Theorem 3.1 (the *indicable* case): given a
datum `D` in a staggered presentation `P` whose vertex group at `v` admits a surjection
`φ : P.vertexGroup v ↠ ℤ`, one passes to the cyclic cover `Γ̃` of `Γ` along the labelling induced by
`φ` (`exists_labelling_vanishOnRelators`), lifts the datum to the cover
(`coverDatum`), and takes the span of the lifted datum (`exists_spanDatum`).  The result is a datum
in a presentation whose graph is a subgraph of the cyclic cover, and the measure
`D.measure = 2 * D.L + 2 - D.M` strictly decreases.

## The lift of the datum

The generators `D.γ j`, of level `0`, lift to closed paths of the cover at `⟨v, 0⟩` (`liftHom`); the
terms lift with their base level recorded in the relator index (`coverTerm`).  The key point of the
construction of the `heq` field of `coverDatum` is that the projection `coverProjPath` of the cover
onto `Γ` induces a *monoid homomorphism* `projHom : VertexGroup ⟨x, n⟩ →* VertexGroup x` which is
**injective** (`coverProjPath_injective`), so that an identity of lifted loops can be checked after
projecting it to `Γ`.  This avoids having to prove that `liftHom` is a homomorphism: it is used only
through the projection identity `projHom (liftHom x) = x`.

The measure increase `D.M < D̃.M` is Howie's argument: a reduced loop `β` at `v` of level `1`
(`exists_loop_pathSum_one`) is walked from `(v,0)`, using `hpair` to find a lift of each of its
arrows among the arrows of `D̃`; injectivity of the projection shows that the walk stays at level
`k + pathSum` of the prefix, so `(v,1)` is a visited vertex of `D̃` distinct from `(v,0)`.

## Main definitions

* `levelZero L v` — the subgroup of `F(Γ)_v` of loops of level `0`;
* `liftHom L v` — the lift of such a loop to a closed path of the cover at `⟨v,0⟩`;
* `projHom L v n` — the projection `VertexGroup ⟨v,n⟩ →* VertexGroup v`;
* `coverTerm`, `coverDatum` — the datum of the cover.
-/
import Mathlib
import Submission.Work.Case1.smallModel
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Datum
import Submission.Work.ORLocInd.Howie.exists_labelling
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_conj
import Submission.Work.ORLocInd.Howie.loop_flip
import Submission.Work.ORLocInd.Howie.exists_spanDatum
import Submission.Work.ORLocInd.Howie.liftPath_pmul
import Submission.Work.ORLocInd.Howie.liftPath_length
import Submission.Work.ORLocInd.Howie.PathSumHom
import Submission.Work.ORLocInd.Howie.M_le_L_add_one
import Submission.Work.ORLocInd.Howie.mem_visitedList_of_mem_usedArrowsList
import Submission.Work.ORLocInd.Howie.exists_loop_pathSum_one
import Submission.Work.ORLocInd.Howie.coverProjPath_red
import Submission.Work.ORLocInd.Howie.coverProjPath_isReduced
import Submission.Work.ORLocInd.Howie.coverProjPath_liftPath
import Submission.Work.ORLocInd.Howie.coverProjPath_injective
import Submission.Work.ORLocInd.Howie.coverPresentation
import Submission.Work.ORLocInd.Howie.coverPath_properties
import Submission.Work.ORLocInd.Howie.coverLiftArrow_reverse
import Submission.Work.ORLocInd.Howie.span_reachable
import Submission.Work.ORLocInd.Howie.finite_of_fg_of_no_surjective_int
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.PresentedGroup

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.Howie

open _root_.Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

instance instDecidableEqCoverVertex (L : Labelling V) [DecidableEq V] :
    DecidableEq (CoverVertex L) :=
  fun x y => decidable_of_iff (x.vert = y.vert ∧ x.level = y.level)
    ⟨fun h => CoverVertex.ext h.1 h.2,
      fun h => ⟨congrArg CoverVertex.vert h, congrArg CoverVertex.level h⟩⟩

/-! ## The relators of the cover presentation, indexed by `(i, n)`

These two `rfl` lemmas are the workaround for the fact that `CoverRelator P = Lex (P.ι × ℤ)` (a
`def` unfolding to a type synonym whose `toLex`/`ofLex` are the identity), which makes `rw` fail to
match `(coverPresentation P L hrel τ hτ).path (toLex (i, n))` syntactically. -/

@[simp] theorem coverPresentation_path_apply (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    (i : P.ι) (n : ℤ) :
    (coverPresentation P L hrel τ hτ).path (toLex (i, n)) = coverPath P L hrel i n := rfl

@[simp] theorem coverPresentation_base_apply (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    (i : P.ι) (n : ℤ) :
    (coverPresentation P L hrel τ hτ).base (toLex (i, n)) = (⟨P.base i, n⟩ : CoverVertex L) := rfl

/-- The length of a lifted relator is the length of the relator. -/
theorem coverPath_length (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    (coverPath P L hrel i n).length = (P.path i).length := by
  rw [coverPath]
  exact (path_length_cast rfl _ (liftPath L (P.path i) n)).trans
    (liftPath_length L (P.path i) n)

/-! ## Casting the free-groupoid product along endpoint equalities -/

/-- Casting the two factors of a product of paths along endpoint equalities. -/
theorem pmul_cast {a b c a' b' c' : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (hu : a = a') (hv : b = b') (hw : c = c') :
    pmul (p.cast hu hv) (q.cast hv hw) = (pmul p q).cast hu hw := by
  rw [pmul, pmul, Quiver.Path.cast_comp' p q hu hv hw, red_cast']

/-! ## The projection of paths of the cover -/

/-- The projection of the cover commutes with the free-groupoid product. -/
theorem coverProjPath_pmul (L : Labelling V) (p : CoverVertex L) {q r : CoverVertex L}
    (P : Quiver.Path p q) (Q : Quiver.Path q r) :
    coverProjPath L p (pmul P Q) = pmul (coverProjPath L p P) (coverProjPath L q Q) := by
  rw [pmul, pmul, coverProjPath_red, coverProjPath_comp]

/-- The projection of the cover commutes with reversal of paths. -/
theorem coverProjPath_reverse (L : Labelling V) {p q : CoverVertex L} (P : Quiver.Path p q) :
    coverProjPath L q P.reverse = (coverProjPath L p P).reverse := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      show coverProjPath L _ ((Quiver.reverse e).toPath.comp P.reverse)
        = ((coverProjPath L p P).cons (coverProjArrow e)).reverse
      rw [coverProjPath_comp, ih, coverProjPath_toPath, coverProjArrow_reverse]
      rfl

/-! ## The subgroup of loops of level `0`, and the lift -/

/-- The subgroup of the vertex group `F(Γ)_v` consisting of the reduced closed paths of level `0`
with respect to a labelling `L`. -/
noncomputable def levelZero (L : Labelling V) (v : V) : Subgroup (VertexGroup v) where
  carrier := {x | pathSum L.toFun x.1 = 0}
  mul_mem' := by
    intro x y hx hy
    show pathSum L.toFun (x * y).1 = 0
    rw [VertexGroup.coe_mul, pathSum_pmul L.toFun L.isBalanced, hx, hy, zero_add]
  one_mem' := by
    show pathSum L.toFun (1 : VertexGroup v).1 = 0
    rw [VertexGroup.coe_one, pathSum_nil]
  inv_mem' := by
    intro x hx
    show pathSum L.toFun (x⁻¹).1 = 0
    rw [VertexGroup.coe_inv, pathSum_reverse L.toFun L.isBalanced, hx, neg_zero]

@[simp] theorem mem_levelZero {L : Labelling V} {v : V} {x : VertexGroup v} :
    x ∈ levelZero L v ↔ pathSum L.toFun x.1 = 0 := Iff.rfl

/-- The endpoint equality of the lifted loop of an element of `levelZero`. -/
theorem levelZero_target {L : Labelling V} {v : V} (x : levelZero L v) :
    (⟨v, 0 + pathSum L.toFun x.1.1⟩ : CoverVertex L) = ⟨v, 0⟩ :=
  CoverVertex.ext rfl (by rw [x.2, zero_add])

/-- The lift of a loop of level `0` at `v` to a closed path of the cyclic cover at `⟨v,0⟩`. -/
noncomputable def liftHom (L : Labelling V) (v : V) (x : levelZero L v) :
    VertexGroup (⟨v, 0⟩ : CoverVertex L) :=
  ⟨(liftPath L x.1.1 0).cast rfl (levelZero_target x),
    (isReduced_cast rfl _ _).mpr (liftPath_isReduced L x.1.1 x.1.2 0)⟩

/-! ## The projection of the vertex groups of the cover -/

/-- The projection of the vertex group of the cover at `⟨v,n⟩` onto the vertex group of `Γ` at `v`,
induced by `coverProjPath`. -/
noncomputable def projHom (L : Labelling V) (v : V) (n : ℤ) :
    VertexGroup (⟨v, n⟩ : CoverVertex L) →* VertexGroup v where
  toFun x := ⟨coverProjPath L ⟨v, n⟩ x.1, coverProjPath_isReduced L x.1 x.2⟩
  map_one' := Subtype.ext (by
    show coverProjPath L (⟨v, n⟩ : CoverVertex L)
      (Quiver.Path.nil : Quiver.Path (⟨v, n⟩ : CoverVertex L) (⟨v, n⟩ : CoverVertex L)) =
        Quiver.Path.nil
    rw [coverProjPath_nil])
  map_mul' x y := Subtype.ext (by
    show coverProjPath L ⟨v, n⟩ (pmul x.1 y.1)
      = pmul (coverProjPath L ⟨v, n⟩ x.1) (coverProjPath L ⟨v, n⟩ y.1)
    exact coverProjPath_pmul L ⟨v, n⟩ x.1 y.1)

@[simp] theorem projHom_coe (L : Labelling V) (v : V) (n : ℤ)
    (x : VertexGroup (⟨v, n⟩ : CoverVertex L)) :
    (projHom L v n x).1 = coverProjPath L ⟨v, n⟩ x.1 := rfl

/-- **The projection of the vertex group of the cover is injective.** -/
theorem projHom_injective (L : Labelling V) (v : V) (n : ℤ) :
    Function.Injective (projHom L v n) := by
  intro x y h
  apply Subtype.ext
  exact coverProjPath_injective L ⟨v, n⟩ ⟨v, n⟩ x.1 y.1 (congrArg Subtype.val h)

/-- The projection of the lift of a loop of level `0` is the loop itself. -/
theorem projHom_liftHom (L : Labelling V) (v : V) (x : levelZero L v) :
    projHom L v 0 (liftHom L v x) = x.1 := by
  apply Subtype.ext
  show coverProjPath L ⟨v, 0⟩ ((liftPath L x.1.1 0).cast rfl (levelZero_target x)) = x.1.1
  rw [coverProjPath_cast_right, coverProjPath_liftPath]
  exact path_cast_self _ _ _

/-! ## The lift of a term of the datum -/

/-- The lift of a term `t = (i, sign, δ)` of a datum to the cyclic cover: the relator index records
the level `pathSum L t.δ` at which the lift of `δ` arrives, and `δ` itself lifts to the level-`0`
lift of `δ`. -/
noncomputable def coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    RelatorTerm (coverPresentation P L hrel τ hτ) (⟨v, 0⟩ : CoverVertex L) where
  i := toLex (t.i, pathSum L.toFun t.δ)
  sign := t.sign
  δ := (liftPath L t.δ 0).cast rfl
    (coverVertex_level_eq L (zero_add (pathSum L.toFun t.δ)))
  reduced := (isReduced_cast rfl _ _).mpr (liftPath_isReduced L t.δ t.reduced 0)

@[simp] theorem coverTerm_i (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (coverTerm P L hrel τ hτ t).i = toLex (t.i, pathSum L.toFun t.δ) := rfl

@[simp] theorem coverTerm_sign (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (coverTerm P L hrel τ hτ t).sign = t.sign := rfl

@[simp] theorem coverPresentation_path_coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i =
      coverPath P L hrel t.i (pathSum L.toFun t.δ) := rfl

@[simp] theorem coverPresentation_base_coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (coverPresentation P L hrel τ hτ).base (coverTerm P L hrel τ hτ t).i =
      (⟨P.base t.i, pathSum L.toFun t.δ⟩ : CoverVertex L) := rfl

/-- The length of the relator path of a lifted term. -/
theorem coverPresentation_path_length_coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    ((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).length =
      (P.path t.i).length :=
  coverPath_length P L hrel t.i (pathSum L.toFun t.δ)

/-- The arrow list of the relator path of a lifted term, projected to the base graph. -/
theorem coverPresentation_path_arrowList_coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).arrowList.map
      (fun f => f.hom.1)) = (P.path t.i).arrowList :=
  coverPath_arrowList P L hrel t.i (pathSum L.toFun t.δ)

/-- The projection of the loop of a lifted term is the loop of the term: the loop
`δ̃ · (signed relator) · δ̃⁻¹` of the lifted term projects to `δ · (signed relator) · δ⁻¹`. -/
theorem coverTerm_loop_proj (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    projHom L v 0 (RelatorTerm.loop (coverTerm P L hrel τ hτ t)) = RelatorTerm.loop t := by
  have hδ : coverProjPath L (⟨v, 0⟩ : CoverVertex L) (coverTerm P L hrel τ hτ t).δ = t.δ := by
    show coverProjPath L (⟨v, 0⟩ : CoverVertex L)
      ((liftPath L t.δ 0).cast rfl
        (coverVertex_level_eq L (zero_add (pathSum L.toFun t.δ)))) = t.δ
    rw [coverProjPath_cast_right, coverProjPath_liftPath]
    exact path_cast_self _ _ _
  have hδr : coverProjPath L ((coverPresentation P L hrel τ hτ).base
        (coverTerm P L hrel τ hτ t).i) (coverTerm P L hrel τ hτ t).δ.reverse = t.δ.reverse := by
    rw [coverProjPath_reverse, hδ]
    rfl
  have hs : coverProjPath L ((coverPresentation P L hrel τ hτ).base
        (coverTerm P L hrel τ hτ t).i)
      (RelatorTerm.signedPath (coverTerm P L hrel τ hτ t)) = RelatorTerm.signedPath t := by
    unfold RelatorTerm.signedPath
    change coverProjPath L ((coverPresentation P L hrel τ hτ).base
        (coverTerm P L hrel τ hτ t).i)
      (if (t.sign = true) then
        ((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).reverse
        else (coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i)
      = if (t.sign = true) then (P.path t.i).reverse else P.path t.i
    by_cases h : t.sign = true
    · rw [if_pos h, if_pos h, coverProjPath_reverse]
      show (coverProjPath L (⟨P.base t.i, pathSum L.toFun t.δ⟩ : CoverVertex L)
        (coverPath P L hrel t.i (pathSum L.toFun t.δ))).reverse = (P.path t.i).reverse
      rw [coverProjPath_coverPath]
    · rw [if_neg h, if_neg h]
      show coverProjPath L (⟨P.base t.i, pathSum L.toFun t.δ⟩ : CoverVertex L)
        (coverPath P L hrel t.i (pathSum L.toFun t.δ)) = P.path t.i
      exact coverProjPath_coverPath P L hrel t.i (pathSum L.toFun t.δ)
  apply Subtype.ext
  show coverProjPath L (⟨v, 0⟩ : CoverVertex L)
      (pmul (coverTerm P L hrel τ hτ t).δ
        (pmul (RelatorTerm.signedPath (coverTerm P L hrel τ hτ t))
          (coverTerm P L hrel τ hτ t).δ.reverse)) =
    pmul t.δ (pmul (RelatorTerm.signedPath t) t.δ.reverse)
  rw [coverProjPath_pmul, coverProjPath_pmul, hδ, hs, hδr]
  rfl

/-! ## The lifted datum -/

/-- The transfer of vanishing through the span (`exists_spanDatum`), stated for the explicit
`spanDatum` rather than for the datum returned by the existential. -/
theorem spanDatum_transfer [DecidableEq V] {P : Presentation V} {v : V} {n : ℕ} (D : Datum P v n) :
    (∀ j, (spanDatum D).γ j ∈ (spanPresentation D).relatorNormalClosure (spanV D)) →
      ∀ j, D.γ j ∈ P.relatorNormalClosure v := by
  intro h j
  have h1 : eraseVG D (spanV D) ((spanDatum D).γ j) ∈ P.relatorNormalClosure v :=
    map_eraseVG_relatorNormalClosure D (h j)
  rwa [show (spanDatum D).γ j = spanGamma D j from rfl, eraseVG_spanGamma D j] at h1

/-- **The lift of a datum to the cyclic cover.**  The generators lift along the labelling (their
levels are `0` by hypothesis); the words are unchanged; the terms lift with `coverTerm`. -/
noncomputable def coverDatum (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0) :
    Datum (coverPresentation P L hrel τ hτ) (⟨v, 0⟩ : CoverVertex L) n where
  γ := fun j => liftHom L v ⟨D.γ j, hγ j⟩
  W := D.W
  terms := fun j => (D.terms j).map (coverTerm P L hrel τ hτ)
  heq := fun j => by
    apply projHom_injective L v 0
    have h1 : projHom L v 0 (FreeGroup.lift (fun i => liftHom L v ⟨D.γ i, hγ i⟩) (D.W j))
        = FreeGroup.lift D.γ (D.W j) := by
      have h := FreeGroup.lift_unique
        (f := fun i => D.γ i)
        (g := (projHom L v 0).comp
          (FreeGroup.lift (fun i => liftHom L v ⟨D.γ i, hγ i⟩)))
        (fun i => by
          show projHom L v 0 (FreeGroup.lift (fun i => liftHom L v ⟨D.γ i, hγ i⟩)
            (FreeGroup.of i)) = D.γ i
          rw [FreeGroup.lift_apply_of]
          exact projHom_liftHom L v ⟨D.γ i, hγ i⟩) (x := D.W j)
      simpa using h
    have h2 : projHom L v 0
          ((((D.terms j).map (coverTerm P L hrel τ hτ)).map RelatorTerm.loop).prod)
        = ((D.terms j).map RelatorTerm.loop).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun t _ => ?_)
      exact coverTerm_loop_proj P L hrel τ hτ t
    rw [h1, h2, D.heq j]

/-! ## Auxiliary facts about the lifted paths -/

theorem vertices_cast_vert (L : Labelling V) {a a' b b' : CoverVertex L} (hu : a = a')
    (hv : b = b') (p : Quiver.Path a b) :
    ((p.cast hu hv).vertices).map CoverVertex.vert = p.vertices.map CoverVertex.vert := by
  cases hu; cases hv; rw [Quiver.Path.cast_rfl_rfl]

theorem liftPath_vertices_vert (L : Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    (liftPath L p n).vertices.map CoverVertex.vert = p.vertices := by
  induction p with
  | nil =>
      rw [liftPath_nil_cast', vertices_cast_vert]
      rfl
  | cons p e ih =>
      simp only [liftPath_cons_cast', vertices_cast_vert, Quiver.Path.vertices_cons,
        List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
      rw [ih]

theorem coverPath_vertices_map_vert (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    ((coverPath P L hrel i n).vertices).map CoverVertex.vert = (P.path i).vertices := by
  rw [coverPath]
  exact (vertices_cast_vert L rfl _ (liftPath L (P.path i) n)).trans
    (liftPath_vertices_vert L (P.path i) n)

theorem coverPresentation_path_vertices_coverTerm (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} (t : RelatorTerm P v) :
    (((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).vertices).map
      CoverVertex.vert = (P.path t.i).vertices :=
  coverPath_vertices_map_vert P L hrel t.i (pathSum L.toFun t.δ)

/-! ## The list facts for the lifted datum -/

theorem coverDatum_visitedList_map [DecidableEq V] (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0) :
    (coverDatum P L hrel τ hτ D hγ).visitedList.map CoverVertex.vert = D.visitedList := by
  have hgamma : ∀ j, (((coverDatum P L hrel τ hτ D hγ).γ j).1).vertices.map CoverVertex.vert =
      ((D.γ j).1).vertices := by
    intro j
    show (((liftPath L (D.γ j).1 0).cast rfl
      (levelZero_target ⟨D.γ j, hγ j⟩)).vertices).map CoverVertex.vert = ((D.γ j).1).vertices
    rw [vertices_cast_vert, liftPath_vertices_vert]
  have hterm : ∀ (t : RelatorTerm P v),
      (RelatorTerm.visitedList (coverTerm P L hrel τ hτ t)).map CoverVertex.vert =
        RelatorTerm.visitedList t := by
    intro t
    unfold RelatorTerm.visitedList
    rw [List.map_append]
    congr 1
    · show (((liftPath L t.δ 0).cast rfl
        (coverVertex_level_eq L (zero_add (pathSum L.toFun t.δ)))).vertices).map
          CoverVertex.vert = t.δ.vertices
      rw [vertices_cast_vert, liftPath_vertices_vert]
    · exact coverPresentation_path_vertices_coverTerm P L hrel τ hτ t
  have h1 : ((List.finRange n).flatMap
        (fun j => ((coverDatum P L hrel τ hτ D hγ).γ j).1.vertices)).map CoverVertex.vert =
      (List.finRange n).flatMap (fun j => ((D.γ j).1).vertices) := by
    rw [List.map_flatMap]
    exact List.flatMap_congr (fun j _ => hgamma j)
  have h2 : ((List.finRange n).flatMap
        (fun j => ((coverDatum P L hrel τ hτ D hγ).terms j).flatMap RelatorTerm.visitedList)).map
          CoverVertex.vert =
      (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList) := by
    rw [List.map_flatMap]
    refine List.flatMap_congr (fun j _ => ?_)
    show (((D.terms j).map (coverTerm P L hrel τ hτ)).flatMap RelatorTerm.visitedList).map
        CoverVertex.vert = (D.terms j).flatMap RelatorTerm.visitedList
    rw [List.map_flatMap, List.flatMap_map]
    exact List.flatMap_congr (fun t _ => hterm t)
  unfold Datum.visitedList
  rw [List.map_append, List.map_append, List.map_cons, List.map_nil, h1, h2]

theorem coverDatum_rawArrows_map [DecidableEq V] (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0) :
    (coverDatum P L hrel τ hτ D hγ).rawArrows.map (coverProjTotal L) = D.rawArrows := by
  have hgamma : ∀ j, (((coverDatum P L hrel τ hτ D hγ).γ j).1).arrowList.map (coverProjTotal L) =
      ((D.γ j).1).arrowList := by
    intro j
    show (((liftPath L (D.γ j).1 0).cast rfl
      (levelZero_target ⟨D.γ j, hγ j⟩)).arrowList).map (coverProjTotal L) = ((D.γ j).1).arrowList
    rw [Quiver.Path.arrowList_cast_map]
    exact liftPath_arrowList L (D.γ j).1 0
  have htermδ : ∀ (t : RelatorTerm P v),
      ((coverTerm P L hrel τ hτ t).δ.arrowList).map (coverProjTotal L) = t.δ.arrowList := by
    intro t
    show (((liftPath L t.δ 0).cast rfl
      (coverVertex_level_eq L (zero_add (pathSum L.toFun t.δ)))).arrowList).map
        (coverProjTotal L) = t.δ.arrowList
    rw [Quiver.Path.arrowList_cast_map]
    exact liftPath_arrowList L t.δ 0
  have h1 : ((List.finRange n).flatMap
        (fun j => ((coverDatum P L hrel τ hτ D hγ).γ j).1.arrowList)).map (coverProjTotal L) =
      (List.finRange n).flatMap (fun j => ((D.γ j).1).arrowList) := by
    rw [List.map_flatMap]
    exact List.flatMap_congr (fun j _ => hgamma j)
  have h2 : ((List.finRange n).flatMap (fun j =>
        ((coverDatum P L hrel τ hτ D hγ).terms j).flatMap
          (fun t => t.δ.arrowList ++ ((coverPresentation P L hrel τ hτ).path t.i).arrowList))).map
            (coverProjTotal L) =
      (List.finRange n).flatMap (fun j => (D.terms j).flatMap
        (fun t => t.δ.arrowList ++ (P.path t.i).arrowList)) := by
    rw [List.map_flatMap]
    refine List.flatMap_congr (fun j _ => ?_)
    show (((D.terms j).map (coverTerm P L hrel τ hτ)).flatMap
      (fun t => t.δ.arrowList ++ ((coverPresentation P L hrel τ hτ).path t.i).arrowList)).map
        (coverProjTotal L) =
      (D.terms j).flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList)
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr (fun t _ => ?_)
    show List.map (coverProjTotal L) ((coverTerm P L hrel τ hτ t).δ.arrowList ++
      ((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).arrowList) =
      t.δ.arrowList ++ (P.path t.i).arrowList
    rw [List.map_append, htermδ t]
    exact congrArg (fun l => t.δ.arrowList ++ l)
      (coverPresentation_path_arrowList_coverTerm P L hrel τ hτ t)
  unfold Datum.rawArrows
  rw [List.map_append, h1, h2]

theorem coverDatum_usedArrowsList_map [DecidableEq V] (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0) :
    (coverDatum P L hrel τ hτ D hγ).usedArrowsList.map (coverProjTotal L) = D.usedArrowsList := by
  have hraw := coverDatum_rawArrows_map P L hrel τ hτ D hγ
  show (((coverDatum P L hrel τ hτ D hγ).rawArrows ++
      (coverDatum P L hrel τ hτ D hγ).rawArrows.map Quiver.totalReverse).map (coverProjTotal L)) = _
  rw [List.map_append, List.map_map, hraw]
  rw [show (coverProjTotal L) ∘ (Quiver.totalReverse) =
      (Quiver.totalReverse) ∘ (coverProjTotal L) from funext (fun f => rfl)]
  rw [← List.map_map, hraw]
  rfl

/-! ## The measure increase -/

theorem coverDatum_M_gt [DecidableEq V] (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0)
    (hβ : ∃ β : Quiver.Path v v, β.IsReduced ∧ pathSum L.toFun β = 1)
    (hpair : ∀ e : Quiver.Total V, e ∈ Datum.usedArrowsList D) :
    D.M < (coverDatum P L hrel τ hτ D hγ).M := by
  classical
  obtain ⟨β, -, hβsum⟩ := hβ
  have hused := coverDatum_usedArrowsList_map P L hrel τ hτ D hγ
  have hvis := coverDatum_visitedList_map P L hrel τ hτ D hγ
  set S : Finset (CoverVertex L) := (coverDatum P L hrel τ hτ D hγ).visitedList.toFinset with hS
  have hSimg : S.image CoverVertex.vert = D.visitedList.toFinset := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hx' : x ∈ (coverDatum P L hrel τ hτ D hγ).visitedList := by
        rw [hS] at hx; exact List.mem_toFinset.mp hx
      rw [← hvis]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx', hxy⟩)
    · intro hy
      have hy' : y ∈ (coverDatum P L hrel τ hτ D hγ).visitedList.map CoverVertex.vert := by
        rw [hvis]; exact List.mem_toFinset.mp hy
      obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy'
      refine Finset.mem_image.mpr ⟨x, ?_, hxy⟩
      rw [hS]; exact List.mem_toFinset.mpr hx
  have hMc : (coverDatum P L hrel τ hτ D hγ).M = S.card := by
    rw [Datum.M, hS]
    exact (List.card_toFinset _).symm
  have hMD : D.M = D.visitedList.toFinset.card := by
    rw [Datum.M]
    exact (List.card_toFinset _).symm
  have hle : D.M ≤ (coverDatum P L hrel τ hτ D hγ).M := by
    rw [hMD, hMc, ← hSimg]
    exact Finset.card_image_le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcard : (S.image CoverVertex.vert).card = S.card := by rw [hSimg, ← hMD, heq, hMc]
  have hinj : Set.InjOn CoverVertex.vert (↑S : Set (CoverVertex L)) :=
    Finset.card_image_iff.mp hcard
  have hS0 : (⟨v, 0⟩ : CoverVertex L) ∈ S := by
    rw [hS]
    exact List.mem_toFinset.mpr (Datum.mem_visitedList_base _)
  have step : ∀ (e : Quiver.Total V), e ∈ D.usedArrowsList → ∀ u ∈ S, u.vert = e.left →
      ∃ w ∈ S, w.vert = e.right ∧ w.level = u.level + L.toFun e := by
    intro e he u hu huvert
    obtain ⟨g, hgmem, hgeq⟩ := List.mem_map.mp (by rw [hused]; exact he)
    have hge : g.hom.1 = e := hgeq
    have hgl : g.left ∈ S := by
      rw [hS]
      exact List.mem_toFinset.mpr (mem_visitedList_of_mem_usedArrowsList _ hgmem).1
    have hgr : g.right ∈ S := by
      rw [hS]
      exact List.mem_toFinset.mpr (mem_visitedList_of_mem_usedArrowsList _ hgmem).2
    have hgle : g.left = u := by
      refine hinj hgl hu ?_
      rw [huvert, ← hge]
      exact g.hom.2.1.symm
    refine ⟨g.right, hgr, ?_, ?_⟩
    · rw [← hge]; exact g.hom.2.2.1.symm
    · rw [← hgle, ← hge]; exact g.hom.2.2.2
  have walk : ∀ {a b : V} (q : Quiver.Path a b) (u : CoverVertex L), u ∈ S → u.vert = a →
      (∀ e ∈ q.arrowList, e ∈ D.usedArrowsList) →
      ∃ w ∈ S, w.vert = b ∧ w.level = u.level + pathSum L.toFun q := by
    intro a b q
    induction q with
    | nil => intro u hu huv _; exact ⟨u, hu, huv, by rw [pathSum_nil, add_zero]⟩
    | cons q e ih =>
        intro u hu huv hall
        obtain ⟨w, hw, hwv, hwl⟩ := ih u hu huv
          (fun f hf => hall f (by rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hf)))
        obtain ⟨w', hw', hw'v, hw'l⟩ := step (Quiver.Total.mk _ _ e)
          (hall _ (by rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp))))
          w hw hwv
        exact ⟨w', hw', hw'v, by rw [hw'l, hwl, pathSum_cons, add_assoc]⟩
  obtain ⟨w, hw, hwv, hwl⟩ := walk β (⟨v, 0⟩ : CoverVertex L) hS0 rfl (fun e _ => hpair e)
  have hw1 : w = (⟨v, 1⟩ : CoverVertex L) :=
    CoverVertex.ext hwv (by rw [hwl, hβsum, zero_add])
  have hS1 : (⟨v, 1⟩ : CoverVertex L) ∈ S := by rw [← hw1]; exact hw
  have heq2 : (⟨v, 0⟩ : CoverVertex L) = ⟨v, 1⟩ := hinj hS0 hS1 rfl
  exact absurd (congrArg CoverVertex.level heq2) (by norm_num)

/-! ## (inlined from `Submission/Work/Case1/eq_one_of_finite_abelianization.lean`) -/

theorem eq_one_of_finite_abelianization {G : Type u} [Group G]
    (h : Finite (Abelianization G)) (ρ : G →* Multiplicative ℤ) : ∀ g, ρ g = 1 := by
  intro g
  have : Finite (Abelianization G) := h
  -- `ρ` factors through the abelianization, which is finite.
  rw [← Abelianization.lift_apply_of ρ g]
  have hpow : (Abelianization.lift ρ (Abelianization.of g)) ^ orderOf (Abelianization.of g) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hn : orderOf (Abelianization.of g) ≠ 0 :=
    (isOfFinOrder_of_finite (Abelianization.of g)).orderOf_pos.ne'
  exact (pow_eq_one_iff_left (n := orderOf (Abelianization.of g)) hn).mp hpow

/-! ## (inlined from `Submission/Work/Case1/pathSum_gamma_eq_zero.lean`) -/
/-! ## Two prerequisites for the finite-abelianisation argument

The proof of `pathSum_gamma_eq_zero` needs two facts.

* `phi_conjElem`: a homomorphism `φ` from a *presented* vertex group into the abelian group
  `Multiplicative ℤ` is invisible to conjugation:
  `φ (conjElem d x) = φ x` for `x : F(Γ)_v`.  Indeed `conjElem d x = g · x · g⁻¹` for the group
  element `g = red (d v)` of the free vertex group `F(Γ)_v`, and an abelian group forgets
  conjugates.

* `RelatorTerm.loop_mem_relatorNormalClosure`: the loop `δ · r_i^{±1} · δ⁻¹` of a term of a datum
  lies in the normal closure of the relators (after projection to the presented vertex group it is
  `1`).  For the positive sign this is `mem_relatorNormalClosure_conj`; for the negative sign the
  loop is the inverse of the positively-signed loop (`loop_flip`). -/

/-- **Conjugation is invisible in an abelian target.**  For a closed path `y` at `v`, the conjugate
`conjElem d y = d v · y · (d v)⁻¹` — the `d v` here being the group element `red (d v)` of the free
vertex group `F(Γ)_v` — has the same image under `φ ∘ toVertexGroup` as `y` itself. -/
theorem phi_conjElem {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {v : V} (P : Work.ORLocInd.Howie.Presentation V) (d : ∀ x : V, Quiver.Path v x)
    (φ : P.vertexGroup v →* Multiplicative ℤ) (y : Work.ORLocInd.Howie.VertexGroup v) :
    φ (P.toVertexGroup v (Work.ORLocInd.Howie.conjElem d y.1)) =
      φ (P.toVertexGroup v y) := by
  -- `conjElem d y = g · y · g⁻¹` with `g = red (d v)`; `red` enters because `d v` need not be
  -- reduced, while a group element of `F(Γ)_v` is a *reduced* closed path.
  let g : Work.ORLocInd.Howie.VertexGroup v :=
    ⟨Work.ORLocInd.Howie.red (d v), Work.ORLocInd.Howie.isReduced_red _⟩
  have hg : Work.ORLocInd.Howie.conjElem d y.1 = g * y * g⁻¹ := by
    apply Subtype.ext
    show Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (d v) y.1) (d v).reverse =
      Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.red (d v)) y.1)
        (Work.ORLocInd.Howie.red (d v)).reverse
    rw [Work.ORLocInd.Howie.pmul_congr_right (Work.ORLocInd.Howie.pmul (d v) y.1)
      (Quiver.Path.ReducesTo.reverse (Work.ORLocInd.Howie.reducesTo_red (d v)))]
    rw [← Work.ORLocInd.Howie.pmul_red_left (d v) y.1]
  rw [hg]
  -- `φ (g · y · g⁻¹) = φ g · φ y · (φ g)⁻¹ = φ y`, the last step by commutativity of
  -- `Multiplicative ℤ`.
  simp only [map_mul, map_inv]
  rw [mul_assoc, mul_comm (φ (P.toVertexGroup v y)) (φ (P.toVertexGroup v g))⁻¹, ← mul_assoc,
    mul_inv_cancel, one_mul]

/-- **The loop of a term lies in the normal closure of the relators.**  Hence it is killed by the
projection `F(Γ)_v → π₁(⟨Γ | R⟩, v)`.  For the positive sign this is
`mem_relatorNormalClosure_conj` (up to `pmul_assoc`), and the flipped term's loop is the inverse
(`loop_flip`). -/
theorem relatorTerm_loop_mem {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V}
    (t : Work.ORLocInd.Howie.RelatorTerm P v) :
    Work.ORLocInd.Howie.RelatorTerm.loop t ∈ P.relatorNormalClosure v := by
  -- the positively-signed statement, which is a relator conjugate
  have key : ∀ (i : P.ι) (δ : Quiver.Path v (P.base i)) (hδ : δ.IsReduced),
      (⟨i, false, δ, hδ⟩ : Work.ORLocInd.Howie.RelatorTerm P v).loop ∈
        P.relatorNormalClosure v := by
    intro i δ hδ
    have hc := Work.ORLocInd.Howie.mem_relatorNormalClosure_conj P v i δ
    have heq : (⟨i, false, δ, hδ⟩ : Work.ORLocInd.Howie.RelatorTerm P v).loop =
        (⟨Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ (P.path i)) δ.reverse,
          Work.ORLocInd.Howie.pmul_isReduced _ _⟩ : Work.ORLocInd.Howie.VertexGroup v) := by
      apply Subtype.ext
      show Work.ORLocInd.Howie.pmul δ (Work.ORLocInd.Howie.pmul (P.path i) δ.reverse) =
        Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ (P.path i)) δ.reverse
      rw [Work.ORLocInd.Howie.pmul_assoc]
    rw [heq]; exact hc
  obtain ⟨i, sign, δ, hδ⟩ := t
  cases sign
  · exact key i δ hδ
  · have hflip : (⟨i, true, δ, hδ⟩ : Work.ORLocInd.Howie.RelatorTerm P v).loop =
        (⟨i, false, δ, hδ⟩ : Work.ORLocInd.Howie.RelatorTerm P v).loop⁻¹ :=
      Work.ORLocInd.Howie.loop_flip
        (t := (⟨i, false, δ, hδ⟩ : Work.ORLocInd.Howie.RelatorTerm P v))
    rw [hflip]
    exact Subgroup.inv_mem _ (key i δ hδ)

/-- The `γ_j` of a datum with `PresentedGroup (Set.range D.W)` of finite abelianisation lie in
`levelZero L v`: `φ` kills them.  Proof: the hom
`ρ := FreeGroup.lift (fun i => φ (P.toVertexGroup v (conjElem d (D.γ i)))) : FreeGroup (Fin n) →* M ℤ`
kills each `W j` (use `D.heq`, that loops are relator conjugates, and that `φ` is invisible to
conjugation because `Multiplicative ℤ` is abelian), hence factors through
`PresentedGroup (Set.range D.W)`, and a hom from a group with finite abelianisation to `Multiplicative
ℤ` is trivial; `hpath` identifies `pathSum L (D.γ j).1` with `ρ (FreeGroup.of j)`. -/
theorem pathSum_gamma_eq_zero {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (v : V) {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    (L : Work.ORLocInd.Howie.Labelling V) (d : ∀ x : V, Quiver.Path v x)
    (φ : P.vertexGroup v →* Multiplicative ℤ)
    (hpath : ∀ (x : V) (p : Quiver.Path x x),
      Work.ORLocInd.Howie.pathSum L.toFun p =
        Multiplicative.toAdd (φ (P.toVertexGroup v (Work.ORLocInd.Howie.conjElem d p))))
    (hfin : Finite (Abelianization (PresentedGroup (Set.range D.W)))) :
    ∀ j, Work.ORLocInd.Howie.pathSum L.toFun (D.γ j).1 = 0 := by
  classical
  -- The hom `ρ : FreeGroup (Fin n) →* Multiplicative ℤ` which sends the generator `i` to the
  -- `φ`-value of the conjugate of `γ_i`.
  let f : Fin n → Multiplicative ℤ :=
    fun i => φ (P.toVertexGroup v (Work.ORLocInd.Howie.conjElem d (D.γ i).1))
  -- The hom `Ψ` obtained by evaluating `W_j` at the `γ_i` (at the level of `F(Γ)_v`) and applying
  -- `φ ∘ toVertexGroup`.  It agrees with `ρ` on generators by `phi_conjElem`.
  let Ψ : FreeGroup (Fin n) →* Multiplicative ℤ :=
    (φ.comp (P.toVertexGroup v)).comp (FreeGroup.lift D.γ)
  have hgen : ∀ i : Fin n, Ψ (FreeGroup.of i) = f i := by
    intro i
    show (φ.comp (P.toVertexGroup v)) (FreeGroup.lift D.γ (FreeGroup.of i)) = f i
    rw [FreeGroup.lift_apply_of]
    exact (phi_conjElem P d φ (D.γ i)).symm
  -- Hence `ρ` kills each relation `W_j`: by `D.heq` the value `W_j(γ)` is a product of loops of
  -- terms, each of which lies in the normal closure of the relators (`relatorTerm_loop_mem`), and
  -- `φ ∘ toVertexGroup` kills that normal closure.
  have hkill : ∀ r ∈ Set.range D.W, FreeGroup.lift f r = 1 := by
    rintro r ⟨j, rfl⟩
    rw [← FreeGroup.lift_unique (f := f) Ψ hgen (x := D.W j)]
    show φ (P.toVertexGroup v (FreeGroup.lift D.γ (D.W j))) = 1
    rw [D.heq j, map_list_prod, List.map_map, map_list_prod, List.map_map]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    show φ (P.toVertexGroup v (Work.ORLocInd.Howie.RelatorTerm.loop t)) = 1
    have hmem : P.toVertexGroup v (Work.ORLocInd.Howie.RelatorTerm.loop t) = 1 := by
      rw [P.toVertexGroup_apply]
      exact (QuotientGroup.eq_one_iff (Work.ORLocInd.Howie.RelatorTerm.loop t)).mpr
        (relatorTerm_loop_mem t)
    rw [hmem, map_one]
  -- `ρ` therefore factors through `PresentedGroup (Set.range D.W)`, which has finite
  -- abelianisation, so the factored homomorphism is trivial (`eq_one_of_finite_abelianization`).
  let ρ' : PresentedGroup (Set.range D.W) →* Multiplicative ℤ :=
    PresentedGroup.toGroup (f := f) hkill
  have htriv : ∀ g, ρ' g = 1 := eq_one_of_finite_abelianization hfin ρ'
  have hfac : ∀ x : FreeGroup (Fin n),
      ρ' (PresentedGroup.mk (Set.range D.W) x) = FreeGroup.lift f x := by
    intro x
    exact QuotientGroup.lift_mk _ _ x
  intro j
  have hρ1 : FreeGroup.lift f (FreeGroup.of j) = 1 := by
    rw [← hfac (FreeGroup.of j)]
    exact htriv _
  have hφ1 : φ (P.toVertexGroup v (Work.ORLocInd.Howie.conjElem d (D.γ j).1)) = 1 := by
    rw [← hρ1, FreeGroup.lift_apply_of]
  rw [hpath v (D.γ j).1, hφ1]
  rfl

/-! ## (inlined from `Submission/Work/Case1/CodeSeparates_cover.lean`) -/
open Work.ORLocInd.Howie
open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The target of an arrow `e : p → q` of the cyclic cover is determined by its source and its
underlying arrow of `Γ`: `q = (e₁.right, p.level + L e₁)`. -/
theorem coverVertex_eq_mk {L : Labelling V} {p q : CoverVertex L} (e : p ⟶ q) :
    q = (⟨e.1.right, p.level + L.toFun e.1⟩ : CoverVertex L) :=
  CoverVertex.ext e.2.2.1.symm e.2.2.2

/-- A total arrow of the cyclic cover is determined by its source and by its underlying arrow of
`Γ`.  (The target is determined by those two, as `coverVertex_eq_mk` says.) -/
theorem coverTotal_ext {L : Labelling V} {f g : Quiver.Total (CoverVertex L)}
    (h1 : f.left = g.left) (h2 : f.hom.1 = g.hom.1) : f = g := by
  obtain ⟨fl, fr, fh⟩ := f
  obtain ⟨gl, gr, gh⟩ := g
  simp only at h1 h2
  subst h1
  have hr : fr = gr := by
    refine CoverVertex.ext ?_ ?_
    · rw [← fh.2.2.1, h2, gh.2.2.1]
    · rw [fh.2.2.2, gh.2.2.2, h2]
  subst hr
  have : fh = gh := Subtype.ext h2
  subst this
  rfl

/-- **Howie's Case 1, `CodeSeparates`.**  If the edge code of the presentation `P` separates
unoriented edges of `Γ`, then so does the code of the cyclic cover `Γ̃` of the lifted presentation
`coverPresentation P L hrel τ hτ`: the code of an edge of the cover refines the code of the
projected edge lexicographically by the level of its source, which pins down the unique lift of the
edge at that level. -/
theorem CodeSeparates_cover {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {P : Work.ORLocInd.Howie.Presentation V} (hsep : P.CodeSeparates)
    (L : Work.ORLocInd.Howie.Labelling V) (hrel : Work.ORLocInd.Howie.VanishOnRelators L P)
    (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) :
    (Work.ORLocInd.Howie.coverPresentation P L hrel τ hτ).CodeSeparates := by
  intro f g h
  -- split the total arrows of the cover into source, target and arrow of the cover
  obtain ⟨fl, fr, fh⟩ := f
  obtain ⟨gl, gr, gh⟩ := g
  -- the code of the cover is `(code of the projected edge, level of the source + τ)`
  have h' : toLex (P.edgeOf fh.1, fl.level + τ fh.1) =
      toLex (P.edgeOf gh.1, gl.level + τ gh.1) := h
  obtain ⟨hcode, hlev⟩ := Prod.mk.inj (toLex_inj.mp h')
  -- the base code separates unoriented edges
  rcases hsep fh.1 gh.1 hcode with heq | heq
  · -- same underlying arrow: the level equality pins down the source, hence the arrow
    left
    refine coverTotal_ext ?_ heq
    refine CoverVertex.ext ?_ ?_
    · rw [← fh.2.1, heq, gh.2.1]
    · have h2' : fl.level + τ fh.1 = gl.level + τ fh.1 := by rw [hlev, heq]
      exact add_right_cancel h2'
  · -- opposite underlying arrows: `f` is the reverse of `g`
    right
    refine coverTotal_ext (g := Quiver.totalReverse (Quiver.Total.mk gl gr gh)) ?_ ?_
    · refine CoverVertex.ext ?_ ?_
      · show fl.vert = gr.vert
        rw [← fh.2.1, heq, Quiver.totalReverse_left]
        exact gh.2.2.1
      · show fl.level = gr.level
        -- `τ (e⁻¹) = τ e - L e` converts the level equality into `fl.level = gl.level + L gh.1`
        have h2' := hlev
        rw [heq] at h2'
        rw [hτ gh.1] at h2'
        have hgl := cover_hom_level gh
        omega
    · exact heq

/-! ## (inlined from `Submission/Work/Case1/CodeSeparates_span.lean`) -/
open Quiver


/-- The code of an unoriented edge of the span is inherited from `P`, so an arrow of the span and
the ambient arrow underlying it have the same code.  This is `rfl` for the definition of
`spanEdgeOf`. -/
theorem spanEdgeOf_apply {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) (e : Quiver.Total (Work.ORLocInd.Howie.SpanVertex D)) :
    Work.ORLocInd.Howie.spanEdgeOf D e = P.edgeOf e.hom.1 := rfl

/-- Reversing an arrow of the span reverses the ambient arrow underlying it. -/
theorem spanTotal_hom_totalReverse {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (e : Quiver.Total (Work.ORLocInd.Howie.SpanVertex D)) :
    (Quiver.totalReverse e).hom.1 = Quiver.totalReverse e.hom.1 := rfl

/-- **The code of `P` separates the unoriented edges of the sub-presentation spanned by a datum.**

The code of an unoriented edge of the span is inherited from `P` (`spanEdgeOf`), so two arrows of
the span with the same code have underlying arrows of `Γ` with the same code; `hsep` then says that
these underlying arrows are equal, or mutually inverse.  Both of these alternatives transfer back to
the span, because a total arrow of the span is determined by its underlying arrow of `Γ`
(`spanTotal_ext`). -/
theorem CodeSeparates_span {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    (hsep : P.CodeSeparates) : (Work.ORLocInd.Howie.spanPresentation D).CodeSeparates := by
  rw [Work.ORLocInd.Howie.Presentation.CodeSeparates] at hsep ⊢
  intro e f h
  rcases hsep e.hom.1 f.hom.1 h with h1 | h1
  · exact Or.inl (Work.ORLocInd.Howie.spanTotal_ext h1)
  · refine Or.inr (Work.ORLocInd.Howie.spanTotal_ext ?_)
    rw [show (Quiver.totalReverse f).hom.1 = Quiver.totalReverse f.hom.1 from rfl]
    exact h1

/-! ## (inlined from `Submission/Work/Case1/spanDatum_L.lean`) -/
open Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}

/-- The transport of a path of the ambient graph into the span of a datum preserves its length. -/
theorem pathToSpan_length (D : Work.ORLocInd.Howie.Datum P v n) {a b : V} (p : Quiver.Path a b)
    (ha : a ∈ D.visitedList) (hb : b ∈ D.visitedList) (hp : Work.ORLocInd.Howie.InSpan D p) :
    (Work.ORLocInd.Howie.pathToSpan D a ha p hb hp).length = p.length := by
  have h := congrArg List.length
    (Work.ORLocInd.Howie.pathToSpan_arrowList D p ha hb hp)
  rwa [List.length_map, Quiver.Path.arrowList_length_eq, Quiver.Path.arrowList_length_eq] at h

/-- The weight of a transported term is the weight of the term. -/
theorem weight_spanTerm (D : Work.ORLocInd.Howie.Datum P v n) {j : Fin n}
    {t : Work.ORLocInd.Howie.RelatorTerm P v} (ht : t ∈ D.terms j) :
    Work.ORLocInd.Howie.RelatorTerm.weight (Work.ORLocInd.Howie.spanTerm D t ht) =
      Work.ORLocInd.Howie.RelatorTerm.weight t := by
  rw [Work.ORLocInd.Howie.RelatorTerm.weight, Work.ORLocInd.Howie.RelatorTerm.weight]
  congr 1
  · exact pathToSpan_length D t.δ D.mem_visitedList_base
      (Work.ORLocInd.Howie.mem_visitedList_base_of_usedRelator
        (Work.ORLocInd.Howie.usedRelator_of_mem_terms ht))
      (Work.ORLocInd.Howie.inSpan_delta D ht)
  · exact pathToSpan_length D (P.path t.i)
      (Work.ORLocInd.Howie.mem_visitedList_base_of_usedRelator
        (Work.ORLocInd.Howie.usedRelator_of_mem_terms ht))
      (Work.ORLocInd.Howie.mem_visitedList_base_of_usedRelator
        (Work.ORLocInd.Howie.usedRelator_of_mem_terms ht))
      (Work.ORLocInd.Howie.inSpan_relator (Work.ORLocInd.Howie.usedRelator_of_mem_terms ht))

/-- The transported generator has the same length as the original generator. -/
theorem spanGamma_length (D : Work.ORLocInd.Howie.Datum P v n) (j : Fin n) :
    (Work.ORLocInd.Howie.spanGamma D j).1.length = (D.γ j).1.length :=
  pathToSpan_length D (D.γ j).1 D.mem_visitedList_base D.mem_visitedList_base
    (Work.ORLocInd.Howie.inSpan_gamma D j)

/-- The sum of the weights of the transported terms of the datum is unchanged. -/
theorem spanTerms_weight_sum (D : Work.ORLocInd.Howie.Datum P v n) (j : Fin n) :
    ((Work.ORLocInd.Howie.spanTerms D j).map Work.ORLocInd.Howie.RelatorTerm.weight).sum =
      ((D.terms j).map Work.ORLocInd.Howie.RelatorTerm.weight).sum := by
  show (((D.terms j).attach.map
      (fun t => Work.ORLocInd.Howie.spanTerm D t.1 t.2)).map
        Work.ORLocInd.Howie.RelatorTerm.weight).sum = _
  rw [List.map_map]
  rw [List.map_congr_left (fun t _ => weight_spanTerm D t.2)]
  rw [List.attach_map_val]

theorem spanDatum_L {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n) :
    (Work.ORLocInd.Howie.spanDatum D).L = D.L := by
  unfold Work.ORLocInd.Howie.Datum.L
  congr 1
  · exact Finset.sum_congr rfl (fun j _ => spanGamma_length D j)
  · exact Finset.sum_congr rfl (fun j _ => spanTerms_weight_sum D j)

/-! ## (inlined from `Submission/Work/Case1/spanDatum_M.lean`) -/
open Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}

/-- Erasing a path of the span to the ambient graph replaces its vertices by their values. -/
theorem erase_vertices (D : Datum P v n) (u : SpanVertex D) :
    ∀ {w : SpanVertex D} (p : Quiver.Path u w),
      (erase D u p).vertices = p.vertices.map Subtype.val
  | _, .nil => rfl
  | _, .cons p e => by
      rw [erase_cons, Quiver.Path.vertices_cons, Quiver.Path.vertices_cons,
        erase_vertices D u p, List.map_concat]

/-- The vertices of a transported generator, projected to `Γ`, are the vertices of the generator. -/
theorem spanGamma_vertices (D : Datum P v n) (j : Fin n) :
    ((spanGamma D j).1.vertices).map Subtype.val = (D.γ j).1.vertices :=
  calc ((spanGamma D j).1.vertices).map Subtype.val
      = (erase D (spanV D) (spanGamma D j).1).vertices :=
        (erase_vertices D (spanV D) (spanGamma D j).1).symm
    _ = (D.γ j).1.vertices :=
        congrArg Quiver.Path.vertices (erase_pathToSpan D (D.γ j).1 D.mem_visitedList_base
          D.mem_visitedList_base (inSpan_gamma D j))

/-- The vertices of a relator path of the span, projected to `Γ`, are those of the relator. -/
theorem spanPath_vertices (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    ((spanPath D i).vertices).map Subtype.val = (P.path i.1).vertices :=
  calc ((spanPath D i).vertices).map Subtype.val
      = (erase D (spanBase D i) (spanPath D i)).vertices :=
        (erase_vertices D (spanBase D i) (spanPath D i)).symm
    _ = (P.path i.1).vertices :=
        congrArg Quiver.Path.vertices (erase_pathToSpan D (P.path i.1)
          (mem_visitedList_base_of_usedRelator i.2) (mem_visitedList_base_of_usedRelator i.2)
          (inSpan_relator i.2))

/-- The vertices of the `δ` of a transported term, projected to `Γ`, are those of `δ`. -/
theorem spanTerm_delta_vertices (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    ((spanTerm D t ht).δ.vertices).map Subtype.val = t.δ.vertices :=
  calc ((spanTerm D t ht).δ.vertices).map Subtype.val
      = (erase D (spanV D) (spanTerm D t ht).δ).vertices :=
        (erase_vertices D (spanV D) (spanTerm D t ht).δ).symm
    _ = t.δ.vertices :=
        congrArg Quiver.Path.vertices (erase_pathToSpan D t.δ D.mem_visitedList_base
          (mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht))
          (inSpan_delta D ht))

/-- The vertices of the relator path of a transported term, projected to `Γ`, are those of the
relator of the term. -/
theorem spanTerm_path_vertices (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    (((spanPresentation D).path (spanTerm D t ht).i).vertices).map Subtype.val
      = (P.path t.i).vertices :=
  spanPath_vertices D (spanTerm D t ht).i

/-- The vertices visited by a transported term are those visited by the term. -/
theorem spanTerm_visitedList (D : Datum P v n) {j : Fin n} (t : RelatorTerm P v)
    (ht : t ∈ D.terms j) :
    (RelatorTerm.visitedList (spanTerm D t ht)).map Subtype.val = RelatorTerm.visitedList t := by
  rw [RelatorTerm.visitedList, RelatorTerm.visitedList, List.map_append,
    spanTerm_delta_vertices D t ht, spanTerm_path_vertices D t ht]

/-- The vertices visited by the transported terms of the datum are those visited by the terms. -/
theorem spanTerms_visitedList (D : Datum P v n) (j : Fin n) :
    ((spanTerms D j).flatMap RelatorTerm.visitedList).map Subtype.val
      = (D.terms j).flatMap RelatorTerm.visitedList := by
  show (((D.terms j).attach.map (fun t => spanTerm D t.1 t.2)).flatMap
      RelatorTerm.visitedList).map Subtype.val = _
  rw [List.map_flatMap, List.flatMap_map]
  rw [List.flatMap_subtype
    (f := fun t : {t // t ∈ D.terms j} =>
      (RelatorTerm.visitedList (spanTerm D t.1 t.2)).map Subtype.val)
    (g := fun t : RelatorTerm P v => RelatorTerm.visitedList t)
    (hf := fun x h => spanTerm_visitedList D x h)]
  rw [List.unattach_attach]

/-- The vertices visited by the transported datum, projected to `Γ`, are the vertices visited by
the datum. -/
theorem spanDatum_visitedList (D : Datum P v n) :
    ((spanDatum D).visitedList).map Subtype.val = D.visitedList := by
  show (([spanV D] ++ (List.finRange n).flatMap (fun j => (spanGamma D j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (spanTerms D j).flatMap RelatorTerm.visitedList))).map
      Subtype.val = ([v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList))
  rw [List.map_append, List.map_append, List.map_flatMap, List.map_flatMap]
  rw [List.flatMap_congr (f := fun j => ((spanGamma D j).1.vertices).map Subtype.val)
        (g := fun j => (D.γ j).1.vertices) (l := List.finRange n)
        (fun j _ => spanGamma_vertices D j),
      List.flatMap_congr
        (f := fun j => ((spanTerms D j).flatMap RelatorTerm.visitedList).map Subtype.val)
        (g := fun j => (D.terms j).flatMap RelatorTerm.visitedList) (l := List.finRange n)
        (fun j _ => spanTerms_visitedList D j)]
  rfl

/-- `M` is the number of distinct vertices of a datum; erasure of the span is injective on the
vertices visited, so the transported datum visits exactly as many distinct vertices. -/
theorem spanDatum_M {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n) :
    (Work.ORLocInd.Howie.spanDatum D).M = D.M := by
  have h : ((spanDatum D).visitedList).dedup.length = (D.visitedList).dedup.length := by
    have h1 := congrArg (fun l : List V => l.dedup.length) (spanDatum_visitedList D)
    rw [List.dedup_map_of_injective (f := Subtype.val) Subtype.val_injective
      ((spanDatum D).visitedList), List.length_map] at h1
    exact h1
  exact h

/-! ## (inlined from `Submission/Work/Case1/coverDatum_transfer.lean`) -/
open Work.ORLocInd.Howie
open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

/-- The projection `projHom L v 0` sends a conjugate `δ · α · δ⁻¹` of a relator of the cyclic cover
to the corresponding conjugate of the relator of `P`: `coverProjPath` commutes with the free-groupoid
product (`coverProjPath_pmul`), with reversal (`coverProjPath_reverse`), and the projection of a
lifted relator is the relator (`coverProjPath_coverPath`). -/
theorem projHom_relatorSet_mem (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) (v : V)
    (i : (coverPresentation P L hrel τ hτ).ι)
    (δ : Quiver.Path (⟨v, 0⟩ : CoverVertex L) ((coverPresentation P L hrel τ hτ).base i))
    (hδ : δ.IsReduced) :
    projHom L v 0
      (⟨pmul δ (pmul ((coverPresentation P L hrel τ hτ).path i) δ.reverse), pmul_isReduced _ _⟩ :
        VertexGroup (⟨v, 0⟩ : CoverVertex L)) ∈ P.relatorNormalClosure v := by
  have hx : projHom L v 0
        (⟨pmul δ (pmul ((coverPresentation P L hrel τ hτ).path i) δ.reverse), pmul_isReduced _ _⟩ :
          VertexGroup (⟨v, 0⟩ : CoverVertex L)) =
        (⟨pmul (coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ)
            (pmul (P.path (ofLex i).1) (coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ).reverse),
          pmul_isReduced _ _⟩ : VertexGroup v) := by
    apply Subtype.ext
    show coverProjPath L (⟨v, 0⟩ : CoverVertex L)
        (pmul δ (pmul ((coverPresentation P L hrel τ hτ).path i) δ.reverse)) =
      pmul (coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ)
        (pmul (P.path (ofLex i).1) (coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ).reverse)
    rw [coverProjPath_pmul L (⟨v, 0⟩ : CoverVertex L) δ
          (pmul ((coverPresentation P L hrel τ hτ).path i) δ.reverse)]
    rw [coverProjPath_pmul L ((coverPresentation P L hrel τ hτ).base i)
          ((coverPresentation P L hrel τ hτ).path i) δ.reverse]
    rw [show coverProjPath L ((coverPresentation P L hrel τ hτ).base i)
          ((coverPresentation P L hrel τ hτ).path i) = P.path (ofLex i).1 from
        coverProjPath_coverPath P L hrel (ofLex i).1 (ofLex i).2]
    rw [show coverProjPath L ((coverPresentation P L hrel τ hτ).base i) δ.reverse =
        (coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ).reverse from coverProjPath_reverse L δ]
    rfl
  rw [hx]
  exact Subgroup.subset_normalClosure
    ⟨(ofLex i).1, coverProjPath L (⟨v, 0⟩ : CoverVertex L) δ,
      coverProjPath_isReduced L δ hδ, rfl⟩

/-- The projection `projHom L v 0 : VertexGroup ⟨v,0⟩ →* VertexGroup v` carries the relator normal
closure of the cyclic cover `⟨Γ̃ | R̃⟩` into the relator normal closure of `P` at `v`.  This is the
analogue for the cyclic cover of `map_eraseVG_relatorNormalClosure` for the span: the generating set
of the normal closure consists of conjugates `δ · α · δ⁻¹` of the lifted relators, and each of these
projects to a conjugate of `P.path i` (`projHom_relatorSet_mem`), hence to an element of
`P.relatorNormalClosure v`. -/
theorem map_projHom_relatorNormalClosure (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) (v : V) :
    (coverPresentation P L hrel τ hτ).relatorNormalClosure (⟨v, 0⟩ : CoverVertex L) ≤
      Subgroup.comap (projHom L v 0) (P.relatorNormalClosure v) := by
  show Subgroup.normalClosure
      ((coverPresentation P L hrel τ hτ).relatorSet (⟨v, 0⟩ : CoverVertex L)) ≤
    Subgroup.comap (projHom L v 0) (P.relatorNormalClosure v)
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨i, δ, hδ, rfl⟩
  exact projHom_relatorSet_mem P L hrel τ hτ v i δ hδ

/-- The transfer of vanishing from the lifted datum to `D`: the projection
`projHom L v 0 : VertexGroup ⟨v,0⟩ →* VertexGroup v` (`coverProjPath`) carries the relator normal
closure of the cover presentation into that of `P`, and sends `(coverDatum ...).γ j` to `D.γ j`.
Both are proved as in `map_eraseVG_relatorNormalClosure` of `exists_spanDatum.lean`: a conjugate of
a cover relator `δ · (coverPath P L hrel i m) · δ⁻¹` projects to the conjugate
`(coverProjPath δ) · P.path i · (coverProjPath δ)⁻¹` (`coverProjPath_pmul`, `coverProjPath_reverse`,
`coverProjPath_coverPath`), and `projHom (liftHom ⟨D.γ j, hγ j⟩) = D.γ j` is `projHom_liftHom`. -/
theorem coverDatum_transfer {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hrel : Work.ORLocInd.Howie.VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    (hγ : ∀ j, Work.ORLocInd.Howie.pathSum L.toFun (D.γ j).1 = 0) :
    (∀ j, (Work.ORLocInd.Howie.coverDatum P L hrel τ hτ D hγ).γ j ∈
        (Work.ORLocInd.Howie.coverPresentation P L hrel τ hτ).relatorNormalClosure
          (⟨v, 0⟩ : Work.ORLocInd.Howie.CoverVertex L)) →
      ∀ j, D.γ j ∈ P.relatorNormalClosure v := by
  intro hD j
  have h1 : projHom L v 0 ((coverDatum P L hrel τ hτ D hγ).γ j) ∈ P.relatorNormalClosure v :=
    map_projHom_relatorNormalClosure P L hrel τ hτ v (hD j)
  have h2 : projHom L v 0 ((coverDatum P L hrel τ hτ D hγ).γ j) = D.γ j := by
    show projHom L v 0 (liftHom L v ⟨D.γ j, hγ j⟩) = D.γ j
    exact projHom_liftHom L v ⟨D.γ j, hγ j⟩
  rwa [h2] at h1

/-! ## (inlined from `Submission/Work/Case1/coverDatum_L.lean`) -/
theorem coverDatum_L [DecidableEq V] (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    {v : V} {n : ℕ} (D : Datum P v n) (hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0) :
    (coverDatum P L hrel τ hτ D hγ).L = D.L := by
  unfold Datum.L
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    show ((liftPath L (D.γ j).1 0).cast rfl
      (levelZero_target ⟨D.γ j, hγ j⟩)).length = ((D.γ j).1).length
    rw [path_length_cast, liftPath_length]
  · apply Finset.sum_congr rfl
    intro j _
    show (List.map RelatorTerm.weight ((D.terms j).map (coverTerm P L hrel τ hτ))).sum
      = (List.map RelatorTerm.weight (D.terms j)).sum
    rw [List.map_map]
    apply congrArg List.sum
    refine List.map_congr_left (fun t _ => ?_)
    show ((liftPath L t.δ 0).cast rfl
        (coverVertex_level_eq L (zero_add (pathSum L.toFun t.δ)))).length
      + ((coverPresentation P L hrel τ hτ).path (coverTerm P L hrel τ hτ t).i).length
      = t.δ.length + (P.path t.i).length
    rw [path_length_cast, liftPath_length, coverPresentation_path_length_coverTerm]

/-! ## The target -/

/-- L2 of `N4_LOCIND_LEAD.md`: Howie's Case 1 (the cyclic-cover descent), in its true form.

Lift the datum to the cyclic cover of the presentation along the labelling induced by the surjection
`φ : P.vertexGroup v ↠ ℤ` (`exists_labelling_vanishOnRelators`), then take the span of the lifted
datum (`exists_spanDatum`).  The path-theoretic machinery needed is available:
`liftPath_isReduced`, `liftPath_length`, `liftPath_pmul` (functoriality of the lift, *with* the
explicit vertex cast), `coverProjPath_red`, `coverProjPath_isReduced`, `coverProjPath_liftPath`,
`coverProjPath_coverPath`, `mem_visitedList_of_mem_usedArrowsList`, `exists_loop_pathSum_one`,
`M_le_L_add_one`.  The cover's `liftHom`/`projHom` on vertex groups, if needed, may be built in this
file (`levelZero L v := {x : VertexGroup v // pathSum L.toFun x.1 = 0}`).

The `γ_j` land in `levelZero L v` because `W_j(γ)` is a product of relator conjugates, hence lies in
`ker φ`; the hom `x_j ↦ φ(γ̄_j)` therefore factors through the finite abelianisation of
`PresentedGroup (Set.range D.W)` and must be `0` — this is where `hfin` is used. -/
theorem case1_descent_univ {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    (hind : ∃ φ : P.vertexGroup v →* Multiplicative ℤ, Function.Surjective φ)
    (hfin : Finite (Abelianization (PresentedGroup (Set.range D.W)))) :
    ∃ (V' : Type u) (_ : Quiver V') (_ : Quiver.HasInvolutiveReverse V') (_ : DecidableEq V')
      (P' : Work.ORLocInd.Howie.Presentation V') (v' : V') (D' : Work.ORLocInd.Howie.Datum P' v' n),
      P'.CodeSeparates ∧ D'.measure < D.measure ∧ D'.W = D.W ∧
      (∀ e : Quiver.Total V', e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D') ∧
      (∀ i : P'.ι, Work.ORLocInd.Howie.UsedRelator D' i) ∧
      (∀ x : V', Nonempty (Quiver.Path v' x)) ∧
      ((∀ j, D'.γ j ∈ P'.relatorNormalClosure v') → ∀ j, D.γ j ∈ P.relatorNormalClosure v) := by
  classical
  obtain ⟨φ, hφ⟩ := hind
  obtain ⟨d, L, τ, hτ, hpath, hvanish⟩ := exists_labelling_vanishOnRelators P v hconn φ hφ
  have hγ : ∀ j, pathSum L.toFun (D.γ j).1 = 0 :=
    pathSum_gamma_eq_zero P v D L d φ hpath hfin
  obtain ⟨β, hβred, hβsum⟩ := exists_loop_pathSum_one P v d L φ hφ hpath
  refine ⟨SpanVertex (coverDatum P L hvanish τ hτ D hγ),
    inferInstance, inferInstance, inferInstance,
    spanPresentation (coverDatum P L hvanish τ hτ D hγ),
    spanV (coverDatum P L hvanish τ hτ D hγ),
    spanDatum (coverDatum P L hvanish τ hτ D hγ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CodeSeparates_span _ (CodeSeparates_cover hsep L hvanish τ hτ)
  · have hM : D.M < (coverDatum P L hvanish τ hτ D hγ).M :=
      coverDatum_M_gt P L hvanish τ hτ D hγ ⟨β, hβred, hβsum⟩ hpair
    have hLc : (coverDatum P L hvanish τ hτ D hγ).L = D.L :=
      coverDatum_L P L hvanish τ hτ D hγ
    have hLsc : (spanDatum (coverDatum P L hvanish τ hτ D hγ)).L =
        (coverDatum P L hvanish τ hτ D hγ).L := spanDatum_L _
    have hMsc : (spanDatum (coverDatum P L hvanish τ hτ D hγ)).M =
        (coverDatum P L hvanish τ hτ D hγ).M := spanDatum_M _
    have hML : D.M ≤ D.L + 1 := M_le_L_add_one D
    show 2 * (spanDatum (coverDatum P L hvanish τ hτ D hγ)).L + 2
        - (spanDatum (coverDatum P L hvanish τ hτ D hγ)).M < 2 * D.L + 2 - D.M
    rw [hLsc, hMsc, hLc]
    omega
  · rfl
  · exact mem_usedArrowsList_spanDatum _
  · exact usedRelator_spanDatum _
  · exact span_reachable _
  · intro h j
    exact coverDatum_transfer P L hvanish τ hτ D hγ (spanDatum_transfer _ h) j

/-! ## The requested theorem (with `V` and `V'` in independent universes)

**Note for the assembling agent.**  The lemma requested at this path is stated with `{V : Type*}`
(so `V` may live in any universe) and a witness `V' : Type u`; that is `case1_descent` below.
The *same-universe* version — which is the shape of the hypothesis `hcase1` of
`datum_vanishes_spanned` / `locallyIndicable_vertexGroup`, and which can be passed there directly —
is `case1_descent_univ` above (its statement is literally `case1_descent` with `{V : Type u}`).

The datum `D` inhabits the universe of `V`, while the witness `V'` must lie in the fixed universe
`u`; the two steps are

* `case1_descent_univ` (the cyclic-cover descent, with `V'` in the same universe as `V`);
* `Work.Case1.smallModel` (a faithful *small model* of a datum: a presentation on a graph whose
  vertices and arrows are indexed by finite types, with a datum with the same words and measure
  whose vanishing implies that of `D`).

Composing the transfers gives the statement. -/

/-- L2 of `N4_LOCIND_LEAD.md`: Howie's Case 1 (the cyclic-cover descent), in its true form. -/
theorem case1_descent {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    (hind : ∃ φ : P.vertexGroup v →* Multiplicative ℤ, Function.Surjective φ)
    (hfin : Finite (Abelianization (PresentedGroup (Set.range D.W)))) :
    ∃ (V' : Type u) (_ : Quiver V') (_ : Quiver.HasInvolutiveReverse V') (_ : DecidableEq V')
      (P' : Work.ORLocInd.Howie.Presentation V') (v' : V') (D' : Work.ORLocInd.Howie.Datum P' v' n),
      P'.CodeSeparates ∧ D'.measure < D.measure ∧ D'.W = D.W ∧
      (∀ e : Quiver.Total V', e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D') ∧
      (∀ i : P'.ι, Work.ORLocInd.Howie.UsedRelator D' i) ∧
      (∀ x : V', Nonempty (Quiver.Path v' x)) ∧
      ((∀ j, D'.γ j ∈ P'.relatorNormalClosure v') → ∀ j, D.γ j ∈ P.relatorNormalClosure v) := by
  obtain ⟨V₁, iq₁, ir₁, ide₁, P₁, v₁, D₁, hsep₁, hlt, hW₁, hpair₁, hrel₁, hconn₁, htr₁⟩ :=
    case1_descent_univ P hsep v D hconn hpair hrel hind hfin
  obtain ⟨V', iq', ir', ide', P', v', D', hsep', hmeas', hW', hpair', hrel', hconn', htr'⟩ :=
    Work.Case1.smallModel P₁ hsep₁ v₁ D₁ hconn₁ hpair₁ hrel₁
  exact ⟨V', iq', ir', ide', P', v', D', hsep', by rw [hmeas']; exact hlt,
    by rw [hW', hW₁], hpair', hrel', hconn', fun h => htr₁ (htr' h)⟩

end Work.ORLocInd.Howie
