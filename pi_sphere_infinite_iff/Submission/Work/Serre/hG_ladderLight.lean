import Mathlib
import Submission.Work.Serre.thomCylLadderEps
import Submission.Work.Serre.thomCylLadder
import Submission.Work.StemsB.AToolsR
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso
import Submission.Work.Serre.TripleCohDefs

/-!
# The middle square `hG` of the ladder of the cellular step

This file proves `Work.Serre.mq_hG_ladder`: the commutation of the **middle square** of the ladder of
the cellular step, i.e. the naturality of the `IH`-class `U` of `Work.Serre.thomCylLadderEps`
under the identification of the part of the mapping cylinder of `q` over `S := ladS D Γ ι f` with
the mapping cylinder of the restricted fibration `q|_S`.

Concretely, with `S := ladS D Γ ι f`, `A := Set.range (cylIncl q)` the bottom copy of the source
and `U_S` the `IH` class over `(cyl (q|_S), A_S)`, the hypotheses of `mq_hG_ladder` provide a class
`U ∈ H^{r+1}(cyl q, A)` whose restriction to the pair `(new, A)`, `new := (cylRetract q) ⁻¹' S ∪ A`,
is the class `uNew r q S U_S` — the image of `U_S` under the inverse of the identification
`oldPartIso : H^*(new, A) ≅ H^*(cyl (q|_S), A_S)`.  The statement is then

`baseG k ≫ TQ k = TP k ≫ totG (k + (r+1))`,

where `baseG` is the restriction `H^k(Γ') → H^k(S)`, `TQ` is the cup product with `U_S` over the old
part, `TP` the cup product with `U` over the mapping cylinder and `totG` the restriction
`H^*(cyl q, A) → H^*(new, A)`.

The mathematical content is the naturality of the cup product together with the compatibility of the
retractions `cylRetract q` and `cylRetract (q|_S)`; the whole proof is the diagram

`(oldPartIso.hom) ∘ totG = relCohMap pX`  (`pX : cyl (q|_S) → cyl q` the identification),

combined with the identification `(oldPartIso.hom) (totG U) = U_S` supplied by the hypothesis `hU`.

The proof is organised in three layers, each of which is a direct elementwise computation (the
`rw`-free form is used because the terms involved are large):

* `mq_hGpX`, `mq_hGpX_congr`, `mq_hGpX_retract`: the map `pX` and its two comparison identities;
* `mq_totG_oldPartIso_apply` / `mq_totG_comp_oldPartIso`: the composite `totG m ≫ oldPartIso.hom` is the
  pullback along `pX`;
* the main theorem: the square, by cancelling `oldPartIso` on the left.
-/

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 400000

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- **Local copy of the retraction compatibility of `cylPreimageHomeo`**
(`Work.Serre.DiscPair.cylRetract_cylPreimageHomeo`), re-proved here so that this module does not have
to import `DiscPair.fibreValuePropagation` (whose closure runs through the E3(b) node and would close
an import cycle with the cellular step). -/
theorem mq_cylRetract_cylPreimageHomeo {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ]
    (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S)
    (y : Work.Serre.cyl (Work.Serre.DiscPair.qS q S)) :
    (Work.Serre.cylRetract q (Work.Serre.DiscPair.cylPreimageHomeo q S hS y) : Γ)
      = ((Work.Serre.cylRetract (Work.Serre.DiscPair.qS q S) y : ↥S) : Γ) := by
  rw [Work.Serre.DiscPair.cylPreimageHomeo_apply]
  revert y
  refine Quotient.ind ?_
  intro a
  rw [Work.Serre.DiscPair.cylPreimageLift_mk]
  cases a with
  | inl z => rfl
  | inr y => rfl

/-! ## The comparison map `pX : cyl (q|_S) → cyl q` -/

/-- The comparison map `cyl (q|_S) → cyl q`: the homeomorphism `cylPreimageHomeo` of the mapping
cylinder of the restricted fibration with the part of the mapping cylinder of `q` over `S`, followed
by the inclusion into `cyl q`. -/
def mq_hGpX (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(Work.Serre.cyl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)), Work.Serre.cyl q) :=
  ⟨fun y => (Work.Serre.preimageMap q (Work.Serre.ladS D Γ ι f)
      Work.RatHurewicz.isClosed_range_attachIncl y : Work.Serre.cyl q),
    continuous_subtype_val.comp
      (Work.Serre.preimageMap q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl).continuous⟩

/-- `pX` is the inclusion of the preimage mapping cylinder followed by the inclusion
`old ↪ old ∪ A`. -/
theorem mq_hGpX_congr (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.ladNew D ι f q), Work.Serre.cyl q)).comp
      (Work.Serre.oldInclToNew q (Work.Serre.ladS D Γ ι f))).comp
        (Work.Serre.preimageMap q (Work.Serre.ladS D Γ ι f) Work.RatHurewicz.isClosed_range_attachIncl)
    = mq_hGpX q := by
  apply ContinuousMap.ext
  intro y
  rfl

/-- The retraction of `cyl q` is compatible with `pX` and the retraction of `cyl (q|_S)`. -/
theorem mq_hGpX_retract (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    (Work.Serre.cylRetract q).comp (mq_hGpX q)
    = (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.ladS D Γ ι f), Work.RatHurewicz.attachCells (D - 2) Γ ι f)).comp
      (Work.Serre.cylRetract (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))) := by
  apply ContinuousMap.ext
  intro y
  exact mq_cylRetract_cylPreimageHomeo q (Work.Serre.ladS D Γ ι f)
    Work.RatHurewicz.isClosed_range_attachIncl y

/-! ## The `Iso` computation rules of `oldPartIso` -/

/-- `oldPartIso.hom` is a left inverse of `oldPartIso.inv`. -/
theorem mq_oldPartIso_hom_inv_apply (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S) (m : ℕ)
    (z : Work.Thom.RelCoh ℚ m (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))) :
    ((Work.Serre.oldPartIso q S hS m).hom).hom
      (((Work.Serre.oldPartIso q S hS m).inv).hom z) = z := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (CategoryTheory.Iso.inv_hom_id (Work.Serre.oldPartIso q S hS m))
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply] using h

/-- `oldPartIso.inv` is a left inverse of `oldPartIso.hom`. -/
theorem mq_oldPartIso_inv_hom_apply (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S) (m : ℕ)
    (z : Work.Thom.RelCoh ℚ m
      ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) :
    ((Work.Serre.oldPartIso q S hS m).inv).hom
      (((Work.Serre.oldPartIso q S hS m).hom).hom z) = z := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (CategoryTheory.Iso.hom_inv_id (Work.Serre.oldPartIso q S hS m))
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply] using h

/-! ## The composite `totG m ≫ oldPartIso.hom` is the pullback along `pX` -/

/-- **The key computation, elementwise**: the restriction to `(new, A)` followed by the
identification `oldPartIso` is the pullback along `pX`. -/
theorem mq_totG_oldPartIso_apply (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (m : ℕ)
    (y : Work.Thom.RelCoh ℚ m (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    ((Work.Serre.oldPartIso q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl m).hom).hom
      ((Work.Serre.totG D ι f q m).hom y)
    = (Work.Thom.relCohMap (mq_hGpX q)
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))))
        (Set.range (Work.Serre.cylIncl q))
        (fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl x).mpr hx) ℚ m).hom y := by
  let S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := Work.Serre.ladS D Γ ι f
  let hS : IsClosed S := Work.RatHurewicz.isClosed_range_attachIncl
  let A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q)
  let rngS : Set (Work.Serre.cyl (Work.Serre.restrictFibre q S)) :=
      Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))
  let AmO : Set ↥((Work.Serre.cylRetract q) ⁻¹' S) := {x | (x : Work.Serre.cyl q) ∈ A}
  let AmN : Set ↥(Work.Serre.ladNew D ι f q) := {x | (x : Work.Serre.cyl q) ∈ A}
  let sub : C(↥(Work.Serre.ladNew D ι f q), Work.Serre.cyl q) :=
      ⟨Subtype.val, continuous_subtype_val⟩
  let hfN : ∀ x ∈ AmN, sub x ∈ A := fun x hx => hx
  let hfO : ∀ x ∈ AmO, Work.Serre.oldInclToNew q S x ∈ AmN := fun x hx => hx
  let hfP : ∀ x ∈ rngS, Work.Serre.preimageMap q S hS x ∈ AmO :=
      fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q S hS x).mpr hx
  let hfX : ∀ x ∈ rngS, mq_hGpX q x ∈ A :=
      fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q S hS x).mpr hx
  let hgf1 : ∀ x ∈ AmO, sub (Work.Serre.oldInclToNew q S x) ∈ A := fun x hx => hx
  let hgf2 : ∀ x ∈ rngS, sub (Work.Serre.oldInclToNew q S (Work.Serre.preimageMap q S hS x)) ∈ A :=
      fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q S hS x).mpr hx
  have h1 : ((Work.Serre.oldPartIso q S hS m).hom).hom ((Work.Serre.totG D ι f q m).hom y)
      = (Work.Thom.relCohMap (Work.Serre.preimageMap q S hS) rngS AmO hfP ℚ m).hom
          ((Work.Thom.relCohMap (Work.Serre.oldInclToNew q S) AmO AmN hfO ℚ m).hom
            ((Work.Thom.relCohMap sub AmN A hfN ℚ m).hom y)) := rfl
  have h2 : (Work.Thom.relCohMap (Work.Serre.preimageMap q S hS) rngS AmO hfP ℚ m).hom
        ((Work.Thom.relCohMap (Work.Serre.oldInclToNew q S) AmO AmN hfO ℚ m).hom
          ((Work.Thom.relCohMap sub AmN A hfN ℚ m).hom y))
      = (Work.Thom.relCohMap (Work.Serre.preimageMap q S hS) rngS AmO hfP ℚ m).hom
        ((Work.Thom.relCohMap (sub.comp (Work.Serre.oldInclToNew q S)) AmO A hgf1 ℚ m).hom y) :=
    congrArg (fun z => (Work.Thom.relCohMap (Work.Serre.preimageMap q S hS) rngS AmO hfP ℚ m).hom z)
      (Work.Thom.relCohMap_compA_apply AmO AmN A (Work.Serre.oldInclToNew q S) sub hfO hfN hgf1 ℚ m y)
  have h3 : (Work.Thom.relCohMap (Work.Serre.preimageMap q S hS) rngS AmO hfP ℚ m).hom
        ((Work.Thom.relCohMap (sub.comp (Work.Serre.oldInclToNew q S)) AmO A hgf1 ℚ m).hom y)
      = (Work.Thom.relCohMap ((sub.comp (Work.Serre.oldInclToNew q S)).comp
            (Work.Serre.preimageMap q S hS)) rngS A hgf2 ℚ m).hom y :=
    Work.Thom.relCohMap_compA_apply rngS AmO A (Work.Serre.preimageMap q S hS)
      (sub.comp (Work.Serre.oldInclToNew q S)) hfP hgf1 hgf2 ℚ m y
  have h4 : (Work.Thom.relCohMap ((sub.comp (Work.Serre.oldInclToNew q S)).comp
            (Work.Serre.preimageMap q S hS)) rngS A hgf2 ℚ m).hom y
      = (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ m).hom y :=
    congrArg (fun φ => (ModuleCat.Hom.hom φ y))
      (Work.Thom.relCohMap_congrA rngS A (mq_hGpX_congr q) hgf2 hfX ℚ m)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **The composite `totG m ≫ (oldPartIso.hom)` is the pullback along `pX`.** -/
theorem mq_totG_comp_oldPartIso (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (m : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.totG D ι f q m)
      (Work.Serre.oldPartIso q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl m).hom
    = Work.Thom.relCohMap (mq_hGpX q)
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))))
        (Set.range (Work.Serre.cylIncl q))
        (fun x hx => (Work.Serre.DiscPair.cylPreimageHomeo_range q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl x).mpr hx) ℚ m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact mq_totG_oldPartIso_apply q m y

/-! ## The compatibility of `baseG` with `CohMap pX` -/

/-- The identification `baseG k = (subtypeIncl)^*` on rational cohomology. -/
theorem mq_baseG_eq_CohMap (k : ℕ) :
    Work.Serre.baseG D Γ ι f k
    = Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.ladS D Γ ι f), Work.RatHurewicz.attachCells (D - 2) Γ ι f)) ℚ k := rfl

/-- **The `CohMap` comparison**: pulling `x` back to `cyl (q|_S)` along
`cylRetract q ∘ pX` is the same as restricting `x` to `S` and then pulling back along
`cylRetract (q|_S)`. -/
theorem mq_CohMap_hGpX_baseG (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (k : ℕ)
    (x : Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    (Work.Thom.CohMap (mq_hGpX q) ℚ k).hom
        ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom x)
      = (Work.Thom.CohMap
          (Work.Serre.cylRetract (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))) ℚ k).hom
          ((Work.Serre.baseG D Γ ι f k).hom x) := by
  have h1 := Work.Thom.CohMap_comp_apply (mq_hGpX q) (Work.Serre.cylRetract q) ℚ k x
  have h2 : (Work.Thom.CohMap ((Work.Serre.cylRetract q).comp (mq_hGpX q)) ℚ k).hom x
      = (Work.Thom.CohMap ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(Work.Serre.ladS D Γ ι f),
              Work.RatHurewicz.attachCells (D - 2) Γ ι f)).comp
            (Work.Serre.cylRetract (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))) ℚ k).hom x :=
    congrArg (fun φ => (Work.Thom.CohMap φ ℚ k).hom x) (mq_hGpX_retract q)
  have h3 := Work.Thom.CohMap_comp_apply
      (Work.Serre.cylRetract (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.ladS D Γ ι f), Work.RatHurewicz.attachCells (D - 2) Γ ι f)) ℚ k x
  have h4 : (Work.Serre.baseG D Γ ι f k).hom x
      = (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Work.Serre.ladS D Γ ι f), Work.RatHurewicz.attachCells (D - 2) Γ ι f)) ℚ k).hom x := rfl
  exact h1.trans (h2.trans (h3.symm.trans
    (congrArg (fun z => (Work.Thom.CohMap
      (Work.Serre.cylRetract (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))) ℚ k).hom z)
      h4.symm)))

end

/-! ## The middle square -/

theorem mq_hG_ladder (r D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U_S : Work.Thom.RelCoh ℚ (r + 1)
      (Work.Serre.cyl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = Work.Serre.uNew r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl U_S)
    (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.baseG D Γ ι f k)
        (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl U_S k)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.TP r q U k)
        (Work.Serre.totG D ι f q (k + (r + 1))) := by
  have hmain : ∀ x : Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D - 2) Γ ι f),
      (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl U_S k).hom
        ((Work.Serre.baseG D Γ ι f k).hom x)
      = (Work.Serre.totG D ι f q (k + (r + 1))).hom ((Work.Serre.TP r q U k).hom x) := by
    intro x
    let S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := Work.Serre.ladS D Γ ι f
    let hS : IsClosed S := Work.RatHurewicz.isClosed_range_attachIncl
    let n : ℕ := k + (r + 1)
    let A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q)
    let rngS : Set (Work.Serre.cyl (Work.Serre.restrictFibre q S)) :=
        Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))
    let hfX : ∀ y ∈ rngS, mq_hGpX q y ∈ A :=
        fun y hy => (Work.Serre.DiscPair.cylPreimageHomeo_range q S hS y).mpr hy
    let e := Work.Serre.oldPartIso q S hS n
    -- ### The hypothesis `hU` in the form needed
    have hII : (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ (r + 1)).hom U = U_S := by
      have hU' : (Work.Serre.totG D ι f q (r + 1)).hom U
          = ((Work.Serre.oldPartIso q S hS (r + 1)).inv).hom U_S := hU
      have step1 : (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ (r + 1)).hom U
          = ((Work.Serre.oldPartIso q S hS (r + 1)).hom).hom
              ((Work.Serre.totG D ι f q (r + 1)).hom U) :=
        (mq_totG_oldPartIso_apply q (r + 1) U).symm
      have step2 : ((Work.Serre.oldPartIso q S hS (r + 1)).hom).hom
              ((Work.Serre.totG D ι f q (r + 1)).hom U)
          = ((Work.Serre.oldPartIso q S hS (r + 1)).hom).hom
              (((Work.Serre.oldPartIso q S hS (r + 1)).inv).hom U_S) :=
        congrArg (fun z => ((Work.Serre.oldPartIso q S hS (r + 1)).hom).hom z) hU'
      exact step1.trans (step2.trans (mq_oldPartIso_hom_inv_apply q S hS (r + 1) U_S))
    -- ### The two sides of the square, after cancelling `oldPartIso`
    have hI := mq_CohMap_hGpX_baseG q k x
    have hTP : (Work.Serre.TP r q U k).hom x
        = (Work.Thom.mixedCupC ℚ A k (r + 1))
            ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom x) U := rfl
    have hW : (Work.Serre.oldCupMap r q S U_S k).hom ((Work.Serre.baseG D Γ ι f k).hom x)
        = (Work.Thom.mixedCupC ℚ rngS k (r + 1))
            ((Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q S)) ℚ k).hom
              ((Work.Serre.baseG D Γ ι f k).hom x)) U_S := rfl
    have hY1 : (e.hom).hom ((Work.Serre.totG D ι f q n).hom ((Work.Serre.TP r q U k).hom x))
        = (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ n).hom
            ((Work.Serre.TP r q U k).hom x) :=
      mq_totG_oldPartIso_apply q n ((Work.Serre.TP r q U k).hom x)
    have hY2 : (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ n).hom
            ((Work.Serre.TP r q U k).hom x)
        = (Work.Thom.mixedCupC ℚ rngS k (r + 1))
            ((Work.Thom.CohMap (mq_hGpX q) ℚ k).hom
              ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom x))
            ((Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ (r + 1)).hom U) :=
      (congrArg (fun z => (Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ n).hom z) hTP).trans
        (Work.StemsB.mixedCupC_pairNaturalR ℚ (mq_hGpX q) rngS A hfX k (r + 1)
          ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom x) U)
    have hY3 : (Work.Thom.mixedCupC ℚ rngS k (r + 1))
            ((Work.Thom.CohMap (mq_hGpX q) ℚ k).hom
              ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom x))
            ((Work.Thom.relCohMap (mq_hGpX q) rngS A hfX ℚ (r + 1)).hom U)
        = (Work.Thom.mixedCupC ℚ rngS k (r + 1))
            ((Work.Thom.CohMap
              (Work.Serre.cylRetract (Work.Serre.restrictFibre q S)) ℚ k).hom
              ((Work.Serre.baseG D Γ ι f k).hom x)) U_S :=
      congrArg₂ (fun a b => (Work.Thom.mixedCupC ℚ rngS k (r + 1)) a b) hI hII
    have hA : (Work.Serre.oldCupMap r q S U_S k).hom ((Work.Serre.baseG D Γ ι f k).hom x)
        = (e.hom).hom
            ((Work.Serre.totG D ι f q n).hom ((Work.Serre.TP r q U k).hom x)) :=
      hW.trans ((hY1.trans (hY2.trans hY3)).symm)
    -- ### Assembly
    have hTQ : (Work.Serre.TQ r q S hS U_S k).hom ((Work.Serre.baseG D Γ ι f k).hom x)
        = (e.inv).hom
            ((Work.Serre.oldCupMap r q S U_S k).hom ((Work.Serre.baseG D Γ ι f k).hom x)) := rfl
    exact hTQ.trans ((congrArg (fun z => (e.inv).hom z) hA).trans
      (mq_oldPartIso_inv_hom_apply q S hS n ((Work.Serre.totG D ι f q n).hom
        ((Work.Serre.TP r q U k).hom x))))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hmain x

end Work.Serre
