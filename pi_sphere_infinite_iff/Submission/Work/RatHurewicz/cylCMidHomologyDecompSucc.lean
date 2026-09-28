import Mathlib
import Submission.Work.RatHurewicz.CMidSuccDefs
import Submission.Work.Serre.CylCMidVan.relChainsR_excisionInterior
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.DiscPair.lesSplitPair
import Submission.Work.Serre.DiscPair.relPairHomotopic
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylCollarShrink

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The cofibre decomposition of the pair `(cyl q, CMid q b)` in degree `r+1`

This file proves `Work.RatHurewicz.cylCMidHomologyDecompSucc`: over `ℚ`,

`H_{r+1}(cyl q, CMid q b) ≅ coker(f_{r+1}) × ker(f_r)`,  `f = relPairMapRat q b`.

The proof follows `Submission/Work/Serre/DiscPair/cylPairCofibre.lean`.  The two comparison
quasi-isomorphisms of the cofibre computation are

* `isIso_collapseMapSucc` — the collapse `C_*(X, q⁻¹b;ℚ) → C_*(CMid q b, P;ℚ)` is an
  isomorphism on homology.  It factors as
  `(X, q⁻¹b) → (cylBot q, PBot q b) → (Ucol q b, PUcol q b) → (CMid q b, Pmid q b)`,
  where the first map is a homeomorphism of pairs (`cylHomeoExplicit`, inverted by the collar
  coordinate), the second is the collar shrink (`cylShrink`, a homotopy equivalence of pairs,
  `isIso_collarPairSucc`) and the third is the excision of the collar
  (`Work.Serre.CylCMidVan.relChainsR_excisionInterior` with the "interiors cover" hypothesis
  `Work.Serre.CMidCollar.interior_union_eq_univ`);
* `isIso_retractMapSucc` — the retraction `C_*(cyl q, P;ℚ) → C_*(B, {b};ℚ)` is an isomorphism on
  homology: `cylRetract q` is a homotopy equivalence (`cylHomotopyEquivExplicit`) and so is its
  restriction to the fibre `P`, which is contracted by the push-up homotopy `cylMove`.

The decomposition itself is the linear algebra of the long exact sequence of the triple
`P ⊆ CMid q b ⊆ cyl q` (`RatTower.tripleShortR`), split over `ℚ` by
`Work.Serre.DiscPair.linearEquiv_prod_of_exact`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The bottom copy inclusion and its inverse, the collar coordinate -/

/-- The bottom copy inclusion `X → cylBot q`, `x ↦ cylIncl q x`. -/
def botIncl (q : C(X, B)) : C(X, ↥(Work.Serre.cylBot q)) where
  toFun x := ⟨Work.Serre.cylIncl q x, x, rfl⟩
  continuous_toFun := Continuous.subtype_mk (Work.Serre.cylIncl q).continuous _

@[simp] theorem botIncl_coe (q : C(X, B)) (x : X) :
    ((botIncl q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = Work.Serre.cylIncl q x := rfl

theorem botIncl_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (botIncl q) (q ⁻¹' ({b} : Set B)) (PBot q b) := by
  intro x hx
  show (Work.Serre.cylRetract q) ((botIncl q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = b
  rw [botIncl_coe, Work.Serre.cylRetract_cylIncl_eq]
  exact hx

/-- **The inverse of the bottom copy inclusion**: the collar coordinate of a point of the bottom
copy. -/
def botRetr (q : C(X, B)) : C(↥(Work.Serre.cylBot q), X) where
  toFun y := ((Work.Serre.cylCollarEquiv q).symm
    ⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩).1
  continuous_toFun := by
    have h1 : Continuous fun y : ↥(Work.Serre.cylBot q) =>
        (⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩ :
          ↥(Work.Serre.cylCollar q)) :=
      Continuous.subtype_mk continuous_subtype_val _
    exact continuous_fst.comp ((Work.Serre.cylCollarEquiv q).symm.continuous.comp h1)

theorem botRetr_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (botRetr q) (PBot q b) (q ⁻¹' ({b} : Set B)) := by
  intro y hy
  set w := (Work.Serre.cylCollarEquiv q).symm
    ⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩ with hwdef
  have h1 : ((Work.Serre.cylCollarEquiv q w : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q)
      = (y : Work.Serre.cyl q) := by
    rw [hwdef]
    exact congrArg Subtype.val (Homeomorph.apply_symm_apply (Work.Serre.cylCollarEquiv q)
      ⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩)
  have h2 : Work.Serre.cylMk q (Sum.inl (w.1, w.2.1))
      = ((Work.Serre.cylCollarEquiv q w : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q) :=
    (Work.Serre.cylCollarEquiv_apply_coe q w).symm
  show q (botRetr q y) = b
  have hq : q (botRetr q y)
      = (Work.Serre.cylRetract q) ((y : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) := by
    have hw1 : botRetr q y = w.1 := by rw [hwdef]; rfl
    rw [hw1, ← h1, ← h2, Work.Serre.cylRetract_cylMk, Work.Serre.cylRetractFun_inl]
  rw [hq]
  exact hy

theorem botRetr_botIncl (q : C(X, B)) (x : X) : botRetr q (botIncl q x) = x := by
  have h0 : (⟨((botIncl q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q),
      Work.Serre.cylBot_subset_cylCollar q (botIncl q x).2⟩ : ↥(Work.Serre.cylCollar q))
      = Work.Serre.cylCollarEquiv q (x, (⟨0, by norm_num⟩ : Work.Serre.CollT)) := by
    refine Subtype.ext ?_
    rw [Work.Serre.cylCollarEquiv_apply_coe]
    rfl
  show ((Work.Serre.cylCollarEquiv q).symm
    ⟨((botIncl q x : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q),
      Work.Serre.cylBot_subset_cylCollar q (botIncl q x).2⟩).1 = x
  rw [h0, Homeomorph.symm_apply_apply]

theorem botIncl_botRetr (q : C(X, B)) (y : ↥(Work.Serre.cylBot q)) :
    botIncl q (botRetr q y) = y := by
  obtain ⟨x', hx'⟩ := y.2
  set w := (Work.Serre.cylCollarEquiv q).symm
    ⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩ with hwdef
  have h1 : ((Work.Serre.cylCollarEquiv q w : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q)
      = Work.Serre.cylIncl q x' := by
    rw [hwdef]
    rw [congrArg Subtype.val (Homeomorph.apply_symm_apply (Work.Serre.cylCollarEquiv q)
      ⟨(y : Work.Serre.cyl q), Work.Serre.cylBot_subset_cylCollar q y.2⟩)]
    exact hx'.symm
  have h2 : ((Work.Serre.cylCollarEquiv q w : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q)
      = Work.Serre.cylMk q (Sum.inl (w.1, w.2.1)) := Work.Serre.cylCollarEquiv_apply_coe q w
  have h3 : Work.Serre.cylMk q (Sum.inl (w.1, w.2.1))
      = Work.Serre.cylMk q (Sum.inl (x', (0 : unitInterval))) := by
    rw [← h2, h1]
    rfl
  have h4 : w.1 = x' := (Work.Serre.cylCollar_injective q w.2.2 h3).1
  have hb : botRetr q y = w.1 := by rw [hwdef]; rfl
  refine Subtype.ext ?_
  show Work.Serre.cylIncl q (botRetr q y) = (y : Work.Serre.cyl q)
  rw [hb, h4, hx']

/-- **The bottom copy inclusion is a homeomorphism of pairs** `(X, q⁻¹{b}) ≅ (cylBot q, PBot q b)`,
hence an isomorphism on relative rational homology. -/
theorem isIso_botPairSucc (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
      (q ⁻¹' ({b} : Set B)) (PBot q b) (botIncl q) (botIncl_mapsTo q b)) n) := by
  have hcomp₁ : Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PBot q b)
        (botIncl q) (botIncl_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (PBot q b) (q ⁻¹' ({b} : Set B))
        (botRetr q) (botRetr_mapsTo q b)
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (q ⁻¹' ({b} : Set B))
        ((botRetr q).comp (botIncl q)) ((botRetr_mapsTo q b).comp (botIncl_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (botIncl q) (botRetr q)
      (botIncl_mapsTo q b) (botRetr_mapsTo q b)
      (hg'' := (botRetr_mapsTo q b).comp (botIncl_mapsTo q b))
  have hcomp₂ : Work.Serre.relChainsRPairMap (PBot q b) (q ⁻¹' ({b} : Set B))
        (botRetr q) (botRetr_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PBot q b)
        (botIncl q) (botIncl_mapsTo q b)
      = Work.Serre.relChainsRPairMap (PBot q b) (PBot q b)
        ((botIncl q).comp (botRetr q)) ((botIncl_mapsTo q b).comp (botRetr_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (botRetr q) (botIncl q)
      (botRetr_mapsTo q b) (botIncl_mapsTo q b)
      (hg'' := (botIncl_mapsTo q b).comp (botRetr_mapsTo q b))
  have hψφ : (botRetr q).comp (botIncl q) = ContinuousMap.id X := by
    ext x
    exact botRetr_botIncl q x
  have hφψ : (botIncl q).comp (botRetr q) = ContinuousMap.id ↥(Work.Serre.cylBot q) := by
    ext y
    exact congrArg Subtype.val (botIncl_botRetr q y)
  have h1 : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B))
        (PBot q b) (botIncl q) (botIncl_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PBot q b)
        (q ⁻¹' ({b} : Set B)) (botRetr q) (botRetr_mapsTo q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₁]
    rw [show Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (q ⁻¹' ({b} : Set B))
          ((botRetr q).comp (botIncl q)) _ = 𝟙 _ from
      (Work.Serre.relChainsRPairMap_congr hψφ _ _).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (q ⁻¹' ({b} : Set B))
          (fun _ hx => hx))]
    rw [HomologicalComplex.homologyMap_id]
  have h2 : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PBot q b)
        (q ⁻¹' ({b} : Set B)) (botRetr q) (botRetr_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B))
        (PBot q b) (botIncl q) (botIncl_mapsTo q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₂]
    rw [show Work.Serre.relChainsRPairMap (PBot q b) (PBot q b)
          ((botIncl q).comp (botRetr q)) _ = 𝟙 _ from
      (Work.Serre.relChainsRPairMap_congr hφψ _ _).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (PBot q b) (fun _ hx => hx))]
    rw [HomologicalComplex.homologyMap_id]
  exact IsIso.mk ⟨_, h1, h2⟩

/-! ## The collar shrink: `(cylBot q, PBot q b) → (Ucol q b, PUcol q b)` -/

/-- The projection of the collar part `Ucol q b` of `CMid q b` to the collar. -/
def toCollar (q : C(X, B)) (b : B) : C(↥(Ucol q b), ↥(Work.Serre.cylCollar q)) where
  toFun y := ⟨((y : ↥(Ucol q b)) : ↥(Work.Serre.CMid q b)), y.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

@[simp] theorem toCollar_coe (q : C(X, B)) (b : B) (y : ↥(Ucol q b)) :
    ((toCollar q b y : ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q)
      = ((y : ↥(Ucol q b)) : Work.Serre.cyl q) := rfl

/-- **The collar shrink, restricted to `Ucol q b`.** -/
def shrinkU (q : C(X, B)) (b : B) :
    C(unitInterval × ↥(Ucol q b), ↥(Ucol q b)) where
  toFun p := ⟨⟨((Work.Serre.cylShrink q p.1 (toCollar q b p.2) :
        ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q),
      Work.Serre.CMidCollar.cylShrink_mem_Mid q b p.1 p.2.1.2⟩,
    (Work.Serre.cylShrink q p.1 (toCollar q b p.2)).2⟩
  continuous_toFun := by
    have hEq : (fun p : unitInterval × ↥(Ucol q b) =>
        ((Work.Serre.cylShrink q p.1 (toCollar q b p.2) : ↥(Work.Serre.cylCollar q)) :
          Work.Serre.cyl q))
      = fun p => (((Work.Serre.cylShrinkHomotopy q) (p.1, toCollar q b p.2) :
          ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q) := by
      funext p
      exact congrArg Subtype.val (Work.Serre.cylShrinkHomotopy_apply q p.1 (toCollar q b p.2))
    have hcont : Continuous fun p : unitInterval × ↥(Ucol q b) =>
        ((Work.Serre.cylShrink q p.1 (toCollar q b p.2) : ↥(Work.Serre.cylCollar q)) :
          Work.Serre.cyl q) := by
      rw [hEq]
      exact continuous_subtype_val.comp ((Work.Serre.cylShrinkHomotopy q).continuous.comp
        (continuous_fst.prodMk ((toCollar q b).continuous.comp continuous_snd)))
    exact Continuous.subtype_mk (Continuous.subtype_mk hcont
      (fun p => Work.Serre.CMidCollar.cylShrink_mem_Mid q b p.1 p.2.1.2))
      (fun p => (Work.Serre.cylShrink q p.1 (toCollar q b p.2)).2)

/-- The shrink at time `1`, as a map `Ucol q b → cylBot q`. -/
def retrU (q : C(X, B)) (b : B) : C(↥(Ucol q b), ↥(Work.Serre.cylBot q)) :=
  (Work.Serre.cylShrinkToBot q).comp (toCollar q b)

@[simp] theorem retrU_apply (q : C(X, B)) (b : B) (y : ↥(Ucol q b)) :
    retrU q b y = Work.Serre.cylShrinkToBot q (toCollar q b y) := rfl

theorem retrU_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (retrU q b) (PUcol q b) (PBot q b) := by
  intro y hy
  show (Work.Serre.cylRetract q) ((Work.Serre.cylShrinkToBot q (toCollar q b y) :
      ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) ∈ ({b} : Set B)
  show (Work.Serre.cylRetract q) ((Work.Serre.cylShrink q 1 (toCollar q b y) :
      ↥(Work.Serre.cylCollar q)) : Work.Serre.cyl q) = b
  rw [Work.Serre.cylRetract_cylShrink]
  exact hy

/-- **The retraction is the identity on the bottom copy.** -/
theorem retrU_collarIncl (q : C(X, B)) (b : B) (u : ↥(Work.Serre.cylBot q)) :
    retrU q b (collarIncl q b u) = u := by
  have hfix := congrArg (fun z : ↥(Work.Serre.cylCollar q) => (z : Work.Serre.cyl q))
    (Work.Serre.cylShrink_fixes_bot q 1 (y := toCollar q b (collarIncl q b u)) u.2)
  exact Subtype.ext hfix

/-- The constant homotopy from `retrU ∘ collarIncl` to the identity of the bottom copy. -/
def homBot (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy ((retrU q b).comp (collarIncl q b))
      (ContinuousMap.id ↥(Work.Serre.cylBot q)) where
  toContinuousMap := ((retrU q b).comp (collarIncl q b)).comp ContinuousMap.snd
  map_zero_left := fun _ => rfl
  map_one_left := fun u => retrU_collarIncl q b u

theorem homBot_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {u : ↥(Work.Serre.cylBot q)}
    (hu : u ∈ PBot q b) : homBot q b (t, u) ∈ PBot q b := by
  rw [show homBot q b (t, u) = retrU q b (collarIncl q b u) from rfl, retrU_collarIncl q b u]
  exact hu

/-- The shrink of `Ucol q b` preserves the fibre cone `PUcol q b`. -/
theorem shrinkU_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {y : ↥(Ucol q b)}
    (hy : y ∈ PUcol q b) : shrinkU q b (t, y) ∈ PUcol q b := by
  have h : (((shrinkU q b (t, y) : ↥(Ucol q b)) : ↥(Work.Serre.CMid q b)) : Work.Serre.cyl q)
      = ((Work.Serre.cylShrink q t (toCollar q b y) : ↥(Work.Serre.cylCollar q)) :
          Work.Serre.cyl q) := rfl
  show (Work.Serre.cylRetract q)
    (((shrinkU q b (t, y) : ↥(Ucol q b)) : ↥(Work.Serre.CMid q b)) : Work.Serre.cyl q) = b
  rw [h, Work.Serre.cylRetract_cylShrink]
  exact hy

/-- **The shrink homotopy of `Ucol q b`**, from the identity to `collarIncl ∘ retrU`. -/
def shrinkUHomotopy (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(Ucol q b))
      ((collarIncl q b).comp (retrU q b)) where
  toContinuousMap := shrinkU q b
  map_zero_left := fun y => by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    show ((Work.Serre.cylShrink q 0 (toCollar q b y) : ↥(Work.Serre.cylCollar q)) :
        Work.Serre.cyl q) = ((y : ↥(Ucol q b)) : Work.Serre.cyl q)
    rw [← Work.Serre.cylShrinkHomotopy_apply q 0 (toCollar q b y)]
    exact congrArg Subtype.val ((Work.Serre.cylShrinkHomotopy q).map_zero_left (toCollar q b y))
  map_one_left := fun _ => rfl

/-- **The inclusion of the bottom copy into the collar is a homotopy equivalence of pairs**
`(cylBot q, PBot q b) → (Ucol q b, PUcol q b)`, hence an isomorphism on relative rational
homology. -/
theorem isIso_collarPairSucc (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PBot q b)
      (PUcol q b) (collarIncl q b) (collarIncl_mapsTo q b)) n) := by
  have hcomp₁ : Work.Serre.relChainsRPairMap (PBot q b) (PUcol q b)
        (collarIncl q b) (collarIncl_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (PUcol q b) (PBot q b) (retrU q b) (retrU_mapsTo q b)
      = Work.Serre.relChainsRPairMap (PBot q b) (PBot q b)
        ((retrU q b).comp (collarIncl q b)) ((retrU_mapsTo q b).comp (collarIncl_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (collarIncl q b) (retrU q b)
      (collarIncl_mapsTo q b) (retrU_mapsTo q b)
      (hg'' := (retrU_mapsTo q b).comp (collarIncl_mapsTo q b))
  have hcomp₂ : Work.Serre.relChainsRPairMap (PUcol q b) (PBot q b)
        (retrU q b) (retrU_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (PBot q b) (PUcol q b)
        (collarIncl q b) (collarIncl_mapsTo q b)
      = Work.Serre.relChainsRPairMap (PUcol q b) (PUcol q b)
        ((collarIncl q b).comp (retrU q b)) ((collarIncl_mapsTo q b).comp (retrU_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (retrU q b) (collarIncl q b)
      (retrU_mapsTo q b) (collarIncl_mapsTo q b)
      (hg'' := (collarIncl_mapsTo q b).comp (retrU_mapsTo q b))
  have h1 : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PBot q b)
        (PUcol q b) (collarIncl q b) (collarIncl_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PUcol q b)
        (PBot q b) (retrU q b) (retrU_mapsTo q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₁,
      Work.Serre.DiscPair.relPairHomotopic (A := PBot q b) (B := PBot q b)
        ((retrU_mapsTo q b).comp (collarIncl_mapsTo q b)) (fun _ hx => hx) (homBot q b)
        (fun t u hu => homBot_mapsTo q b t hu) n,
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (PBot q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  have h2 : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PUcol q b)
        (PBot q b) (retrU q b) (retrU_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PBot q b)
        (PUcol q b) (collarIncl q b) (collarIncl_mapsTo q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₂,
      ← Work.Serre.DiscPair.relPairHomotopic (A := PUcol q b) (B := PUcol q b)
        (f := ContinuousMap.id ↥(Ucol q b)) (fun _ hx => hx)
        ((collarIncl_mapsTo q b).comp (retrU_mapsTo q b)) (shrinkUHomotopy q b)
        (fun t x hx => shrinkU_mapsTo q b t hx) n,
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (PUcol q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  exact IsIso.mk ⟨_, h1, h2⟩

/-! ## The collapse comparison -/

/-- The inclusion `Ucol q b ↪ CMid q b`. -/
def inclUcolMid (q : C(X, B)) (b : B) :
    C(↥(Ucol q b), ↥(Work.Serre.CMid q b)) :=
  ⟨fun x => (x : ↥(Work.Serre.CMid q b)), continuous_subtype_val⟩

theorem inclUcolMid_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (inclUcolMid q b) (PUcol q b) (Pmid q b) := by
  intro x hx
  show (x : ↥(Work.Serre.CMid q b)) ∈ Pmid q b
  exact hx

/-- `relChainsRInclPairMap` is `relChainsRPairMap` of the inclusion of the subtype. -/
theorem relChainsRInclPairMap_eq_relChainsRPairMap (X : TopCat) (U A : Set X) :
    Work.Serre.relChainsRInclPairMap X U A
      = Work.Serre.relChainsRPairMap {x : ↥U | (x : X) ∈ A} A
          (⟨fun x => (x : X), continuous_subtype_val⟩ : C(↥U, X)) (fun _ hx => hx) := by
  unfold Work.Serre.relChainsRInclPairMap Work.Serre.relChainsRPairMap
  refine Work.Serre.CsrSharp.Tools.csrRelMapOf_congr rfl ?_ _ _
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext rfl

/-- The same bridge for the special case `(Ucol q b, PUcol q b) ⊆ (CMid q b, Pmid q b)`. -/
theorem relChainsRInclPairMap_mid_eq (q : C(X, B)) (b : B) :
    Work.Serre.relChainsRPairMap (PUcol q b) (Pmid q b) (inclUcolMid q b)
        (inclUcolMid_mapsTo q b)
      = Work.Serre.relChainsRInclPairMap (TopCat.of ↥(Work.Serre.CMid q b))
          (Ucol q b) (Pmid q b) := by
  rw [relChainsRInclPairMap_eq_relChainsRPairMap]
  unfold Work.Serre.relChainsRPairMap
  refine Work.Serre.CsrSharp.Tools.csrRelMapOf_congr rfl ?_ _ _
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext rfl

/-- **The collapse `C_*(X, q⁻¹b;ℚ) → C_*(CMid q b, P;ℚ)` is an isomorphism on rational homology.**
It factors through `(cylBot q, PBot q b)` (a homeomorphism of pairs) and `(Ucol q b, PUcol q b)`
(the collar shrink, a homotopy equivalence of pairs), and the last leg is the excision of the collar
with the "interiors cover" hypothesis. -/
theorem isIso_collapseMapSucc (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) n) := by
  haveI hA : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
      (q ⁻¹' ({b} : Set B)) (PBot q b) (botIncl q) (botIncl_mapsTo q b)) n) :=
    isIso_botPairSucc q b n
  haveI hB : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
      (PBot q b) (PUcol q b) (collarIncl q b) (collarIncl_mapsTo q b)) n) :=
    isIso_collarPairSucc q b n
  haveI hC : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (PUcol q b)
      (Pmid q b) (inclUcolMid q b) (inclUcolMid_mapsTo q b)) n) := by
    rw [relChainsRInclPairMap_mid_eq q b]
    exact Work.Serre.CylCMidVan.relChainsR_excisionInterior (Ucol q b) (Pmid q b)
      (interior_Pmid_union_Ucol q b) n
  have hcomp₁ : Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PBot q b)
        (botIncl q) (botIncl_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (PBot q b) (PUcol q b)
        (collarIncl q b) (collarIncl_mapsTo q b)
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PUcol q b)
        ((collarIncl q b).comp (botIncl q))
        ((collarIncl_mapsTo q b).comp (botIncl_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (botIncl q) (collarIncl q b)
      (botIncl_mapsTo q b) (collarIncl_mapsTo q b)
      (hg'' := (collarIncl_mapsTo q b).comp (botIncl_mapsTo q b))
  have hcomp₃ : Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PUcol q b)
        ((collarIncl q b).comp (botIncl q))
        ((collarIncl_mapsTo q b).comp (botIncl_mapsTo q b))
      ≫ Work.Serre.relChainsRPairMap (PUcol q b) (Pmid q b)
          (inclUcolMid q b) (inclUcolMid_mapsTo q b)
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (Pmid q b)
        ((inclUcolMid q b).comp ((collarIncl q b).comp (botIncl q)))
        ((inclUcolMid_mapsTo q b).comp
          ((collarIncl_mapsTo q b).comp (botIncl_mapsTo q b))) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp ((collarIncl q b).comp (botIncl q))
      (inclUcolMid q b) ((collarIncl_mapsTo q b).comp (botIncl_mapsTo q b))
      (inclUcolMid_mapsTo q b)
      (hg'' := (inclUcolMid_mapsTo q b).comp
        ((collarIncl_mapsTo q b).comp (botIncl_mapsTo q b)))
  have hgc : (inclUcolMid q b).comp ((collarIncl q b).comp (botIncl q))
      = Work.Serre.toCMid q b := by
    ext x
    rfl
  have heq : Work.Serre.collapseMap q b
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) (PBot q b)
          (botIncl q) (botIncl_mapsTo q b)
        ≫ Work.Serre.relChainsRPairMap (PBot q b) (PUcol q b)
          (collarIncl q b) (collarIncl_mapsTo q b)
        ≫ Work.Serre.relChainsRPairMap (PUcol q b) (Pmid q b)
          (inclUcolMid q b) (inclUcolMid_mapsTo q b) := by
    rw [← Category.assoc, hcomp₁, hcomp₃, Work.Serre.relChainsRPairMap_congr hgc _ _]
    rfl
  rw [heq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  infer_instance

/-! ## The retraction comparison -/

theorem cylRetract_cylMove' (q : C(X, B)) (y : Work.Serre.cyl q) (s : unitInterval) :
    Work.Serre.cylRetract q (Work.Serre.cylMove q (y, s)) = Work.Serre.cylRetract q y := by
  induction y using Quotient.inductionOn with
  | h z => rcases z with ⟨p, t⟩ | x <;> rfl

/-- **The retraction `C_*(cyl q, P;ℚ) → C_*(B, {b};ℚ)` is an isomorphism on rational homology**:
`cylRetract q` is a homotopy equivalence (`cylHomotopyEquivExplicit`) and so is its restriction to
the fibre `P`, which is contracted by the push-up homotopy `cylMove`. -/
theorem isIso_retractMapSucc (q : C(X, B)) (b : B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) n) := by
  refine Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso (Work.Serre.fibreSet q b)
    ({b} : Set B) (Work.Serre.cylRetract q) (fun _ hx => hx) n ?_ ?_
  · intro k
    obtain ⟨E, hE⟩ := Work.Serre.cylHomotopyEquivExplicit q
    have h := Work.Serre.IsRatHomologyIso.of_homotopyEquiv E k
    rwa [hE] at h
  · intro k
    let φ : C(↥(Work.Serre.fibreSet q b), ↥({b} : Set B)) :=
      Work.Serre.DiscPair.restrictPair (Work.Serre.fibreSet q b) ({b} : Set B)
        (Work.Serre.cylRetract q) (fun _ hx => hx)
    let ψ : C(↥({b} : Set B), ↥(Work.Serre.fibreSet q b)) :=
      ⟨fun _ => ⟨Work.Serre.cylInr q b, rfl⟩, continuous_const⟩
    have hφψ : (φ.comp ψ).Homotopic (ContinuousMap.id ↥({b} : Set B)) := by
      have h : φ.comp ψ = ContinuousMap.id ↥({b} : Set B) :=
        ContinuousMap.ext (fun x => Subsingleton.elim _ _)
      rw [h]
    have hψφ : (ψ.comp φ).Homotopic (ContinuousMap.id ↥(Work.Serre.fibreSet q b)) :=
      ⟨(ContinuousMap.Homotopy.symm
        { toContinuousMap :=
            ⟨fun p : unitInterval × ↥(Work.Serre.fibreSet q b) =>
                ⟨Work.Serre.cylMove q (p.2.1, p.1), by
                  show (Work.Serre.cylRetract q) (Work.Serre.cylMove q (p.2.1, p.1)) = b
                  rw [cylRetract_cylMove' q (p.2.1) p.1]
                  exact p.2.2⟩,
              Continuous.subtype_mk ((Work.Serre.cylMove q).continuous.comp
                ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
                (fun p => by
                  show (Work.Serre.cylRetract q) (Work.Serre.cylMove q (p.2.1, p.1)) = b
                  rw [cylRetract_cylMove' q (p.2.1) p.1]
                  exact p.2.2)⟩
          map_zero_left := fun y => by
            apply Subtype.ext
            show Work.Serre.cylMove q (y.1, 0) = y.1
            rw [Work.Serre.cylMove_zero]
          map_one_left := fun y => by
            apply Subtype.ext
            show Work.Serre.cylMove q (y.1, 1) = Work.Serre.cylInr q b
            rw [Work.Serre.cylMove_one]
            change Work.Serre.cylInr q (Work.Serre.cylRetract q y.1) = Work.Serre.cylInr q b
            rw [show Work.Serre.cylRetract q y.1 = b from y.2] })⟩
    have h := Work.Serre.IsRatHomologyIso.of_homotopyEquiv
      (ContinuousMap.HomotopyEquiv.mk φ ψ hψφ hφψ) k
    exact h

/-! ## The chain-level commuting square -/

/-- **The chain-level commuting square**: the collapse, the inclusion of the triple
`P ⊆ CMid q b ⊆ cyl q` and the retraction compose to the pair comparison map `relPairMapRat q b`. -/
theorem collapseMap_comp_retractMap' (q : C(X, B)) (b : B) :
    Work.Serre.collapseMap q b ≫ Work.Serre.inclMap q b ≫ Work.Serre.retractMap q b
      = Work.Serre.relPairMapRat q b := by
  have hIncl : Work.Serre.inclMap q b
      = Work.Serre.relChainsRPairMap {y : ↥(Work.Serre.CMid q b) |
            (y : Work.Serre.cyl q) ∈ Work.Serre.fibreSet q b} (Work.Serre.fibreSet q b)
          (⟨fun y => (y : Work.Serre.cyl q), continuous_subtype_val⟩ :
            C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
          (by intro y hy; exact hy) := rfl
  rw [hIncl, Work.Serre.collapseMap, Work.Serre.retractMap]
  rw [Work.Serre.csrPairFunctoriality
        (⟨fun y => (y : Work.Serre.cyl q), continuous_subtype_val⟩ :
          C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
        (Work.Serre.cylRetract q) (by intro y hy; exact hy) (by intro x hx; exact hx)]
  rw [Work.Serre.csrPairFunctoriality (Work.Serre.toCMid q b)
        ((Work.Serre.cylRetract q).comp
          (⟨fun y => (y : Work.Serre.cyl q), continuous_subtype_val⟩ :
            C(↥(Work.Serre.CMid q b), Work.Serre.cyl q)))
        (by intro x hx; exact hx) (by intro y hy; exact hy)]
  have hmap : ((Work.Serre.cylRetract q).comp
        (⟨fun y => (y : Work.Serre.cyl q), continuous_subtype_val⟩ :
          C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))).comp
        (Work.Serre.toCMid q b) = q := by
    ext x
    exact DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x
  rw [show Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) ({b} : Set B)
        (((Work.Serre.cylRetract q).comp
          (⟨fun y => (y : Work.Serre.cyl q), continuous_subtype_val⟩ :
            C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))).comp
          (Work.Serre.toCMid q b)) _
      = Work.Serre.relChainsRPairMap (q ⁻¹' ({b} : Set B)) ({b} : Set B) q _ from
    Work.Serre.relChainsRPairMap_congr hmap _ _]
  rfl

/-- **The cofibre decomposition of the pair `(cyl q, CMid q b)` in degree `r+1`.**

`CMid q b = range (cylIncl q) ∪ (cylRetract q)⁻¹{b}` is the union of the bottom copy `A ≅ X` of the
mapping cylinder with the fibre cone over `b` (`≅ C(q⁻¹b)`), and `relPairMapRat q b` is the map of
pairs `(X, q⁻¹b) → (B, {b})` induced by `q` on relative rational chains.  The homology of the pair
`(cyl q, CMid q b)` is the homology of the cofibre of that map, i.e. it splits (over the field `ℚ`)
as the product of the cokernel in degree `r+1` and the kernel in degree `r`:

  `H_{r+1}(cyl q, CMid q b; ℚ) ≅ coker(f_{r+1}) × ker(f_r)`,  `f = relPairMapRat q b`.

This is the point case (`S = {b}`) of `Work.Serre.DiscPair.cylPairCofibre`, which proves the same
decomposition with the same proof for the pair-set `(cylRetract q) ⁻¹' S ∪ range (cylIncl q)`,
`S = range (attachIncl …)`; that proof does not use either its fibration hypothesis or the
attachment structure of `S`.  It is also the `n = r + 1` case of
`Work.Serre.CylCMidVan.cylCMidHomologyDecomp`.  For a Serre fibration with fibre rationally `S^r`
through degree `N` (`r ≤ N`) one has `f_{r+1}` surjective (`Work.Serre.ratPairComparisonOneBoundary`)
and `f_r` invertible (`Work.Serre.B1Rel.relPairMapRat_isIso`), so this decomposition computes the
vanishing `H_{r+1}(cyl q, CMid q b; ℚ) = 0`. -/
theorem cylCMidHomologyDecompSucc (r : ℕ) (hr : 1 ≤ r)
    {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b : B) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        (Work.Serre.CMid q b)).homology (r + 1)) ≅
      ModuleCat.of ℚ (↥(CategoryTheory.Limits.cokernel (HomologicalComplex.homologyMap
            (Work.Serre.relPairMapRat q b) (r + 1))) ×
        ↥(CategoryTheory.Limits.kernel (HomologicalComplex.homologyMap
            (Work.Serre.relPairMapRat q b) r)))) := by
  -- the triple `P ⊆ CMid q b ⊆ cyl q`
  let S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.Serre.RatTower.tripleShortR (TopCat.of (Work.Serre.cyl q)) (Work.Serre.fibreSet q b)
      (Work.Serre.CMid q b) Set.subset_union_right
  have hS : S.ShortExact := Work.Serre.RatTower.tripleShortR_shortExact _ _ _ _
  have hrel : (ComplexShape.down ℕ).Rel (r + 1) r := by simp [ComplexShape.down]
  -- the two comparison quasi-isomorphisms
  haveI hc₁ : IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1)) :=
    isIso_collapseMapSucc q b (r + 1)
  haveI hc₂ : IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r) :=
    isIso_collapseMapSucc q b r
  haveI hr₁ : IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1)) :=
    isIso_retractMapSucc q b (r + 1)
  haveI hr₂ : IsIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r) :=
    isIso_retractMapSucc q b r
  -- the maps of the long exact sequence of the triple and the comparison maps
  let α := HomologicalComplex.homologyMap S.f (r + 1)
  let β := HomologicalComplex.homologyMap S.g (r + 1)
  let δ := hS.δ (r + 1) r hrel
  let γ := HomologicalComplex.homologyMap S.f r
  let e₁ := asIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1))
  let e₂ := asIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1))
  let e₁' := asIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r)
  let e₂' := asIso (HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r)
  let f₁ := HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) (r + 1)
  let f₂ := HomologicalComplex.homologyMap (Work.Serre.relPairMapRat q b) r
  -- the chain level square
  have hsquare : Work.Serre.collapseMap q b ≫ S.f ≫ Work.Serre.retractMap q b
      = Work.Serre.relPairMapRat q b := collapseMap_comp_retractMap' q b
  -- the two commuting squares on homology
  have hsq : e₁.hom ≫ α ≫ e₂.hom = f₁ := by
    show HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) (r + 1)
        ≫ HomologicalComplex.homologyMap S.f (r + 1)
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) (r + 1) = _
    erw [← HomologicalComplex.homologyMap_comp (φ := S.f)
      (ψ := Work.Serre.retractMap q b) (i := r + 1)]
    erw [← HomologicalComplex.homologyMap_comp (φ := Work.Serre.collapseMap q b)
      (ψ := (S.f ≫ Work.Serre.retractMap q b)) (i := r + 1)]
    rw [hsquare]
  have hsq' : e₁'.hom ≫ γ ≫ e₂'.hom = f₂ := by
    show HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) r
        ≫ HomologicalComplex.homologyMap S.f r
        ≫ HomologicalComplex.homologyMap (Work.Serre.retractMap q b) r = _
    erw [← HomologicalComplex.homologyMap_comp (φ := S.f)
      (ψ := Work.Serre.retractMap q b) (i := r)]
    erw [← HomologicalComplex.homologyMap_comp (φ := Work.Serre.collapseMap q b)
      (ψ := (S.f ≫ Work.Serre.retractMap q b)) (i := r)]
    rw [hsquare]
  -- the corresponding submodules
  have hrange : (LinearMap.range α.hom).map e₂.hom.hom = LinearMap.range f₁.hom := by
    have hrange_e₁ : (e₁.hom.hom).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      exact ⟨e₁.inv.hom y, Iso.inv_hom_id_apply e₁ y⟩
    have hLM : ModuleCat.Hom.hom f₁ = (ModuleCat.Hom.hom e₂.hom).comp
        ((ModuleCat.Hom.hom α).comp (ModuleCat.Hom.hom e₁.hom)) := by
      erw [← hsq, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
    erw [hLM, LinearMap.range_comp, LinearMap.range_comp, hrange_e₁, Submodule.map_top]
    rfl
  have hker : (LinearMap.ker γ.hom).map e₁'.inv.hom = LinearMap.ker f₂.hom := by
    have hLM : ModuleCat.Hom.hom f₂ = (ModuleCat.Hom.hom e₂'.hom).comp
        ((ModuleCat.Hom.hom γ).comp (ModuleCat.Hom.hom e₁'.hom)) := by
      erw [← hsq', ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
    rw [hLM]
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show (ModuleCat.Hom.hom e₂'.hom) ((ModuleCat.Hom.hom γ)
        ((ModuleCat.Hom.hom e₁'.hom) ((ModuleCat.Hom.hom e₁'.inv) y))) = 0
      rw [Iso.inv_hom_id_apply e₁' y, hy]
      exact map_zero _
    · intro hy
      have hy' : (ModuleCat.Hom.hom e₂'.hom) ((ModuleCat.Hom.hom γ)
          ((ModuleCat.Hom.hom e₁'.hom) x)) = 0 := hy
      refine ⟨(ModuleCat.Hom.hom e₁'.hom) x, ?_, Iso.hom_inv_id_apply e₁' x⟩
      have h2 := congrArg (ModuleCat.Hom.hom e₂'.inv) hy'
      rw [Iso.hom_inv_id_apply e₂' ((ModuleCat.Hom.hom γ)
        ((ModuleCat.Hom.hom e₁'.hom) x))] at h2
      show (ModuleCat.Hom.hom γ) ((ModuleCat.Hom.hom e₁'.hom) x) = 0
      have h3 : (ModuleCat.Hom.hom e₂'.inv) 0 = 0 := map_zero _
      rw [h3] at h2
      exact h2
  -- the splitting of the exact fragment
  obtain ⟨e₀⟩ := Work.Serre.DiscPair.linearEquiv_prod_of_exact α.hom β.hom δ.hom γ.hom
    (hS.homology_exact₂ (r + 1)).moduleCat_range_eq_ker
    (hS.homology_exact₃ (r + 1) r hrel).moduleCat_range_eq_ker
    (hS.homology_exact₁ (r + 1) r hrel).moduleCat_range_eq_ker
  have eC : (↥((S.X₂).homology (r + 1)) ⧸ LinearMap.range α.hom) ≃ₗ[ℚ]
      (↥((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B)).homology (r + 1))
        ⧸ LinearMap.range f₁.hom) :=
    Submodule.Quotient.equiv (LinearMap.range α.hom) (LinearMap.range f₁.hom)
      e₂.toLinearEquiv hrange
  have eK : ↥(LinearMap.ker γ.hom) ≃ₗ[ℚ] ↥(LinearMap.ker f₂.hom) :=
    LinearEquiv.ofSubmodules e₁'.toLinearEquiv.symm (LinearMap.ker γ.hom)
      (LinearMap.ker f₂.hom) hker
  exact ⟨((e₀.trans (eC.prodCongr eK)).trans
    (((ModuleCat.cokernelIsoRangeQuotient f₁).toLinearEquiv.prodCongr
      (ModuleCat.kernelIsoKer f₂).toLinearEquiv).symm)).toModuleIso⟩

end

end Work.RatHurewicz
