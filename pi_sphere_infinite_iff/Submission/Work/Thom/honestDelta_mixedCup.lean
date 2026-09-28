/-
# The mixed cup product commutes with the Mayer–Vietoris connecting map

For a topological space `X`, a subset `A ⊆ X` and an open cover `X = U ∪ V`, the honest
Mayer–Vietoris connecting map `Work.Cohomology.honestDelta` is compatible with the cup product
with a relative class `b ∈ H^n(X,A)`:

  `δ∅(u) ⌣ b = δ_A (u ⌣ b|_{U∩V})`   for `u ∈ H^k(U∩V)`,

where `δ∅` is the connecting map of the pair `(X,∅)`, `δ_A` that of the pair `(X,A)`, and `⌣` is
the mixed cup product `Work.Cohomology.mixedCupC` (the module structure of the relative
cohomology over the absolute one).

The proof is by the snake lemma.  Fix a cocycle representative `t` of `b`.  On a class `[c]` of a
cocycle `c` of the overlap the right hand side is `δ_A([c ⌣ t|_{U∩V}])`, and on the left hand side
`δ∅([c]) = [w]` where `w` is the top element of the snake datum of `(cmW ∅)(c)`.  Cupping with `t`
is a morphism of the small Mayer–Vietoris complexes of degree `n` (`Work.Thom.cupSES`), so it maps
the snake datum `(zt, w)` of the `∅`-side to the snake datum `(cupMid zt, cupTop w)` of the
`A`-side; the two sides of the identity are therefore the two ends of the same snake computation,
the only substantive input being the compatibility of the comparison maps `cmpX`, `cmpW` with the
cup product (`Work.Thom.cupCmpRestrictTop`, `Work.Thom.cupCmpRestrictOvl`) and the description of
`Ttop` on the small cochain model (`Work.Thom.Ttop_cyclesMk`).
-/
import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.cupDeltaMaps
import Submission.Work.Thom.cupRightLM_dcomm
import Submission.Work.Thom.tau1LM_dcomm
import Submission.Work.Thom.relRestrCochain_dcocycle
import Submission.Work.Thom.alphaU_tau1
import Submission.Work.Thom.cupSESChain
import Submission.Work.Thom.cupCmpRestrictTop
import Submission.Work.Thom.cupCmpRestrictOvl
import Submission.Work.Thom.Ttop_cyclesMk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Thom

open Work.Cohomology

noncomputable section

/-! ## 1. Bookkeeping for homology classes -/

/-- **The composite of `ofHom (toSpanSingleton a)` with a morphism**: a morphism out of `ℤ` is
determined by the image of `1`. -/
lemma ofHom_toSpanSingleton_comp {M N : ModuleCat ℤ} (a : M) (g : M ⟶ N) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M a) ≫ g
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ N (ModuleCat.Hom.hom g a)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply]
  simp

variable {K L : CochainComplex (ModuleCat ℤ) ℕ}

/-- The `d`-form of the relative cocycle condition is the `relDiffLM`-form. -/
lemma relComplex_d_eq_zero_iff_relDiffLM {X : TopCat} {A : Set X} {n : ℕ}
    (x : (relComplex ℤ X A).X n) :
    ModuleCat.Hom.hom ((relComplex ℤ X A).d n (n+1)) x = 0 ↔ relDiffLM ℤ X A n x = 0 := by
  rw [Work.Cohomology.relComplex_d_apply]

/-- **The class of a cycle under a morphism of complexes.** -/
lemma homologyMap_cocycleOfK (φ : K ⟶ L) (i : ℕ) (x : K.X i)
    (hx : ModuleCat.Hom.hom (K.d i (i+1)) x = 0)
    (hx' : ModuleCat.Hom.hom (L.d i (i+1)) (ModuleCat.Hom.hom (φ.f i) x) = 0) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)
        ((K.homologyπ i) (cocycleOfK K x hx))
      = (L.homologyπ i) (cocycleOfK L (ModuleCat.Hom.hom (φ.f i) x) hx') := by
  have h1 : (K.homologyπ i ≫ HomologicalComplex.homologyMap φ i)
      = (HomologicalComplex.cyclesMap φ i ≫ L.homologyπ i) :=
    HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) =>
    ModuleCat.Hom.hom g (cocycleOfK K x hx)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]
  congr 1
  have hii := congrArg (fun (g : K.cycles i ⟶ L.X i) => ModuleCat.Hom.hom g
    (cocycleOfK K x hx)) (HomologicalComplex.cyclesMap_i φ i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hii
  refine (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance ?_
  rw [hii, iCycles_cocycleOfK]
  exact (iCycles_cocycleOfK L (ModuleCat.Hom.hom (φ.f i) x) hx').symm

/-- **Transport of a homology class along an equality of degrees.** -/
lemma eqToHom_homology_cocycleOfK (K : CochainComplex (ModuleCat ℤ) ℕ) {a b : ℕ} (h : a = b)
    (y : K.X a) (hy : ModuleCat.Hom.hom (K.d a (a+1)) y = 0)
    (hy' : ModuleCat.Hom.hom (K.d b (b+1)) ((K.XIsoOfEq h).hom y) = 0) :
    (K.homologyπ b) (cocycleOfK K ((K.XIsoOfEq h).hom y) hy')
      = CategoryTheory.eqToHom (congrArg (fun m => K.homology m) h)
          ((K.homologyπ a) (cocycleOfK K y hy)) := by
  cases h
  simp

/-- **Degree transports commute with the comparison isomorphism** `cmpXIso`. -/
lemma eqToHom_cmpXIso_inv (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {a b : ℕ} (h : a = b) :
    (cmpXIso X A U V hU hV hcov b).inv
        ≫ CategoryTheory.eqToHom
            (congrArg (fun m => (relComplex ℤ X A).homology m) h.symm)
      = CategoryTheory.eqToHom
          (congrArg (fun m => (dualComplex ℤ (relMVTopC X A U V)).homology m) h.symm)
        ≫ (cmpXIso X A U V hU hV hcov a).inv := by
  cases h
  simp


/-- The combined degree-transport compatibility with `cmpXIso`. -/
lemma eqToHom_cmpXIso_inv_comp (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {a b : ℕ} (h : a = b) :
    CategoryTheory.eqToHom
        (congrArg (fun m => (dualComplex ℤ (relMVTopC X A U V)).homology m) h)
        ≫ (cmpXIso X A U V hU hV hcov b).inv
        ≫ CategoryTheory.eqToHom
            (congrArg (fun m => (relComplex ℤ X A).homology m) h.symm)
      = (cmpXIso X A U V hU hV hcov a).inv := by
  cases h
  simp

/-- The relative cohomology class of a cocycle, as the class of the associated cycle. -/
lemma relClassOf_eq_homologyπ (X : TopCat) (A : Set X) {n : ℕ} (a : relKern ℤ X A n)
    (h : relDiffLM ℤ X A n a = 0) :
    relClassOf ℤ X A a h
      = (relComplex ℤ X A).homologyπ n (cocycleOfK (relComplex ℤ X A) a
          (show ModuleCat.Hom.hom ((relComplex ℤ X A).d n (n+1)) a = 0 by
            rw [Work.Cohomology.relComplex_d]; exact h)) := rfl

/-- The restriction of a relative class to the overlap, on the class of a cocycle. -/
lemma relRestrOvl_relClassOf (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((relComplex ℤ X A).X n)) (ht : relDiffLM ℤ X A n t = 0)
    (h' : relDiffLM ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) n
      (relRestrCochain A (U ∩ V) n t) = 0) :
    TsqH.relRestrOvl X A U V n (relClassOf ℤ X A t ht)
      = relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
          (relRestrCochain A (U ∩ V) n t) h' := by
  rw [relClassOf_eq_homologyπ (X := TopCat.of ↑X) (A := A) t ht,
    relClassOf_eq_homologyπ (X := TopCat.of ↥(U ∩ V)) (A := interAU A (U ∩ V))
      (relRestrCochain A (U ∩ V) n t) h']
  rw [TsqH.relRestrOvl]
  simp only [Work.Thom.relCohMap]
  have h1 : ModuleCat.Hom.hom ((relComplex ℤ X A).d n (n+1)) t = 0 := by
    rw [relComplex_d]; exact ht
  have h2 : ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of ↥(U ∩ V))
      (interAU A (U ∩ V))).d n (n+1)) (relRestrCochain A (U ∩ V) n t) = 0 := by
    rw [relComplex_d]; exact h'
  exact homologyMap_cocycleOfK _ n t h1 h2

/-- **`Tov` on the class of a cocycle of the overlap** is the honest mixed cup product. -/
lemma Tov_relClassOf (X : TopCat) (A U V : Set X) (n k : ℕ)
    (t : ↥((relComplex ℤ X A).X n)) (ht : relDiffLM ℤ X A n t = 0)
    (c : relKern ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) k)
    (hc : relDiffLM ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) k c = 0)
    (h' : relDiffLM ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) n
      (relRestrCochain A (U ∩ V) n t) = 0)
    (hca : relDiffLM ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) (k+n)
      ((cupRightLM (relRestrCochain A (U ∩ V) n t) (interAU ∅ (U ∩ V)) k) c) = 0) :
    TsqH.Tov X A U V n (relClassOf ℤ X A t ht) k
        (relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)
      = relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
          ((cupRightLM (relRestrCochain A (U ∩ V) n t) (interAU ∅ (U ∩ V)) k) c) hca := by
  show (LinearMap.applyₗ (TsqH.relRestrOvl X A U V n (relClassOf ℤ X A t ht)))
      (mixedCupC ℤ (interAU A (U ∩ V)) k n
        ((pdCohIso ↥(U ∩ V) k).hom
          (relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)))
    = relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
        ((cupRightLM (relRestrCochain A (U ∩ V) n t) (interAU ∅ (U ∩ V)) k) c) hca
  rw [show (pdCohIso ↥(U ∩ V) k).hom
        (relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) c.1
          (relClassOf_cochainDiff ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)
      from relToAbs_relClassOf (X := ↥(U ∩ V)) (∅ : Set ↥(U ∩ V)) c hc]
  rw [relRestrOvl_relClassOf X A U V n t ht h']
  rw [mixedCupC_eq_mixedCup]
  change mixedCup (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) k n
      (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) c.1
        (relClassOf_cochainDiff ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc))
      (relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
        (relRestrCochain A (U ∩ V) n t) h')
    = relClassOf ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
        ((cupRightLM (relRestrCochain A (U ∩ V) n t) (interAU ∅ (U ∩ V)) k) c) hca
  rw [(Work.Cohomology.mixedCup_apply (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) k n c.1
    (relRestrCochain A (U ∩ V) n t)
    (relClassOf_cochainDiff ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)
    h').choose_spec.choose_spec]
  exact Work.Cohomology.relClassOf_congr ℤ (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V))
    (Work.Cohomology.mixedCup_apply (TopCat.of ↥(U ∩ V)) (interAU A (U ∩ V)) k n c.1
      (relRestrCochain A (U ∩ V) n t)
      (relClassOf_cochainDiff ℤ (TopCat.of ↥(U ∩ V)) (interAU ∅ (U ∩ V)) c hc)
      h').choose_spec.choose
    hca
    (Subtype.ext (by rw [Work.Thom.cupRightLM_apply]))

/-- **The Mayer–Vietoris connecting map on the class of a cycle**, via snake data. -/
theorem hmvδ_apply (X : TopCat) (A U V : Set X) (k : ℕ)
    (z : (dualComplex ℤ (relMVUV X A U V)).X k)
    (hz : (dualComplex ℤ (relMVUV X A U V)).d k (k+1) z = 0)
    (zt : ((dualComplex ℤ (relMVUU X A U V)) ⊞
      (dualComplex ℤ (relMVVV X A U V))).X k)
    (hzt : ModuleCat.Hom.hom ((hmvG X A U V).f k) zt = z)
    (w : (dualComplex ℤ (relMVTopC X A U V)).X (k+1))
    (hw : ModuleCat.Hom.hom ((hmvF X A U V).f (k+1)) w
      = ModuleCat.Hom.hom (((dualComplex ℤ (relMVUU X A U V)) ⊞
          (dualComplex ℤ (relMVVV X A U V))).d k (k+1)) zt)
    (hwc : (dualComplex ℤ (relMVTopC X A U V)).d (k+1) (k+2) w = 0) :
    ModuleCat.Hom.hom ((hmv_shortExact X A U V).δ k (k+1) (relCohMVUpRel k))
        (ModuleCat.Hom.hom ((dualComplex ℤ (relMVUV X A U V)).homologyπ k)
          (cocycleOfK _ z hz))
      = ModuleCat.Hom.hom ((dualComplex ℤ (relMVTopC X A U V)).homologyπ (k+1))
          (cocycleOfK _ w hwc) := by
  let D₃ := dualComplex ℤ (relMVUV X A U V)
  let D₂ := (dualComplex ℤ (relMVUU X A U V)) ⊞ (dualComplex ℤ (relMVVV X A U V))
  let D₁ := dualComplex ℤ (relMVTopC X A U V)
  have hx₃ : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₃.X k) z) ≫ D₃.d k (k+1) = 0 := by
    have hz' : ModuleCat.Hom.hom (D₃.d k (k+1)) z = 0 := hz
    rw [ofHom_toSpanSingleton_comp, hz', LinearMap.toSpanSingleton_zero, ModuleCat.ofHom_zero]
  have hx₂ : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₂.X k) zt)
      ≫ (hmvG X A U V).f k
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₃.X k) z) := by
    rw [ofHom_toSpanSingleton_comp, hzt]
  have hx₁ : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₁.X (k+1)) w)
      ≫ (hmvF X A U V).f (k+1)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₂.X k) zt) ≫ D₂.d k (k+1) := by
    rw [ofHom_toSpanSingleton_comp, hw]
    exact (ofHom_toSpanSingleton_comp zt (D₂.d k (k+1))).symm
  have hδ := CategoryTheory.ShortComplex.ShortExact.δ_eq
    (hS := hmv_shortExact X A U V) k (k+1)
    (relCohMVUpRel k)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₃.X k) z)) hx₃
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₂.X k) zt)) hx₂
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (D₁.X (k+1)) w)) hx₁
    (k+2) ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (k+1) (k+2) rfl))
  have hδ' := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ D₁.homology (k+1)) =>
    ModuleCat.Hom.hom g 1) hδ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hδ'
  simp only [D₁, D₂, D₃] at hδ' ⊢
  rw [cocycleOfK, cocycleOfK]
  exact hδ'

/-- `Ttop` on the classes of honest relative cocycles is the honest mixed cup. -/
theorem Ttop_relClassOf (X : TopCat) (A U V : Set X) (n j : ℕ)
    (t : ↥((relComplex ℤ X A).X n))
    (ht : relDiffLM ℤ X A n t = 0)
    (α : ↥((relComplex ℤ X ∅).X j))
    (hα : relDiffLM ℤ X ∅ j α = 0) :
    TsqH.Ttop X A n (relClassOf ℤ X A t ht) j (relClassOf ℤ X ∅ α hα)
      = relClassOf ℤ X A
          ⟨cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
            cup_mem_relKern_right ℤ X A α.1 t.2⟩
          ((mixedCup_apply (TopCat.of X) A j n α.1 t
            (relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose) := by
  show (LinearMap.applyₗ (relClassOf ℤ X A t ht))
      (mixedCupC ℤ A j n ((pdCohIso X j).hom (relClassOf ℤ X ∅ α hα)))
    = relClassOf ℤ X A
        ⟨cup ℤ (TopCat.toSSet.obj X) α.1 t.1, cup_mem_relKern_right ℤ X A α.1 t.2⟩
        ((mixedCup_apply (TopCat.of X) A j n α.1 t
          (relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose)
  rw [show (pdCohIso X j).hom (relClassOf ℤ X ∅ α hα)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj X) α.1
          (relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) from
    relToAbs_relClassOf (X := ↑X) (∅ : Set ↑X) α hα]
  rw [mixedCupC_eq_mixedCup]
  exact (mixedCup_apply (TopCat.of X) A j n α.1 t
    (relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose_spec


/-- The homology class of `cocycleOfK` depends only on the underlying element. -/
lemma homologyπ_cocycleOfK_congr (K : CochainComplex (ModuleCat ℤ) ℕ) {i : ℕ} (x x' : K.X i)
    (h : x = x')
    (hx : ModuleCat.Hom.hom (K.d i (i+1)) x = 0)
    (hx' : ModuleCat.Hom.hom (K.d i (i+1)) x' = 0) :
    (K.homologyπ i) (cocycleOfK K x hx) = (K.homologyπ i) (cocycleOfK K x' hx') := by
  subst h
  exact congrArg (fun h => (K.homologyπ i) (cocycleOfK K x h)) (Subsingleton.elim hx hx')

theorem honestDelta_mixedCup (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) (b : Work.Thom.RelCoh ℤ n X A) (k : ℕ) :
    (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.honestDelta X (∅ : Set X) U V hU hV hcov k)
        (Work.Thom.TsqH.Ttop X A n b (k + 1)))
      = (CategoryTheory.CategoryStruct.comp
          (Work.Thom.TsqH.Tov X A U V n b k)
          (CategoryTheory.CategoryStruct.comp
            (Work.Cohomology.honestDelta X A U V hU hV hcov (k + n))
            (CategoryTheory.eqToHom (congrArg (fun m => Work.Cohomology.pdCoh X A m)
              (by omega : k + n + 1 = (k + 1) + n))))) := by
  obtain ⟨t, ht, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ X A n b
  have hdt : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) A t ht
  have hkn : (k+1)+n = k+n+1 := Nat.add_right_comm k 1 n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨c, hc, hcu⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of ↥(U ∩ V))
    (Work.Cohomology.interAU ∅ (U ∩ V)) k u
  rw [← hcu]
  have hcocy : (Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU ∅ (U ∩ V))).d k (k+1) c = 0 := by
    rw [Work.Cohomology.relComplex_d]; exact hc
  set z : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X ∅ U V)).X k :=
    (Work.Cohomology.cmpW X ∅ U V).f k c with hzdef
  have hz : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X ∅ U V)).d k (k+1) z = 0 := by
    have hcomm := congrArg (fun (g : (Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU ∅ (U ∩ V))).X k ⟶ (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relMVUV X ∅ U V)).X (k+1)) => g c)
      (HomologicalComplex.Hom.comm (Work.Cohomology.cmpW X ∅ U V) k (k+1))
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [hcocy, map_zero] at hcomm
    simpa [hzdef] using hcomm
  obtain ⟨zt, w, hzt, hw, hwd⟩ := exists_snake_data X ∅ U V k z hz
  have hzt' : (Work.Cohomology.hmvG X A U V).f (k+n) (cupMid X A U V n k t.1 t.2 zt)
      = cupUV X A U V n k t.1 t.2 z := by
    rw [cup_hmvG X A U V n k t.1 t.2 zt]
    exact congrArg (fun y => (cupUV X A U V n k t.1 t.2) y) hzt
  have hmid : ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
        (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).d (k+n) ((k+1)+n)
        (cupMid X A U V n k t.1 t.2 zt)
      = cupMid X A U V n (k+1) t.1 t.2
          ((((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X ∅ U V)) ⊞
            (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X ∅ U V))).d k (k+1)) zt) := by
    have hcomm := congrArg (fun (g : ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X ∅ U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X ∅ U V))).X k ⟶ ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))).X ((k+1)+n)) => g zt)
      (cupMid_d_comm X A U V n t.1 t.2 hdt k)
    simp only [ConcreteCategory.comp_apply] at hcomm
    exact hcomm
  have hw' : (Work.Cohomology.hmvF X A U V).f ((k+1)+n)
      (cupTop X A U V n (k+1) t.1 t.2 w)
      = ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).d (k+n) ((k+1)+n)
        (cupMid X A U V n k t.1 t.2 zt) := by
    rw [cup_hmvF X A U V n (k+1) t.1 t.2 w, hw]
    exact hmid.symm
  have htop_d : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).d
      ((k+1)+n) (((k+1)+1)+n) (cupTop X A U V n (k+1) t.1 t.2 w)
      = cupTop X A U V n (k+2) t.1 t.2
          (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).d
            (k+1) (k+2)) w) := by
    have hcomm := congrArg (fun (g : (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X ∅ U V)).X (k+1) ⟶ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)).X (((k+1)+1)+n)) => g w)
      (cupTop_d_comm X A U V n t.1 t.2 hdt (k+1))
    simp only [ConcreteCategory.comp_apply] at hcomm
    exact hcomm
  have hcw : (Work.Cohomology.dualComplex ℤ
      (Work.Cohomology.relMVTopC X A U V)).d ((k+1)+n) (((k+1)+n)+1)
      (cupTop X A U V n (k+1) t.1 t.2 w) = 0 := by
    have hmono : Mono ((Work.Cohomology.hmvF X A U V).f (((k+1)+n)+1)) := by
      have hSd := (HomologicalComplex.shortExact_iff_degreewise_shortExact
        (ShortComplex.mk (Work.Cohomology.hmvF X A U V) (Work.Cohomology.hmvG X A U V)
          (Work.Cohomology.hmv_comp X A U V))).1 (Work.Cohomology.hmv_shortExact X A U V)
        (((k+1)+n)+1)
      exact hSd.mono_f
    apply (ModuleCat.mono_iff_injective
      ((Work.Cohomology.hmvF X A U V).f (((k+1)+n)+1))).mp hmono
    rw [map_zero]
    have hcomm := congrArg (fun (g : (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)).X ((k+1)+n) ⟶
        ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).X (((k+1)+n)+1)) =>
        g (cupTop X A U V n (k+1) t.1 t.2 w))
      (HomologicalComplex.Hom.comm (Work.Cohomology.hmvF X A U V) ((k+1)+n) (((k+1)+n)+1))
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [← hcomm, hw']
    exact congrArg (fun (g : ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))).X (k+n) ⟶ ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))).X (((k+1)+n)+1)) =>
        g (cupMid X A U V n k t.1 t.2 zt))
      (HomologicalComplex.d_comp_d ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))) (k+n) ((k+1)+n) (((k+1)+n)+1))
  have hE4 : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d
      (k+n) ((k+1)+n) (cupUV X A U V n k t.1 t.2 z) = 0 := by
    have hcomm := congrArg (fun (g : (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUV X ∅ U V)).X k ⟶ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUV X A U V)).X ((k+1)+n)) => g z)
      (cupUV_d_comm X A U V n t.1 t.2 hdt k)
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [hz, map_zero] at hcomm
    exact hcomm
  have hE4' : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d
      (k+n) (k+n+1) (cupUV X A U V n k t.1 t.2 z) = 0 := by
    have hdd : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d
        (k+n) (k+n+1)
        = (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d (k+n) ((k+1)+n)
          ≫ (HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relMVUV X A U V)) hkn).hom :=
      (HomologicalComplex.d_comp_XIsoOfEq_hom (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUV X A U V)) hkn (k+n)).symm
    rw [hdd, ConcreteCategory.comp_apply, hE4, map_zero]
  have hx₁_d : (HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)) hkn).hom
      (cupTop X A U V n (k+1) t.1 t.2 w)
      = (HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)) hkn).hom
      (cupTop X A U V n (k+1) t.1 t.2 w) := rfl
  have hx₁ : (Work.Cohomology.hmvF X A U V).f (k+n+1)
      ((HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)) hkn).hom
        (cupTop X A U V n (k+1) t.1 t.2 w))
      = ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).d (k+n) (k+n+1)
        (cupMid X A U V n k t.1 t.2 zt) := by
    have key := congrArg (fun (g : (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)).X ((k+1)+n) ⟶
        ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).X (k+n+1)) =>
        g (cupTop X A U V n (k+1) t.1 t.2 w))
      (HomologicalComplex.XIsoOfEq_hom_naturality (Work.Cohomology.hmvF X A U V) hkn)
    simp only [ConcreteCategory.comp_apply] at key
    rw [hw'] at key
    rw [← key]
    have hdd : ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).d (k+n) (k+n+1)
        = ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
            (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).d (k+n) ((k+1)+n)
          ≫ (HomologicalComplex.XIsoOfEq ((Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relMVVV X A U V))) hkn).hom :=
      (HomologicalComplex.d_comp_XIsoOfEq_hom ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))) hkn (k+n)).symm
    rw [hdd, ConcreteCategory.comp_apply]
  have hx₁c : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).d
      (k+n+1) (k+n+2)
      ((HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)) hkn).hom
        (cupTop X A U V n (k+1) t.1 t.2 w)) = 0 := by
    have hmono : Mono ((Work.Cohomology.hmvF X A U V).f (k+n+2)) := by
      have hSd := (HomologicalComplex.shortExact_iff_degreewise_shortExact
        (ShortComplex.mk (Work.Cohomology.hmvF X A U V) (Work.Cohomology.hmvG X A U V)
          (Work.Cohomology.hmv_comp X A U V))).1 (Work.Cohomology.hmv_shortExact X A U V)
        (k+n+2)
      exact hSd.mono_f
    apply (ModuleCat.mono_iff_injective ((Work.Cohomology.hmvF X A U V).f (k+n+2))).mp hmono
    rw [map_zero]
    have hcomm := congrArg (fun (g : (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)).X (k+n+1) ⟶
        ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) ⊞
          (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V))).X (k+n+2)) =>
        g ((HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relMVTopC X A U V)) hkn).hom (cupTop X A U V n (k+1) t.1 t.2 w)))
      (HomologicalComplex.Hom.comm (Work.Cohomology.hmvF X A U V) (k+n+1) (k+n+2))
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [← hcomm, hx₁]
    exact congrArg (fun (g : ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))).X (k+n) ⟶ ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))).X (k+n+2)) =>
        g (cupMid X A U V n k t.1 t.2 zt))
      (HomologicalComplex.d_comp_d ((Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU X A U V)) ⊞ (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV X A U V))) (k+n) (k+n+1) (k+n+2))
  have hL : (CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.honestDelta X (∅ : Set X) U V hU hV hcov k)
      (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) (k + 1)))
      (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU ∅ (U ∩ V)) c hc)
      = (Work.Cohomology.cmpXIso X A U V hU hV hcov ((k+1)+n)).inv
          ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).homologyπ ((k+1)+n)
            (Work.Cohomology.cocycleOfK _ (Work.Thom.cupTop X A U V n (k+1) t.1 t.2 w) hcw)) := by
    rw [Work.Cohomology.honestDelta]
    simp only [ConcreteCategory.comp_apply]
    have h1 : (Work.Cohomology.cmpWIso X ∅ U V k).hom
          (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU ∅ (U ∩ V)) c hc)
        = (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X ∅ U V)).homologyπ k
            (Work.Cohomology.cocycleOfK _
              ((Work.Cohomology.cmpW X ∅ U V).f k c) hz) := by
      rw [Work.Cohomology.cmpWIso_hom, relClassOf_eq_homologyπ (X := TopCat.of ↥(U ∩ V))
        (A := Work.Cohomology.interAU ∅ (U ∩ V)) c hc]
      exact homologyMap_cocycleOfK (Work.Cohomology.cmpW X ∅ U V) k c hcocy hz
    rw [show (Work.Cohomology.cmpWIso X ∅ U V k).hom
        (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V))
          (Work.Cohomology.interAU ∅ (U ∩ V)) c hc) = _ from h1]
    rw [hmvδ_apply X ∅ U V k ((Work.Cohomology.cmpW X ∅ U V).f k c) hz zt hzt w hw hwd]
    exact Ttop_cyclesMk X A U V hU hV hcov n (k+1) t ht w hwd hcw
  have hR : (CategoryTheory.CategoryStruct.comp (Work.Thom.TsqH.Tov X A U V n
        (Work.Cohomology.relClassOf ℤ X A t ht) k)
      (CategoryTheory.CategoryStruct.comp (Work.Cohomology.honestDelta X A U V hU hV hcov (k + n))
        (CategoryTheory.eqToHom (congrArg (fun m => Work.Cohomology.pdCoh X A m)
          (by omega : k + n + 1 = (k + 1) + n)))))
      (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU ∅ (U ∩ V)) c hc)
      = (Work.Cohomology.cmpXIso X A U V hU hV hcov ((k+1)+n)).inv
          ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).homologyπ ((k+1)+n)
            (Work.Cohomology.cocycleOfK _ (Work.Thom.cupTop X A U V n (k+1) t.1 t.2 w) hcw)) := by
    have h' : Work.Cohomology.relDiffLM ℤ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V)) n (relRestrCochain A (U ∩ V) n t) = 0 := by
      rw [← Work.Cohomology.relComplex_d_apply ℤ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V)) (relRestrCochain A (U ∩ V) n t)]
      have ht' : (Work.Cohomology.relComplex ℤ X A).d n (n+1) t = 0 := by
        rw [Work.Cohomology.relComplex_d]; exact ht
      have hcomm := congrArg (fun (g : (Work.Cohomology.relComplex ℤ X A).X n ⟶
          (Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU A (U ∩ V))).X (n+1)) => g t)
        (HomologicalComplex.Hom.comm (Work.Cohomology.relComplexMap ℤ
          (X₁ := TopCat.of ↥(U ∩ V)) (X₂ := X) (Work.Cohomology.interAU A (U ∩ V)) A
          (Work.Cohomology.subtypeIncl X (U ∩ V)) (fun y hy => hy)) n (n+1))
      simp only [ConcreteCategory.comp_apply] at hcomm
      rw [ht', map_zero] at hcomm
      exact hcomm
    have hca : Work.Cohomology.relDiffLM ℤ (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V)) (k+n)
        ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
          (Work.Cohomology.interAU ∅ (U ∩ V)) k) c) = 0 :=
      (Work.Cohomology.mixedCup_apply (TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU A (U ∩ V)) k n c.1 (relRestrCochain A (U ∩ V) n t)
        (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of ↥(U ∩ V))
          (Work.Cohomology.interAU ∅ (U ∩ V)) c hc) h').choose_spec.choose
    simp only [ConcreteCategory.comp_apply]
    rw [show (Work.Thom.TsqH.Tov X A U V n (Work.Cohomology.relClassOf ℤ X A t ht) k)
        (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V))
          (Work.Cohomology.interAU ∅ (U ∩ V)) c hc)
        = Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU A (U ∩ V))
            ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c) hca
        from Tov_relClassOf X A U V n k t ht c hc h' hca]
    rw [Work.Cohomology.honestDelta]
    simp only [ConcreteCategory.comp_apply]
    have h2 : (Work.Cohomology.cmpWIso X A U V (k+n)).hom
          (Work.Cohomology.relClassOf ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU A (U ∩ V))
            ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c) hca)
        = (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).homologyπ (k+n)
            (Work.Cohomology.cocycleOfK _ (cupUV X A U V n k t.1 t.2 z) hE4') := by
      rw [Work.Cohomology.cmpWIso_hom, relClassOf_eq_homologyπ (X := TopCat.of ↥(U ∩ V))
        (A := Work.Cohomology.interAU A (U ∩ V))
        ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
          (Work.Cohomology.interAU ∅ (U ∩ V)) k) c) hca]
      have hxcyc : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)).d
          (k+n) (k+n+1)
          ((Work.Cohomology.cmpW X A U V).f (k+n)
            ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c)) = 0 := by
        have hcomm := congrArg (fun (g : (Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU A (U ∩ V))).X (k+n) ⟶ (Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relMVUV X A U V)).X (k+n+1)) =>
            g ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c))
          (HomologicalComplex.Hom.comm (Work.Cohomology.cmpW X A U V) (k+n) (k+n+1))
        simp only [ConcreteCategory.comp_apply] at hcomm
        have hcax : ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ (TopCat.of ↥(U ∩ V))
            (Work.Cohomology.interAU A (U ∩ V))).d (k+n) (k+n+1))
            ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c) = 0 :=
          (relComplex_d_eq_zero_iff_relDiffLM _).mpr hca
        rw [hcax, map_zero] at hcomm
        exact hcomm
      refine (homologyMap_cocycleOfK (Work.Cohomology.cmpW X A U V) (k+n)
        ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
          (Work.Cohomology.interAU ∅ (U ∩ V)) k) c)
        ((relComplex_d_eq_zero_iff_relDiffLM _).mpr hca) hxcyc).trans ?_
      exact homologyπ_cocycleOfK_congr _
          ((Work.Cohomology.cmpW X A U V).f (k+n)
            ((Work.Thom.cupRightLM (relRestrCochain A (U ∩ V) n t)
              (Work.Cohomology.interAU ∅ (U ∩ V)) k) c))
          (cupUV X A U V n k t.1 t.2 z)
          (by rw [hzdef]; exact cupCmpRestrictOvl X A U V n k t c) hxcyc hE4'
    rw [h2]
    rw [hmvδ_apply X A U V (k+n) (cupUV X A U V n k t.1 t.2 z) hE4'
      (cupMid X A U V n k t.1 t.2 zt) hzt'
      ((HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC X A U V)) hkn).hom
        (cupTop X A U V n (k+1) t.1 t.2 w)) hx₁ hx₁c]
    erw [eqToHom_homology_cocycleOfK (Work.Cohomology.dualComplex ℤ
      (Work.Cohomology.relMVTopC X A U V)) hkn (cupTop X A U V n (k+1) t.1 t.2 w) hcw hx₁c]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      eqToHom_cmpXIso_inv_comp X A U V hU hV hcov hkn]
  rw [hL, hR]

end

end Work.Thom
