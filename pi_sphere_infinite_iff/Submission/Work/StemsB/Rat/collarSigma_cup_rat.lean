import Mathlib
import Submission.Work.StemsB.Rat.CollarCup
import Submission.Work.StemsB.Rat.CollarSplit
import Submission.Work.StemsB.Rat.CollarSplitFull
import Submission.Work.StemsB.MixedCupR
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.pairDelta_mixedCup_general_R
import Submission.Work.Cohomology.gradedComm

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.StemsB.Rat


noncomputable section

/-! ## Degree-transport helpers

All degree bookkeeping in this file is done with `eqToHom (congrArg (fun t => K.homology t) h)`,
following the idiom of `Submission/Work/StemsB/collarDelta_collarSPart.lean`. -/

private lemma transT_eq_eqToHom {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v : Work.Thom.Coh ℚ i Y) :
    transT Y h v = (CategoryTheory.eqToHom (congrArg (fun t =>
      (Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y)).homology t) h) :
        Work.Thom.Coh ℚ i Y ⟶ Work.Thom.Coh ℚ j Y) v := by
  cases h; rfl

private lemma CohMap_eqToHom_homology {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X', Y')) {i j : ℕ} (h : i = j)
    (z : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y')).homology i) :
    (Work.Thom.CohMap f ℚ j).hom
        (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y')).homology t) h) z)
      = CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X') h)
          ((Work.Thom.CohMap f ℚ i).hom z) := by
  cases h; rfl

private lemma mixedCup_eqToHom_left {X : TopCat} (A : Set X) {i i' : ℕ} (h : i = i') (k : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℚ X).homology i)
    (z : (Work.Cohomology.relComplex ℚ X A).homology k) :
    (Work.Cohomology.mixedCupR ℚ X A i' k)
        (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.singularCochainComplex ℚ X).homology t) h) x) z
      = CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.relComplex ℚ X A).homology (t + k)) h)
          ((Work.Cohomology.mixedCupR ℚ X A i k) x z) := by
  cases h; rfl

private lemma cast_proof_irrel (K : CochainComplex (ModuleCat ℚ) ℕ) {i j : ℕ} (h h' : i = j)
    (z : K.homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h) : K.homology i ⟶ K.homology j) z
      = (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h') : K.homology i ⟶ K.homology j) z := by
  rw [Subsingleton.elim h h']

private lemma cast_comp (K : CochainComplex (ModuleCat ℚ) ℕ) {i j k : ℕ} (h : i = j) (h' : j = k)
    (z : K.homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h') : K.homology j ⟶ K.homology k)
        ((CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h) : K.homology i ⟶ K.homology j) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) (h.trans h'))
          : K.homology i ⟶ K.homology k) z := by
  cases h; cases h'; simp

private lemma cast_self (K : CochainComplex (ModuleCat ℚ) ℕ) (i : ℕ) (h : i = i)
    (z : K.homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h) : K.homology i ⟶ K.homology i) z = z := by
  rw [Subsingleton.elim h rfl]; simp

private lemma CohMap_map_smul {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X', Y')) (n : ℕ) (c : ℚ)
    (z : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y')).homology n) :
    (Work.Thom.CohMap f ℚ n).hom (c • z) = c • ((Work.Thom.CohMap f ℚ n).hom z) := by
  rw [map_smul]

variable {Y : Type} [TopologicalSpace Y]

/-- The map `collarSection : Y → C` composed with the inclusion `C ↪ Q` acts on cohomology as
`collarRestr` followed by `collarSection^*`. -/
private lemma collarSection_collarRestr (b : ℕ) (hb : 1 ≤ b) (n : ℕ)
    (z : Work.Thom.Coh ℚ n (↥(sphLoopBig b) × Y)) :
    (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ n).hom (collarRestr b Y n z)
      = (Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ n).hom z := by
  have hcomp := Work.Cohomology.singularCohomologyMap_comp ℚ (TopCat.ofHom (collarSection (Y := Y) b hb))
      (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) n
  rw [collarSection_comp_subtypeIncl (Y := Y) b hb] at hcomp
  have h := congrArg ModuleCat.Hom.hom hcomp
  rw [show collarRestr (Y := Y) b n
      = (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(sphLoopCollarProd b Y), ↥(sphLoopBig b) × Y)) ℚ n).hom from rfl]
  rw [show (Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ n).hom
      = ((Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ n).hom).comp
          ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(sphLoopCollarProd b Y), ↥(sphLoopBig b) × Y)) ℚ n).hom) from h]
  rfl

/-- `collarSectionIncl^* ≫ collarProjY^* = 𝟙` on the cohomology of `Y`. -/
private lemma collarSectionIncl_collarProjY (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    ((Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ n).hom).comp
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ n).hom)
      = LinearMap.id := by
  rw [Work.Thom.CohMap_linear_comp (collarSectionIncl (Y := Y) b hb) (collarProjY (Y := Y) b) ℚ n]
  rw [show (collarProjY (Y := Y) b).comp (collarSectionIncl (Y := Y) b hb) = ContinuousMap.id Y
      from by ext y; rfl]
  show (Work.Thom.CohMap (ContinuousMap.id Y) ℚ n).hom = (LinearMap.id : Work.Thom.Coh ℚ n Y →ₗ[ℚ] Work.Thom.Coh ℚ n Y)
  rw [show (Work.Thom.CohMap (ContinuousMap.id Y) ℚ n) = 𝟙 (Work.Thom.Coh ℚ n Y) from by
    show Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y) (TopCat.of Y)
        (TopCat.ofHom (ContinuousMap.id Y)) n = 𝟙 _
    rw [TopCat.ofHom_id]
    exact Work.Cohomology.singularCohomologyMap_id ℚ (TopCat.of Y) n]
  rfl

/-! ## Coefficient-`ℚ` shims for the degree-transport lemmas of the Thom chapter

`cocycle_transport_K_rat`, `relComplex_XIsoOfEq_coe_rat` and
`relClassOf_cast_rat` are stated over `ℤ` in `Submission/Work/Thom/localThomMap_cup_zero.lean`;
their proofs are coefficient-independent, and these are the `ℚ` copies. -/

private lemma cocycle_transport_K_rat {K : CochainComplex (ModuleCat ℚ) ℕ} {k j : ℕ} (h : k = j)
    (u : K.X k) (hu : ModuleCat.Hom.hom (K.d k (k+1)) u = 0) :
    ModuleCat.Hom.hom (K.d j (j+1)) ((K.XIsoOfEq h).hom u) = 0 := by
  have e1 := HomologicalComplex.XIsoOfEq_hom_comp_d K h (j+1)
  have e1' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1'
  have e2 := HomologicalComplex.d_comp_XIsoOfEq_hom K (congrArg (fun t => t + 1) h) k
  have e2' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2'
  rw [e1', ← e2', hu, map_zero]

private lemma relComplex_XIsoOfEq_coe_rat {Y : TopCat} {B : Set Y} {k j : ℕ} (h : k = j)
    (y : (Work.Cohomology.relComplex ℚ Y B).X k) :
    ((((Work.Cohomology.relComplex ℚ Y B).XIsoOfEq h).hom y)).1 =
      (h ▸ (y.1 : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k) :
        Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) j) := by
  subst h; simp

private lemma eqRec_homologyπ_cocycleOfK_rat {K : CochainComplex (ModuleCat ℚ) ℕ} {a b : ℕ}
    (h : a = b) (y : K.X a) (hy : (K.d a (a+1)).hom y = 0)
    (hy' : (K.d b (b+1)).hom ((K.XIsoOfEq h).hom y) = 0) :
    (h ▸ (K.homologyπ a (Work.Cohomology.cocycleOfK K y hy)) : K.homology b)
      = K.homologyπ b (Work.Cohomology.cocycleOfK K ((K.XIsoOfEq h).hom y) hy') := by
  cases h; simp

private lemma relClassOf_cast_rat {Y : TopCat} {A : Set Y} {k j : ℕ} (h : k = j)
    (u : Work.Cohomology.relKern ℚ Y A k) (hu : Work.Cohomology.relDiffLM ℚ Y A k u = 0)
    (hu' : Work.Cohomology.relDiffLM ℚ Y A j
      (((Work.Cohomology.relComplex ℚ Y A).XIsoOfEq h).hom u) = 0) :
    (h ▸ Work.Cohomology.relClassOf ℚ Y A u hu : (Work.Cohomology.relComplex ℚ Y A).homology j)
      = Work.Cohomology.relClassOf ℚ Y A (((Work.Cohomology.relComplex ℚ Y A).XIsoOfEq h).hom u)
          hu' := by
  rw [show Work.Cohomology.relClassOf ℚ Y A u hu = (Work.Cohomology.relComplex ℚ Y A).homologyπ k
      (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ Y A) u
        (show ((Work.Cohomology.relComplex ℚ Y A).d k (k+1)).hom u = 0 by
          rw [Work.Cohomology.relComplex_d]; exact hu)) from rfl,
    show Work.Cohomology.relClassOf ℚ Y A (((Work.Cohomology.relComplex ℚ Y A).XIsoOfEq h).hom u) hu'
      = (Work.Cohomology.relComplex ℚ Y A).homologyπ j
        (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ Y A)
          (((Work.Cohomology.relComplex ℚ Y A).XIsoOfEq h).hom u)
          (show ((Work.Cohomology.relComplex ℚ Y A).d j (j+1)).hom
              (((Work.Cohomology.relComplex ℚ Y A).XIsoOfEq h).hom u) = 0 by
            rw [Work.Cohomology.relComplex_d]; exact hu')) from rfl]
  exact eqRec_homologyπ_cocycleOfK_rat (K := Work.Cohomology.relComplex ℚ Y A) h u _ _

/-! ## Associativity of the mixed cup product (general degrees) -/

/-- **Associativity of the mixed cup product** `(a ⌣ b) ⌣ z = a ⌣ (b ⌣ z)` (general degrees),
with the degree cast `Nat.add_assoc m n k`.  This is the generalisation of
`Work.StemsB.Rat.mixedCupC_assoc_zero`, proved the same way (cochain-level `cupAssoc`). -/
private lemma mixedCupC_assoc_cast {X : Type} [TopologicalSpace X] (A : Set X) (m n k : ℕ)
    (a : Work.Thom.Coh ℚ m X) (b : Work.Thom.Coh ℚ n X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m (n + k)) a ((Work.Thom.mixedCupC ℚ A n k) b z)
      = (Nat.add_assoc m n k) ▸
          ((Work.Thom.mixedCupC ℚ A (m + n) k)
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of X)) m n) a b) z) := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) m a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) n b
  obtain ⟨ζ, hζ, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ (TopCat.of X) A k z
  simp only [Work.StemsB.mixedCupC_eq_mixedCupR ℚ]
  -- the left-hand side
  obtain ⟨hmem1, hcoc1, h1⟩ :=
    Work.Cohomology.mixedCupR_apply ℚ (TopCat.of X) A n k β ζ hβ hζ
  rw [h1]
  obtain ⟨hmem2, hcoc2, h2⟩ :=
    Work.Cohomology.mixedCupR_apply ℚ (TopCat.of X) A m (n + k) α
      ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) β ζ.1, hmem1⟩ hα hcoc1
  rw [h2]
  -- the right-hand side, under the cast
  rw [Work.Cohomology.cupH'_apply' ℚ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ :=
    Work.Cohomology.mixedCupR_apply ℚ (TopCat.of X) A (m + n) k
      (Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ
      (Work.Cohomology.cochainDiff_cup_of_cocycles ℚ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ)
      hζ
  rw [h3]
  -- push the cast inside
  let u3 : Work.Cohomology.relKern ℚ (TopCat.of X) A (m + n + k) :=
    ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ.1, hmem3⟩
  have hu3 : Work.Cohomology.relDiffLM ℚ (TopCat.of X) A (m + n + k) u3 = 0 := hcoc3
  have hu3' : Work.Cohomology.relDiffLM ℚ (TopCat.of X) A (m + (n + k))
      (((Work.Cohomology.relComplex ℚ (TopCat.of X) A).XIsoOfEq (Nat.add_assoc m n k)).hom u3) = 0 := by
    rw [← Work.Cohomology.relComplex_d_apply]
    exact cocycle_transport_K_rat (K := Work.Cohomology.relComplex ℚ (TopCat.of X) A)
      (Nat.add_assoc m n k) u3 (by rw [Work.Cohomology.relComplex_d_apply]; exact hu3)
  rw [relClassOf_cast_rat (Y := TopCat.of X) (A := A) (Nat.add_assoc m n k) u3 hu3 hu3']
  -- the cochain identity
  refine Work.Cohomology.relClassOf_congr ℚ (TopCat.of X) A hcoc2 _ (Subtype.ext ?_)
  rw [relComplex_XIsoOfEq_coe_rat (Y := TopCat.of X) (B := A) (Nat.add_assoc m n k)]
  simpa only [Subtype.coe_mk, Subtype.coe_eta] using
    (Work.Cohomology.cupAssoc ℚ (TopCat.toSSet.obj (TopCat.of X)) α β ζ.1).symm


/-! ## Casts for `cupH'`, and the square-zero computation -/

/-- `h ▸ x = y` implies `x = h.symm ▸ y`. -/
private lemma cast_eq_of_cast_eq {F : ℕ → Type*} {a b : ℕ} (h : a = b) {x : F a} {y : F b}
    (hxy : h ▸ x = y) : x = h.symm ▸ y := by
  cases h; simpa using hxy

/-- `h ▸ x = y` implies `x = (the cast along `h.symm`) y`, with the cast written as `eqToHom`. -/
private lemma cast_eq_of_cast_eq' {F : ℕ → Type*} {a b : ℕ} (h : a = b) {x : F a} {y : F b}
    (hxy : h ▸ x = y) : x = (CategoryTheory.eqToHom (congrArg F h.symm)) y := by
  cases h; simpa using hxy

private lemma cast_zero_apply {F : ℕ → Type*} [∀ n, Zero (F n)] {a b : ℕ} (h : a = b) :
    h ▸ (0 : F a) = (0 : F b) := by cases h; rfl

private lemma eqToHom_homology_zero (J : CochainComplex (ModuleCat ℚ) ℕ) {a b : ℕ} (h : a = b) :
    (CategoryTheory.eqToHom (congrArg (fun t => J.homology t) h) : J.homology a ⟶ J.homology b)
      (0 : J.homology a) = 0 := by
  cases h; simp

/-- `eqToHom`-casts on homology are `▸`-casts. -/
private lemma eqToHom_homology_eq_cast (K : CochainComplex (ModuleCat ℚ) ℕ) {a b : ℕ} (h : a = b)
    (x : K.homology a) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h) : K.homology a ⟶ K.homology b) x
      = h ▸ x := by
  cases h; rfl

/-- The cup product is natural in the degree of its first argument. -/
private lemma cupH'_cast_left {X : SSet} {a a' c : ℕ} (h : a = a')
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology a)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology c) :
    (Work.Cohomology.cupH' ℚ X a' c) (h ▸ x) y
      = (congrArg (fun t => t + c) h) ▸ ((Work.Cohomology.cupH' ℚ X a c) x y) := by
  cases h; rfl

/-- The cup product is natural in the degree of its second argument. -/
private lemma cupH'_cast_right {X : SSet} {c b b' : ℕ} (h : b = b')
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology c)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology b) :
    (Work.Cohomology.cupH' ℚ X c b') x (h ▸ y)
      = (congrArg (fun t => c + t) h) ▸ ((Work.Cohomology.cupH' ℚ X c b) x y) := by
  cases h; rfl

/-- The cup product is natural in the degree of its first argument (transport form). -/
private lemma cupH'_eqToHom_left {X : SSet} {a a' c : ℕ} (h : a = a')
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology a)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology c) :
    (Work.Cohomology.cupH' ℚ X a' c)
        ((CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.SSetCochainComplex ℚ X).homology t) h)) x) y
      = (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.SSetCochainComplex ℚ X).homology (t + c)) h))
          ((Work.Cohomology.cupH' ℚ X a c) x y) := by
  cases h; rfl

/-- The cup product is natural in the degree of its second argument (transport form). -/
private lemma cupH'_eqToHom_right {X : SSet} {c b b' : ℕ} (h : b = b')
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology c)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology b) :
    (Work.Cohomology.cupH' ℚ X c b') x
        ((CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.SSetCochainComplex ℚ X).homology t) h)) y)
      = (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.SSetCochainComplex ℚ X).homology (c + t)) h))
          ((Work.Cohomology.cupH' ℚ X c b) x y) := by
  cases h; rfl

/-- **The square of an `s`-part**: `(a ⌣ s) ⌣ (b ⌣ s) = 0` when `s ⌣ s = 0`. -/
private lemma cupH'_sq_kill {X : SSet} (p q d : ℕ)
    (A : (Work.Cohomology.SSetCochainComplex ℚ X).homology p)
    (B : (Work.Cohomology.SSetCochainComplex ℚ X).homology q)
    (s : (Work.Cohomology.SSetCochainComplex ℚ X).homology d)
    (hssq : (Work.Cohomology.cupH' ℚ X d d) s s = 0) :
    (Work.Cohomology.cupH' ℚ X (p + d) (q + d))
      ((Work.Cohomology.cupH' ℚ X p d) A s) ((Work.Cohomology.cupH' ℚ X q d) B s) = 0 := by
  have h1 : (Work.Cohomology.cupH' ℚ X (q + d) d)
      ((Work.Cohomology.cupH' ℚ X q d) B s) s = 0 := by
    rw [cast_eq_of_cast_eq
      (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k)
      (Nat.add_assoc q d d) (Work.Cohomology.cupH'_assoc ℚ X q d d B s s)]
    have hz : (Work.Cohomology.cupH' ℚ X q (d + d)) B
        ((Work.Cohomology.cupH' ℚ X d d) s s) = 0 := by
      rw [hssq, Work.Cohomology.cupH'_zero_right]
    rw [hz]
    exact cast_zero_apply (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k) _
  have h2 : (Work.Cohomology.cupH' ℚ X d (q + d)) s
      ((Work.Cohomology.cupH' ℚ X q d) B s) = 0 := by
    rw [cast_eq_of_cast_eq
      (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k)
      (Nat.add_comm d (q + d))
      (Work.Cohomology.gradedComm ℚ X d (q + d) s ((Work.Cohomology.cupH' ℚ X q d) B s))]
    rw [h1]
    simp
    exact cast_zero_apply (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k) _
  have h3 : (Work.Cohomology.cupH' ℚ X p (d + (q + d))) A
      ((Work.Cohomology.cupH' ℚ X d (q + d)) s ((Work.Cohomology.cupH' ℚ X q d) B s)) = 0 := by
    rw [h2, Work.Cohomology.cupH'_zero_right]
  rw [cast_eq_of_cast_eq
    (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k)
    (Nat.add_assoc p d (q + d))
    (Work.Cohomology.cupH'_assoc ℚ X p d (q + d) A s ((Work.Cohomology.cupH' ℚ X q d) B s))]
  rw [h3]
  exact cast_zero_apply (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ X).homology k) _

/-- `cupH'` is `ℚ`-linear in its first argument. -/
private lemma cupH'_smul_left {X : SSet} (k l : ℕ) (c : ℚ)
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology k)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology l) :
    (Work.Cohomology.cupH' ℚ X k l) (c • x) y
      = c • ((Work.Cohomology.cupH' ℚ X k l) x y) := by
  have h := map_smul (Work.Cohomology.cupH' ℚ X k l) c x
  exact congrFun (congrArg DFunLike.coe h) y

/-- `cupH'` is `ℚ`-linear in its second argument. -/
private lemma cupH'_smul_right {X : SSet} (k l : ℕ) (c : ℚ)
    (x : (Work.Cohomology.SSetCochainComplex ℚ X).homology k)
    (y : (Work.Cohomology.SSetCochainComplex ℚ X).homology l) :
    (Work.Cohomology.cupH' ℚ X k l) x (c • y)
      = c • ((Work.Cohomology.cupH' ℚ X k l) x y) := by
  exact map_smul ((Work.Cohomology.cupH' ℚ X k l) x) c y

/-- **The product of two `s`-parts vanishes** when `s ⌣ s = 0`. -/
private lemma collarSPart_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (m m' : ℕ) (X : Work.Thom.Coh ℚ (m + b) ↥(sphLoopCollarProd b Y))
    (Y' : Work.Thom.Coh ℚ (m' + b) ↥(sphLoopCollarProd b Y)) :
    cupT ↥(sphLoopCollarProd b Y) (m + b) (m' + b)
      (collarSPart b hb Y τ hτ s m X) (collarSPart b hb Y τ hτ s m' Y') = 0 := by
  have h1 : (m + 1) + (b - 1) = m + b := by omega
  have h2 : (m' + 1) + (b - 1) = m' + b := by omega
  set sx1 := collarSigma b hb Y τ hτ m X with hsx1
  set sx2 := collarSigma b hb Y τ hτ m' Y' with hsx2
  set A1 := (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) (m + 1)).hom
      ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + 1)).hom sx1) with hA1
  set A2 := (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) (m' + 1)).hom
      ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m' + 1)).hom sx2) with hA2
  set W1 : (CollKC b Y).homology ((m + 1) + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + 1) (b - 1)) A1 s with hW1
  set W2 : (CollKC b Y).homology ((m' + 1) + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m' + 1) (b - 1)) A2 s with hW2
  have hu : collarSPart b hb Y τ hτ s m X = h1 ▸ (((-1 : ℚ) ^ (m + 1)) • W1) := by
    rw [collarSPart_apply b hb Y τ hτ s m X]
    rw [← hsx1, collarProjC_eq_restr_apply, ← hA1, ← hW1]
    rw [collarRelEqS_apply b hb Y m h1 _]
    exact eqToHom_homology_eq_cast (CollKC b Y) h1 _
  have hv : collarSPart b hb Y τ hτ s m' Y' = h2 ▸ (((-1 : ℚ) ^ (m' + 1)) • W2) := by
    rw [collarSPart_apply b hb Y τ hτ s m' Y']
    rw [← hsx2, collarProjC_eq_restr_apply, ← hA2, ← hW2]
    rw [collarRelEqS_apply b hb Y m' h2 _]
    exact eqToHom_homology_eq_cast (CollKC b Y) h2 _
  have hkill : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) ((m + 1) + (b - 1))
      ((m' + 1) + (b - 1))) W1 W2 = 0 :=
    cupH'_sq_kill (m + 1) (m' + 1) (b - 1) A1 A2 s hssq
  have hgoal : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
      (collarSPart b hb Y τ hτ s m X) (collarSPart b hb Y τ hτ s m' Y') = 0 := by
    rw [hu, hv]
    have hstep1 : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
        (h1 ▸ (((-1 : ℚ) ^ (m + 1)) • W1)) (h2 ▸ (((-1 : ℚ) ^ (m' + 1)) • W2))
        = (congrArg (fun t => t + (m' + b)) h1) ▸
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) ((m + 1) + (b - 1))
              (m' + b)) (((-1 : ℚ) ^ (m + 1)) • W1)
              (h2 ▸ (((-1 : ℚ) ^ (m' + 1)) • W2))) :=
      cupH'_cast_left h1 (((-1 : ℚ) ^ (m + 1)) • W1) (h2 ▸ (((-1 : ℚ) ^ (m' + 1)) • W2))
    rw [hstep1]
    have hstep2 : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) ((m + 1) + (b - 1))
        (m' + b)) (((-1 : ℚ) ^ (m + 1)) • W1) (h2 ▸ (((-1 : ℚ) ^ (m' + 1)) • W2))
        = (congrArg (fun t => ((m + 1) + (b - 1)) + t) h2) ▸
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) ((m + 1) + (b - 1))
              ((m' + 1) + (b - 1))) (((-1 : ℚ) ^ (m + 1)) • W1)
              (((-1 : ℚ) ^ (m' + 1)) • W2)) :=
      cupH'_cast_right h2 (((-1 : ℚ) ^ (m + 1)) • W1) (((-1 : ℚ) ^ (m' + 1)) • W2)
    rw [hstep2]
    rw [cupH'_smul_left, cupH'_smul_right, hkill]
    rw [smul_zero, smul_zero]
    have hc2 : (congrArg (fun t => ((m + 1) + (b - 1)) + t) h2) ▸
        (0 : (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (CollC b Y))).homology
          (((m + 1) + (b - 1)) + ((m' + 1) + (b - 1)))) = 0 :=
      cast_zero_apply (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ
        (TopCat.toSSet.obj (CollC b Y))).homology k)
        (congrArg (fun t => ((m + 1) + (b - 1)) + t) h2)
    rw [hc2]
    exact cast_zero_apply (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ
        (TopCat.toSSet.obj (CollC b Y))).homology k)
        (congrArg (fun t => t + (m' + b)) h1)
  show (Work.StemsB.Rat.cupT ↥(sphLoopCollarProd b Y) (m + b) (m' + b))
      (collarSPart b hb Y τ hτ s m X) (collarSPart b hb Y τ hτ s m' Y') = 0
  exact hgoal


/-! ## The transgression / projection maps, with fixed spellings -/

/-- The singular cochain complex of the collar, in the `SSetCochainComplex` spelling (which is the
one used by `cupH'` and `gradedComm`). -/
private abbrev CollKCx (b : ℕ) (Y : Type) [TopologicalSpace Y] : CochainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (CollC b Y))

/-- `π^* : H^k(Y) → H^k(Q)`, the pullback along the projection of the collar pair. -/
private abbrev piStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ k).hom

/-- `σ^* : H^k(C) → H^k(Y)`, the pullback along the collar section. -/
private abbrev sgStar (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ k).hom

/-- `i^* : H^k(Q) → H^k(C)`, the restriction of the collar pair. -/
private abbrev iStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) k).hom

/-- `δ : H^k(C) → H^{k+1}(Q,C)`, the connecting homomorphism of the collar pair. -/
private abbrev dPair (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) k).hom

/-- `δ (i^* z) = 0`. -/
private lemma dPair_iStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology k) :
    dPair b Y k (iStar b Y k z) = 0 := by
  have h := Work.Cohomology.pair_comp_δ ℚ (CollQ b Y) (CollA b Y) k
  have h2 := congrArg ModuleCat.Hom.hom h
  have h3 := congrFun (congrArg DFunLike.coe h2) z
  simpa [iStar, dPair, ModuleCat.hom_comp] using h3

/-- `i^*` is a ring map, hence `i^*a ⌣ i^*b = i^*(a ⌣ b)`. -/
private lemma iStar_cup (b : ℕ) (Y : Type) [TopologicalSpace Y] (m m' : ℕ)
    (a : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology m)
    (b' : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology m') :
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) m m')
        (iStar b Y m a) (iStar b Y m' b')
      = iStar b Y (m + m')
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) m m') a b') := by
  rw [show iStar b Y m
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m).hom from rfl]
  rw [show iStar b Y m'
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m').hom from rfl]
  rw [show iStar b Y (m + m')
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) (m + m')).hom from rfl]
  exact (Work.Cohomology.cupNaturalH ℚ
    (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m m' a b').symm

/-- **The first cross term vanishes**: `δ (i^*a ⌣ i^*b) = 0`. -/
private lemma collar_dPair_restr_cup (b : ℕ) (Y : Type) [TopologicalSpace Y] (m m' : ℕ)
    (a : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (m + b))
    (b' : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (m' + b)) :
    dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (iStar b Y (m + b) a) (iStar b Y (m' + b) b')) = 0 := by
  rw [iStar_cup]
  exact dPair_iStar b Y ((m + b) + (m' + b)) _

/-- **The `s`-`s` term vanishes** (`s ⌣ s = 0`). -/
private lemma collar_dPair_SPart_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (m m' : ℕ) (X : (CollKC b Y).homology (m + b)) (Y' : (CollKC b Y).homology (m' + b)) :
    dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (collarSPart b hb Y τ hτ s m X) (collarSPart b hb Y τ hτ s m' Y')) = 0 := by
  have h : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
      (collarSPart b hb Y τ hτ s m X) (collarSPart b hb Y τ hτ s m' Y') = 0 :=
    collarSPart_cup b hb Y τ hτ s hssq m m' X Y'
  rw [h]
  exact map_zero _


/-- `δ` is `ℚ`-linear. -/
private lemma dPair_smul (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) (c : ℚ)
    (z : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥(CollA b Y))).homology k) :
    dPair b Y k (c • z) = c • dPair b Y k z := by
  rw [map_smul]

/-- Graded commutativity, with the degree cast in the collar spelling. -/
private lemma gradedComm_coll (b : ℕ) (Y : Type) [TopologicalSpace Y] (m m' : ℕ)
    (x : (CollKC b Y).homology m) (y : (CollKC b Y).homology m') :
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) m m') x y
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollKCx b Y).homology t)
          (Nat.add_comm m m').symm))
          (((-1 : ℚ) ^ (m * m')) • ((Work.Cohomology.cupH' ℚ
            (TopCat.toSSet.obj (CollC b Y)) m' m) y x)) := by
  rw [eqToHom_homology_eq_cast (CollKCx b Y) (Nat.add_comm m m').symm]
  exact cast_eq_of_cast_eq (F := fun t => (CollKCx b Y).homology t) (Nat.add_comm m m')
    (Work.Cohomology.gradedComm ℚ (TopCat.toSSet.obj (CollC b Y)) m m' x y)

/-- `δ` is natural in the degree (transport form, in the collar spelling). -/
private lemma dPair_eqToHom_cast (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (z : (CollKCx b Y).homology i) :
    dPair b Y j
        ((CategoryTheory.eqToHom (congrArg (fun t => (CollKCx b Y).homology t) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (congrArg (fun t => t + 1) h)) (dPair b Y i z)
          : (CollRC b Y).homology (j + 1)) := by
  cases h; rfl

/-- **The second cross term**: `δ (i^*a ⌣ π^*(σ^* X) ⌣ s) = δ (i^*a ⌣ i^*X)`. -/
private lemma collar_dPair_restr_SPart (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b hb (Y := Y) s τ)
    (m m' : ℕ) (X : (CollKC b Y).homology (m + b)) (Y' : (CollKC b Y).homology (m' + b))
    (a : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (m + b))
    (ha : a = piStar b Y (m + b) (sgStar b hb Y (m + b) X)) :
    dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (iStar b Y (m + b) a) (collarSPart b hb Y τ hτ s m' Y'))
      = ((-1 : ℚ) ^ (m + b)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + b) ((m' + b) + 1))
            (piStar b Y (m + b) (sgStar b hb Y (m + b) X))
            (dPair b Y (m' + b) Y')) := by
  have hC := Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (m + b) (m' + b)
    a (collarSPart b hb Y τ hτ s m' Y')
  rw [hC]
  rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (m' + b)).hom
        (collarSPart b hb Y τ hτ s m' Y') = dPair b Y (m' + b) Y' from
    collarDelta_collarSPart b hb Y τ hτ s hs m' Y']
  rw [ha]

/-- **The third cross term**: `δ (π^*(Σ X) ⌣ s ⌣ i^*b') = ± π^*(σ^* Y') ⌣ δ X`. -/
private lemma collar_dPair_SPart_restr (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b hb (Y := Y) s τ)
    (m m' : ℕ) (X : (CollKC b Y).homology (m + b)) (Y' : (CollKC b Y).homology (m' + b))
    (b' : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (m' + b))
    (hb' : b' = piStar b Y (m' + b) (sgStar b hb Y (m' + b) Y')) :
    dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (collarSPart b hb Y τ hτ s m X) (iStar b Y (m' + b) b'))
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            (congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm)))
          (((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m' + b) ((m + b) + 1))
              (piStar b Y (m' + b) (sgStar b hb Y (m' + b) Y'))
              (dPair b Y (m + b) X))) := by
  rw [gradedComm_coll b Y (m + b) (m' + b) (collarSPart b hb Y τ hτ s m X) (iStar b Y (m' + b) b')]
  rw [dPair_eqToHom_cast b Y (Nat.add_comm (m + b) (m' + b)).symm]
  have hinner : dPair b Y ((m' + b) + (m + b))
        (((-1 : ℚ) ^ ((m + b) * (m' + b))) •
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m' + b) (m + b))
            (iStar b Y (m' + b) b') (collarSPart b hb Y τ hτ s m X)))
      = ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m' + b) ((m + b) + 1))
            (piStar b Y (m' + b) (sgStar b hb Y (m' + b) Y'))
            (dPair b Y (m + b) X)) := by
    rw [dPair_smul]
    rw [Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (m' + b) (m + b)
      b' (collarSPart b hb Y τ hτ s m X)]
    rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (m + b)).hom
          (collarSPart b hb Y τ hτ s m X) = dPair b Y (m + b) X from
      collarDelta_collarSPart b hb Y τ hτ s hs m X]
    rw [hb']
    rw [smul_smul, ← pow_add]
  rw [hinner]


/-- `δ` is additive. -/
private lemma dPair_add (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (x y : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥(CollA b Y))).homology k) :
    dPair b Y k (x + y) = dPair b Y k x + dPair b Y k y := by
  rw [map_add]

/-! ## Casts in the `Coh`/`RelCoh` spellings, and `transT` -/

/-- Composition of degree transports of `Coh`. -/
private lemma Coh_cast_comp {X : Type} [TopologicalSpace X] {i j k : ℕ} (h : i = j) (h' : j = k)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) (h.trans h'))) z := by
  cases h; cases h'; rfl

/-- Degree transports of `Coh` are proof-irrelevant. -/
private lemma Coh_cast_congr {X : Type} [TopologicalSpace X] {i j : ℕ} (h h' : i = j)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h')) z := by
  rw [Subsingleton.elim h h']

/-- A degree transport of `Coh` along a self-equality is the identity. -/
private lemma Coh_cast_self {X : Type} [TopologicalSpace X] {i : ℕ} (h : i = i)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z = z := by
  rw [Subsingleton.elim h rfl]; rfl

/-- Composition of degree transports of `RelCoh`. -/
private lemma RelCoh_cast_comp {X : Type} [TopologicalSpace X] (A : Set X) {i j k : ℕ}
    (h : i = j) (h' : j = k) (z : Work.Thom.RelCoh ℚ i X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (h.trans h'))) z := by
  cases h; cases h'; rfl

/-- Degree transports of `RelCoh` are proof-irrelevant. -/
private lemma RelCoh_cast_congr {X : Type} [TopologicalSpace X] (A : Set X) {i j : ℕ}
    (h h' : i = j) (z : Work.Thom.RelCoh ℚ i X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h')) z := by
  rw [Subsingleton.elim h h']

/-- `transT` composes. -/
private lemma transT_comp {Y : Type} [TopologicalSpace Y] {k l j : ℕ} (h : k = l) (h' : l = j)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h' (transT Y h v) = transT Y (h.trans h') v := by
  cases h; cases h'; rfl

/-- `transT` is proof-irrelevant in the degree equality. -/
private lemma transT_congr {Y : Type} [TopologicalSpace Y] {k l : ℕ} (h h' : k = l)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h v = transT Y h' v := by
  rw [Subsingleton.elim h h']

/-- `transT` along a self-equality is the identity. -/
private lemma transT_self {Y : Type} [TopologicalSpace Y] {k : ℕ} (h : k = k)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h v = v := by
  rw [transT_congr h rfl]; rfl

/-- `π^*` commutes with degree transports. -/
private lemma piStar_transT (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v : Work.Thom.Coh ℚ i Y) :
    piStar b Y j (transT Y h v)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t (↥(sphLoopBig b) × Y)) h))
          (piStar b Y i v) := by
  rw [transT_eq_eqToHom]
  exact CohMap_eqToHom_homology (collarProjY (Y := Y) b) h v

/-- The mixed cup product is natural in the degree of its absolute argument. -/
private lemma mixedCupC_cast_left {X : Type} [TopologicalSpace X] (A : Set X) {i i' : ℕ}
    (h : i = i') (k : ℕ) (x : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i' k)
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) x) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + k) X A) h))
          ((Work.Thom.mixedCupC ℚ A i k) x z) := by
  cases h; rfl


/-- Shifting the degree in a transport of `RelCoh` does not change the resulting cast. -/
private lemma RelCoh_cast_shift {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) :
    congrArg (fun t => Work.Thom.RelCoh ℚ (t + c) X A) h
      = congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (congrArg (fun t => t + c) h) := by
  cases h; rfl

/-- Shifting the degree (on the left) in a transport of `RelCoh`. -/
private lemma RelCoh_cast_shiftL {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) :
    congrArg (fun t => Work.Thom.RelCoh ℚ (c + t) X A) h
      = congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (congrArg (fun t => c + t) h) := by
  cases h; rfl

/-- A transport of `RelCoh` along `congrArg (· + c)` is a transport along the shifted equality. -/
private lemma RelCoh_cast_shift_apply {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) (h' : i + c = j + c) (z : Work.Thom.RelCoh ℚ (i + c) X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + c) X A) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h')) z := by
  rw [RelCoh_cast_shift A h]

/-- A `▸`-transport of `RelCoh` is an `eqToHom`-transport. -/
private lemma RelCoh_cast_eqToHom {X : Type} [TopologicalSpace X] (A : Set X) {i j : ℕ}
    (h : i = j) (z : Work.Thom.RelCoh ℚ i X A) :
    h ▸ z = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z := by
  cases h; rfl

/-- The mixed cup product is natural in the degree of its relative argument. -/
private lemma mixedCupC_cast_right' {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    {k k' : ℕ} (h : k = k') (a : Work.Thom.Coh ℚ m X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m k') a
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (m + t) X A) h))
          ((Work.Thom.mixedCupC ℚ A m k) a z) := by
  cases h; rfl

/-- **`δ` and the degree transport of the collar total space.** -/
private lemma dPair_transT (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (z : (CollKC b Y).homology i) :
    dPair b Y j (transT ↥(sphLoopCollarProd b Y) h z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (congrArg (fun t => t + 1) h)) (dPair b Y i z)
          : (CollRC b Y).homology (j + 1)) := by
  rw [transT_eq_eqToHom]
  exact dPair_eqToHom_cast b Y h z

/-- `transT` is additive. -/
private lemma transT_add {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v w : Work.Thom.Coh ℚ i Y) :
    transT Y h (v + w) = transT Y h v + transT Y h w := by
  rw [map_add]

/-- `transT` is `ℚ`-linear. -/
private lemma transT_smul {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j) (c : ℚ)
    (v : Work.Thom.Coh ℚ i Y) :
    transT Y h (c • v) = c • transT Y h v := by
  rw [map_smul]

/-- The definition of `collarSigma`. -/
private lemma collarSigma_eq (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ) (m : ℕ)
    (z : (CollKC b Y).homology (m + b)) :
    collarSigma b hb Y τ hτ m z
      = (LinearEquiv.ofBijective (collarPhi b Y τ (m + 1)) (hτ (m + 1))).symm
          (collarRelEq b Y m (collarDelta b Y m z)) := rfl


/-! ## The collar section kills the `s`-part -/

private lemma collarSection_collarSPart (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hσ : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (b - 1)).hom s = 0)
    (m : ℕ) (X : Work.Thom.Coh ℚ (m + b) ↥(sphLoopCollarProd b Y)) :
    (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + b)).hom
      (Work.StemsB.Rat.collarSPart b hb Y τ hτ s m X) = 0 := by
  have hk : (m + 1) + (b - 1) = m + b := by omega
  set sx := collarSigma b hb Y τ hτ m X with hsx
  set w := (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + 1) (b - 1))
      ((HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) (m + 1)).hom
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + 1)).hom sx)) s with hw
  have hsp : collarSPart b hb Y τ hτ s m X
      = CategoryTheory.eqToHom (congrArg (fun t => (CollKC b Y).homology t) hk)
          (((-1 : ℚ) ^ (m + 1)) • w) := by
    rw [collarSPart_apply b hb Y τ hτ s m X]
    rw [← hsx, collarProjC_eq_restr_apply, ← hw]
    exact collarRelEqS_apply b hb Y m hk _
  rw [hsp]
  rw [CohMap_eqToHom_homology (collarSection (Y := Y) b hb) hk]
  have hcup : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ ((m + 1) + (b - 1))).hom w
      = (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) (m + 1) (b - 1)
          ((Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + 1)).hom
            ((HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) (m + 1)).hom
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + 1)).hom sx)))
          ((Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (b - 1)).hom s)) := by
    rw [hw]
    exact Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarSection (Y := Y) b hb)) (m + 1) (b - 1) _ s
  have hw0 : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ ((m + 1) + (b - 1))).hom w
      = (0 : Work.Thom.Coh ℚ ((m + 1) + (b - 1)) Y) := by
    rw [hcup, hσ, Work.Cohomology.cupH'_zero_right]
  rw [CohMap_map_smul, hw0, smul_zero]
  exact map_zero _

/-! ## The base part of the splitting -/

private lemma collarSplit_base (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hσ : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (b - 1)).hom s = 0)
    (m : ℕ)
    (X : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥(sphLoopCollarProd b Y))).homology (m + b))
    (a : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))).homology (m + b))
    (ha : X - collarSPart b hb Y τ hτ s m X = collarRestr b Y (m + b) a) :
    a = (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + b)).hom
          ((Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + b)).hom X) := by
  have hsg : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + b)).hom
        (collarRestr b Y (m + b) a)
      = (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + b)).hom X := by
    rw [← ha, map_sub, collarSection_collarSPart b hb Y τ hτ s hσ m X, sub_zero]
  have hjs : (Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ (m + b)).hom a
      = (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (m + b)).hom X := by
    rw [← collarSection_collarRestr b hb (m + b) a]
    exact hsg
  haveI hI : IsIso (Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ (m + b)) :=
    isIso_collarSectionIncl (Y := Y) b hb (m + b)
  have hinj : Function.Injective
      (Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ (m + b)).hom := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  have h1 : (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + b)).hom
      ((Work.Thom.CohMap (collarSectionIncl (Y := Y) b hb) ℚ (m + b)).hom a) = a := by
    apply hinj
    rw [← LinearMap.comp_apply, collarSectionIncl_collarProjY b hb (m + b), LinearMap.id_apply]
  rw [hjs] at h1
  exact h1.symm

/-- **The derivation property of the collar transgression, at the level of `δ`.**

`δ (X ⌣ Y') = (-1)^{m+b} (π^*(σ^*X) ⌣ δ Y') + (-1)^{(m+b)(m'+b)+(m'+b)} (π^*(σ^*Y') ⌣ δ X)`,
the second term carrying the degree cast `((m'+b)+(m+b))+1 → ((m+b)+(m'+b))+1`. -/
private lemma collar_pairδ_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b hb (Y := Y) s τ)
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Thom.CohMap (collarSection (Y := Y) b hb) ℚ (b - 1)).hom s = 0)
    (m m' : ℕ) (X : (CollKC b Y).homology (m + b)) (Y' : (CollKC b Y).homology (m' + b)) :
    dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) X Y')
      = ((-1 : ℚ) ^ (m + b)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + b) ((m' + b) + 1))
            (piStar b Y (m + b) (sgStar b hb Y (m + b) X))
            (dPair b Y (m' + b) Y'))
        + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
              (congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm)))
            (((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
              ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m' + b) ((m + b) + 1))
                (piStar b Y (m' + b) (sgStar b hb Y (m' + b) Y'))
                (dPair b Y (m + b) X))) := by
  obtain ⟨a, ha⟩ := collarSplit b hb Y τ hτ s hs m X
  obtain ⟨b', hb'⟩ := collarSplit b hb Y τ hτ s hs m' Y'
  set u := collarSPart b hb Y τ hτ s m X with hu
  set v := collarSPart b hb Y τ hτ s m' Y' with hv
  have hae : a = piStar b Y (m + b) (sgStar b hb Y (m + b) X) :=
    collarSplit_base b hb Y τ hτ s hσ m X a ha
  have hbe : b' = piStar b Y (m' + b) (sgStar b hb Y (m' + b) Y') :=
    collarSplit_base b hb Y τ hτ s hσ m' Y' b' hb'
  have hX : X = iStar b Y (m + b) a + u := by
    rw [← sub_eq_iff_eq_add, hu]
    exact ha
  have hY' : Y' = iStar b Y (m' + b) b' + v := by
    rw [← sub_eq_iff_eq_add, hv]
    exact hb'
  have hW : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) X Y'
      = (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (iStar b Y (m + b) a) (iStar b Y (m' + b) b')
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          (iStar b Y (m + b) a) v
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
          u (iStar b Y (m' + b) b')
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) u v := by
    rw [hX, hY', Work.Cohomology.cupH'_add_left, Work.Cohomology.cupH'_add_right,
      Work.Cohomology.cupH'_add_right]
    abel
  have hD : dPair b Y ((m + b) + (m' + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) X Y')
      = dPair b Y ((m + b) + (m' + b))
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
            (iStar b Y (m + b) a) (iStar b Y (m' + b) b'))
        + dPair b Y ((m + b) + (m' + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
              (iStar b Y (m + b) a) v)
        + dPair b Y ((m + b) + (m' + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b))
              u (iStar b Y (m' + b) b'))
        + dPair b Y ((m + b) + (m' + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) u v) := by
    rw [hW, dPair_add, dPair_add, dPair_add]
  rw [hD, hu, hv]
  rw [collar_dPair_restr_cup b Y m m' a b',
    collar_dPair_restr_SPart b hb Y τ hτ s hs m m' X Y' a hae,
    collar_dPair_SPart_restr b hb Y τ hτ s hs m m' X Y' b' hbe,
    collar_dPair_SPart_cup b hb Y τ hτ s hssq m m' X Y']
  abel


/-- Composition of degree transports in the `CollRC` spelling. -/
private lemma CollRC_cast_comp (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j k : ℕ} (h : i = j)
    (h' : j = k) (z : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) (h.trans h'))) z := by
  cases h; cases h'; rfl

/-- Degree transports in the `CollRC` spelling are proof-irrelevant. -/
private lemma CollRC_cast_congr (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ}
    (h h' : i = j) (z : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h')) z := by
  rw [Subsingleton.elim h h']

/-- The inverse of a `CollRC`-transport. -/
private lemma CollRC_cast_symm (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (x : (CollRC b Y).homology j) (y : (CollRC b Y).homology i)
    (hxy : x = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) y) :
    y = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h.symm)) x := by
  rw [hxy]
  exact ((CollRC_cast_comp b Y h h.symm y).trans (by
    rw [CollRC_cast_congr b Y (h.trans h.symm) rfl]; rfl)).symm

/-- A transport of `CollRC` is additive. -/
private lemma CollRC_cast_add (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (x y : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) (x + y)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) x
        + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) y := by
  rw [map_add]

/-- A transport of `CollRC` is `ℚ`-linear. -/
private lemma CollRC_cast_smul (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (c : ℚ) (x : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) (c • x)
      = c • ((CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) x) := by
  rw [map_smul]

/-- Additivity of the mixed cup product in its absolute argument. -/
private lemma mixedCup_add_arg {X : Type} [TopologicalSpace X] (A : Set X) (i k : ℕ)
    (x y : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i k) (x + y) z
      = (Work.Thom.mixedCupC ℚ A i k) x z + (Work.Thom.mixedCupC ℚ A i k) y z := by
  rw [map_add, LinearMap.add_apply]

/-- `ℚ`-linearity of the mixed cup product in its absolute argument. -/
private lemma mixedCup_smul_arg {X : Type} [TopologicalSpace X] (A : Set X) (i k : ℕ)
    (c : ℚ) (x : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i k) (c • x) z = c • ((Work.Thom.mixedCupC ℚ A i k) x z) := by
  rw [map_smul]
  rfl

theorem collarSigma_cup_rat (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y)
          (Work.StemsB.sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (m m' : ℕ)
    (X : Work.Thom.Coh ℚ (m + b) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (Y' : Work.Thom.Coh ℚ (m' + b) ↥(Work.StemsB.sphLoopCollarProd b Y)) :
    Work.StemsB.Rat.transT Y (by omega : m + m' + b + 1 = (m + b) + (m' + 1))
        (Work.StemsB.Rat.collarSigma b (by omega) (Y := Y) τ hτ (m + m' + b)
          (Work.StemsB.Rat.transT ↥(Work.StemsB.sphLoopCollarProd b Y)
            (by omega : (m + b) + (m' + b) = (m + m' + b) + b)
            (Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (m + b) (m' + b) X Y')))
      = ((-1 : ℚ) ^ (m + b)) •
          Work.StemsB.Rat.cupT Y (m + b) (m' + 1)
            ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
              (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
              (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (m + b)).hom X)
            (Work.StemsB.Rat.collarSigma b (by omega) (Y := Y) τ hτ m' Y')
        + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
          Work.StemsB.Rat.transT Y (by omega : (m' + b) + (m + 1) = (m + b) + (m' + 1))
            (Work.StemsB.Rat.cupT Y (m' + b) (m + 1)
              ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
                (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
                (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (m' + b)).hom Y')
              (Work.StemsB.Rat.collarSigma b (by omega) (Y := Y) τ hτ m X)) := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (m + b) + (m' + b) = (m + m' + b) + b := by omega
  have h2 : m + m' + b + 1 = (m + b) + (m' + 1) := by omega
  have h3 : (m' + b) + (m + 1) = (m + b) + (m' + 1) := by omega
  have hcar : ((m + m' + b) + b) + 1 = (m + m' + b + 1) + b := by omega
  have hγ1 : ((m + b) + (m' + 1)) + b = (m + m' + b + 1) + b := by omega
  have hγ2 : ((m' + b) + (m + 1)) + b = (m + m' + b + 1) + b := by omega
  have hsh : (m' + b) + (m + b) = (m + b) + (m' + b) :=
    Nat.add_comm (m' + b) (m + b)
  -- the product of the two collar classes
  set W : (CollKC b Y).homology ((m + b) + (m' + b)) :=
      (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (m' + b)) X Y' with hW
  -- the two sphere-cup terms
  set T1 : (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (TopCat.of Y))).homology
        ((m + b) + (m' + 1)) :=
      (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) (m + b) (m' + 1))
        ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m + b)).hom X)
        (collarSigma b hb1 Y τ hτ m' Y') with hT1
  set T2 : (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (TopCat.of Y))).homology
        ((m' + b) + (m + 1)) :=
      (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) (m' + b) (m + 1))
        ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m' + b)).hom Y')
        (collarSigma b hb1 Y τ hτ m X) with hT2
  -- the pushed-forward target value, at degree `K + 1`
  set U : Work.Thom.Coh ℚ (m + m' + b + 1) Y :=
      ((-1 : ℚ) ^ (m + b)) • (transT Y h2.symm T1)
      + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
          (transT Y (h3.trans h2.symm) T2) with hU
  -- the two relative classes the computation ends at
  set Z1 : Work.Thom.RelCoh ℚ (((m + b) + (m' + 1)) + b)
      (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((m + b) + (m' + 1)) b)
        (piStar b Y ((m + b) + (m' + 1)) T1) τ with hZ1
  set Z2 : Work.Thom.RelCoh ℚ (((m' + b) + (m + 1)) + b)
      (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((m' + b) + (m + 1)) b)
        (piStar b Y ((m' + b) + (m + 1)) T2) τ with hZ2
  -- the common final form
  set Xfin : Work.Thom.RelCoh ℚ ((m + m' + b + 1) + b)
      (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      ((-1 : ℚ) ^ (m + b)) • ((CategoryTheory.eqToHom (congrArg (fun t =>
          Work.Thom.RelCoh ℚ t (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ1)) Z1)
      + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
          ((CategoryTheory.eqToHom (congrArg (fun t =>
            Work.Thom.RelCoh ℚ t (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ2)) Z2)
    with hXfin
  -- supplementary degrees
  have hcar1' : (m + b) + 1 = (m + 1) + b := by omega
  have hcar2' : (m' + b) + 1 = (m' + 1) + b := by omega
  -- the two `collarPhi`-images of the transgressions
  set Z1' : Work.Thom.RelCoh ℚ ((m' + 1) + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      collarPhi b Y τ (m' + 1) (collarSigma b hb1 Y τ hτ m' Y') with hZ1'
  set Z2' : Work.Thom.RelCoh ℚ ((m + 1) + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      collarPhi b Y τ (m + 1) (collarSigma b hb1 Y τ hτ m X) with hZ2'
  -- the two `δ`-images, in the `Thom.mixedCupC` spelling
  set M1 : Work.Thom.RelCoh ℚ ((m + b) + ((m' + b) + 1))
      (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + b) ((m' + b) + 1))
        (piStar b Y (m + b) (sgStar b hb1 Y (m + b) X))
        (dPair b Y (m' + b) Y') with hM1def
  set M2 : Work.Thom.RelCoh ℚ ((m' + b) + ((m + b) + 1))
      (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m' + b) ((m + b) + 1))
        (piStar b Y (m' + b) (sgStar b hb1 Y (m' + b) Y'))
        (dPair b Y (m + b) X) with hM2def
  -- ### The left-hand chain
  have hL : collarPhi b Y τ (m + m' + b + 1) U = Xfin := by
    rw [hU, collarPhi_apply]
    have hp : piStar b Y (m + m' + b + 1)
          (((-1 : ℚ) ^ (m + b)) • (transT Y h2.symm T1)
            + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) • (transT Y (h3.trans h2.symm) T2))
        = ((-1 : ℚ) ^ (m + b)) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) h2.symm)) (piStar b Y ((m + b) + (m' + 1)) T1))
          + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) (h3.trans h2.symm)))
              (piStar b Y ((m' + b) + (m + 1)) T2)) := by
      rw [map_add, map_smul, map_smul, piStar_transT, piStar_transT]
    rw [hp]
    have f1 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + m' + b + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) h2.symm)) (piStar b Y ((m + b) + (m' + 1)) T1)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) h2.symm b
        (piStar b Y ((m + b) + (m' + 1)) T1), ← hZ1]
    have f2 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + m' + b + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) (h3.trans h2.symm)))
            (piStar b Y ((m' + b) + (m + 1)) T2)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (h3.trans h2.symm))) Z2 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) (h3.trans h2.symm) b
        (piStar b Y ((m' + b) + (m + 1)) T2), ← hZ2]
    have g1 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ1)) Z1 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) h2.symm hγ1 Z1
    have g2 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (h3.trans h2.symm))) Z2
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ2)) Z2 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) (h3.trans h2.symm) hγ2 Z2
    rw [mixedCup_add_arg, mixedCup_smul_arg, mixedCup_smul_arg, f1, f2, g1, g2, hXfin]
  -- ### The right-hand chain
  have hR : collarRelEq b Y (m + m' + b)
        (collarDelta b Y (m + m' + b) (transT ↥(sphLoopCollarProd b Y) h1 W)) = Xfin := by
    rw [show collarDelta b Y (m + m' + b) = dPair b Y ((m + m' + b) + b) from rfl]
    rw [collarRelEq_apply b Y (m + m' + b) hcar]
    rw [dPair_transT b Y h1 W]
    rw [CollRC_cast_comp b Y (congrArg (fun t => t + 1) h1) hcar
      (dPair b Y ((m + b) + (m' + b)) W)]
    -- the core computation
    have e3 : dPair b Y ((m + b) + (m' + b)) W
        = ((-1 : ℚ) ^ (m + b)) • M1
          + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
              (congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm)))
            (((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) • M2) := by
      rw [hW, hM1def, hM2def,
        Work.StemsB.Rat.mixedCupC_eq_mixedCup b Y (m + b) ((m' + b) + 1),
        Work.StemsB.Rat.mixedCupC_eq_mixedCup b Y (m' + b) ((m + b) + 1)]
      exact collar_pairδ_cup b hb1 Y τ hτ s hs hssq hσ m m' X Y'
    rw [e3]
    rw [CollRC_cast_add (b := b) (Y := Y)
      ((congrArg (fun t => t + 1) h1).trans hcar),
      CollRC_cast_smul (b := b) (Y := Y)
        ((congrArg (fun t => t + 1) h1).trans hcar)]
    rw [CollRC_cast_comp b Y
      (congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm)
      ((congrArg (fun t => t + 1) h1).trans hcar) _,
      CollRC_cast_smul (b := b) (Y := Y)
        ((congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm).trans
          ((congrArg (fun t => t + 1) h1).trans hcar))]
    -- compute the two `δ`-images
    have hd1 : dPair b Y (m' + b) Y'
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar2'.symm)) Z1' := by
      refine CollRC_cast_symm b Y hcar2' Z1' (dPair b Y (m' + b) Y') ?_
      rw [show Z1' = collarPhi b Y τ (m' + 1) (collarSigma b hb1 Y τ hτ m' Y') from hZ1']
      rw [collarSigma_spec b hb1 Y τ hτ m' Y']
      exact (collarRelEq_apply b Y m' hcar2' (dPair b Y (m' + b) Y')).symm
    have hd2 : dPair b Y (m + b) X
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar1'.symm)) Z2' := by
      refine CollRC_cast_symm b Y hcar1' Z2' (dPair b Y (m + b) X) ?_
      rw [show Z2' = collarPhi b Y τ (m + 1) (collarSigma b hb1 Y τ hτ m X) from hZ2']
      rw [collarSigma_spec b hb1 Y τ hτ m X]
      exact (collarRelEq_apply b Y m hcar1' (dPair b Y (m + b) X)).symm
    have hA1eq : ((m + b) + (m' + 1)) + b = (m + b) + ((m' + b) + 1) := by omega
    have hA2eq : ((m' + b) + (m + 1)) + b = (m' + b) + ((m + b) + 1) := by omega
    have hM1c : M1 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA1eq)) Z1 := by
      rw [hM1def]
      rw [hd1]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (m + b) hcar2'.symm
        (piStar b Y (m + b) (sgStar b hb1 Y (m + b) X)) Z1']
      rw [show Z1' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m' + 1) b)
            (piStar b Y (m' + 1) (collarSigma b hb1 Y τ hτ m' Y')) τ from by
          rw [hZ1', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (m + b) (m' + 1) b
        (piStar b Y (m + b) (sgStar b hb1 Y (m + b) X))
        (piStar b Y (m' + 1) (collarSigma b hb1 Y τ hτ m' Y')) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar2'.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (m + b) (m' + 1) b)
        (congrArg (fun t => (m + b) + t) hcar2'.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (m + b) (m' + 1))
            (piStar b Y (m + b) (sgStar b hb1 Y (m + b) X))
            (piStar b Y (m' + 1) (collarSigma b hb1 Y τ hτ m' Y'))
          = piStar b Y ((m + b) + (m' + 1)) T1 from by
        rw [hT1]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (m + b) (m' + 1) ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m + b)).hom X)
          (collarSigma b hb1 Y τ hτ m' Y')).symm]
    have hM2c : M2 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA2eq)) Z2 := by
      rw [hM2def]
      rw [hd2]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (m' + b) hcar1'.symm
        (piStar b Y (m' + b) (sgStar b hb1 Y (m' + b) Y')) Z2']
      rw [show Z2' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + 1) b)
            (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m X)) τ from by
          rw [hZ2', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (m' + b) (m + 1) b
        (piStar b Y (m' + b) (sgStar b hb1 Y (m' + b) Y'))
        (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m X)) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar1'.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (m' + b) (m + 1) b)
        (congrArg (fun t => (m' + b) + t) hcar1'.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (m' + b) (m + 1))
            (piStar b Y (m' + b) (sgStar b hb1 Y (m' + b) Y'))
            (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m X))
          = piStar b Y ((m' + b) + (m + 1)) T2 from by
        rw [hT2]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (m' + b) (m + 1) ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m' + b)).hom Y')
          (collarSigma b hb1 Y τ hτ m X)).symm]
    -- assemble
    have h1eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) h1).trans hcar))) M1
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hγ1)) Z1 := by
      rw [hM1c]
      exact (CollRC_cast_comp b Y hA1eq ((congrArg (fun t => t + 1) h1).trans hcar) Z1).trans
        (CollRC_cast_congr b Y (hA1eq.trans ((congrArg (fun t => t + 1) h1).trans hcar)) hγ1 Z1)
    have h2eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm).trans
          ((congrArg (fun t => t + 1) h1).trans hcar)))) M2
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hγ2)) Z2 := by
      rw [hM2c]
      exact (CollRC_cast_comp b Y hA2eq
          ((congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm).trans
            ((congrArg (fun t => t + 1) h1).trans hcar)) Z2).trans
        (CollRC_cast_congr b Y (hA2eq.trans
          ((congrArg (fun t => t + 1) (Nat.add_comm (m + b) (m' + b)).symm).trans
            ((congrArg (fun t => t + 1) h1).trans hcar))) hγ2 Z2)
    rw [h1eq, h2eq, hXfin]
  -- ### Assembly
  have hmain : collarPhi b Y τ (m + m' + b + 1) U
      = collarRelEq b Y (m + m' + b)
          (collarDelta b Y (m + m' + b) (transT ↥(sphLoopCollarProd b Y) h1 W)) :=
    hL.trans hR.symm
  have hSig : collarSigma b hb1 Y τ hτ (m + m' + b) (transT ↥(sphLoopCollarProd b Y) h1 W)
      = U := by
    rw [collarSigma_eq b hb1 Y τ hτ (m + m' + b)]
    rw [show (LinearEquiv.ofBijective (collarPhi b Y τ (m + m' + b + 1))
          (hτ (m + m' + b + 1))).symm
        (collarRelEq b Y (m + m' + b)
          (collarDelta b Y (m + m' + b) (transT ↥(sphLoopCollarProd b Y) h1 W))) = U from by
      rw [← hmain]
      exact LinearEquiv.symm_apply_apply
        (LinearEquiv.ofBijective (collarPhi b Y τ (m + m' + b + 1)) (hτ (m + m' + b + 1))) U]
  have hUgoal : transT Y h2 U
      = ((-1 : ℚ) ^ (m + b)) • T1
        + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) • transT Y h3 T2 := by
    rw [hU, transT_add, transT_smul, transT_smul, transT_comp, transT_comp,
      transT_self, transT_congr ((h3.trans h2.symm).trans h2) h3]
  have hgoal : transT Y h2 (collarSigma b hb1 Y τ hτ (m + m' + b)
        (transT ↥(sphLoopCollarProd b Y) h1 W))
      = ((-1 : ℚ) ^ (m + b)) • T1
        + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) • transT Y h3 T2 := by
    rw [hSig, hUgoal]
  -- convert the goal
  show transT Y (by omega : m + m' + b + 1 = (m + b) + (m' + 1))
      (collarSigma b hb1 Y τ hτ (m + m' + b) (transT ↥(sphLoopCollarProd b Y) h1 W))
    = ((-1 : ℚ) ^ (m + b)) • T1
      + ((-1 : ℚ) ^ ((m + b) * (m' + b) + (m' + b))) • transT Y h3 T2
  exact hgoal


end

end Work.StemsB.Rat
