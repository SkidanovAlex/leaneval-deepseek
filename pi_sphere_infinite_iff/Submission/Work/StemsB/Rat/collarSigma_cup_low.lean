import Mathlib
import Submission.Work.StemsB.Rat.CollarSigmaLow
import Submission.Work.StemsB.Rat.collarDPairCupLow
import Submission.Work.StemsB.pairDelta_mixedCup_general_R
import Submission.Work.Cohomology.gradedComm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB.Rat

noncomputable section

/-! ## Degree-transport plumbing

All of this is the low-degree copy of the private plumbing of
`Submission/Work/StemsB/Rat/CollarSigmaCup.lean`. -/

/-- The singular cochain complex of the collar, in the `SSetCochainComplex` spelling. -/
private abbrev CollKCx (b : ℕ) (Y : Type) [TopologicalSpace Y] : CochainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (CollC b Y))

/-- `π^* : H^k(Y) → H^k(Q)`. -/
private abbrev piStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ k).hom

/-- `σ^* : H^k(C) → H^k(Y)`. -/
private abbrev sgStar (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b hb) ℚ k).hom

/-- `i^* : H^k(Q) → H^k(C)`. -/
private abbrev iStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) k).hom

/-- `δ : H^k(C) → H^{k+1}(Q,C)`. -/
private abbrev dPair (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :=
  (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) k).hom

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

private lemma CohMap_map_smul {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X', Y')) (n : ℕ) (c : ℚ)
    (z : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y')).homology n) :
    (Work.Thom.CohMap f ℚ n).hom (c • z) = c • ((Work.Thom.CohMap f ℚ n).hom z) := by
  rw [map_smul]

private lemma Coh_cast_comp {X : Type} [TopologicalSpace X] {i j k : ℕ} (h : i = j) (h' : j = k)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) (h.trans h'))) z := by
  cases h; cases h'; rfl

private lemma Coh_cast_congr {X : Type} [TopologicalSpace X] {i j : ℕ} (h h' : i = j)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h')) z := by
  rw [Subsingleton.elim h h']

private lemma Coh_cast_self {X : Type} [TopologicalSpace X] {i : ℕ} (h : i = i)
    (z : Work.Thom.Coh ℚ i X) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) z = z := by
  rw [Subsingleton.elim h rfl]; rfl

private lemma RelCoh_cast_comp {X : Type} [TopologicalSpace X] (A : Set X) {i j k : ℕ}
    (h : i = j) (h' : j = k) (z : Work.Thom.RelCoh ℚ i X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (h.trans h'))) z := by
  cases h; cases h'; rfl

private lemma RelCoh_cast_congr {X : Type} [TopologicalSpace X] (A : Set X) {i j : ℕ}
    (h h' : i = j) (z : Work.Thom.RelCoh ℚ i X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h')) z := by
  rw [Subsingleton.elim h h']

private lemma RelCoh_cast_shift {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) :
    congrArg (fun t => Work.Thom.RelCoh ℚ (t + c) X A) h
      = congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (congrArg (fun t => t + c) h) := by
  cases h; rfl

private lemma RelCoh_cast_shiftL {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) :
    congrArg (fun t => Work.Thom.RelCoh ℚ (c + t) X A) h
      = congrArg (fun t => Work.Thom.RelCoh ℚ t X A) (congrArg (fun t => c + t) h) := by
  cases h; rfl

private lemma RelCoh_cast_shift_apply {X : Type} [TopologicalSpace X] (A : Set X) {i j c : ℕ}
    (h : i = j) (h' : i + c = j + c) (z : Work.Thom.RelCoh ℚ (i + c) X A) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + c) X A) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h')) z := by
  rw [RelCoh_cast_shift A h]

private lemma RelCoh_cast_eqToHom {X : Type} [TopologicalSpace X] (A : Set X) {i j : ℕ}
    (h : i = j) (z : Work.Thom.RelCoh ℚ i X A) :
    h ▸ z = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z := by
  cases h; rfl

private lemma transT_comp {Y : Type} [TopologicalSpace Y] {k l j : ℕ} (h : k = l) (h' : l = j)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h' (transT Y h v) = transT Y (h.trans h') v := by
  cases h; cases h'; rfl

private lemma transT_congr {Y : Type} [TopologicalSpace Y] {k l : ℕ} (h h' : k = l)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h v = transT Y h' v := by
  rw [Subsingleton.elim h h']

private lemma transT_self {Y : Type} [TopologicalSpace Y] {k : ℕ} (h : k = k)
    (v : Work.Thom.Coh ℚ k Y) : transT Y h v = v := by
  rw [transT_congr h rfl]; rfl

private lemma transT_add {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v w : Work.Thom.Coh ℚ i Y) :
    transT Y h (v + w) = transT Y h v + transT Y h w := by
  rw [map_add]

private lemma transT_smul {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j) (c : ℚ)
    (v : Work.Thom.Coh ℚ i Y) :
    transT Y h (c • v) = c • transT Y h v := by
  rw [map_smul]

private lemma piStar_transT (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v : Work.Thom.Coh ℚ i Y) :
    piStar b Y j (transT Y h v)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t (↥(sphLoopBig b) × Y)) h))
          (piStar b Y i v) := by
  rw [transT_eq_eqToHom]
  exact CohMap_eqToHom_homology (collarProjY (Y := Y) b) h v

private lemma mixedCupC_cast_left {X : Type} [TopologicalSpace X] (A : Set X) {i i' : ℕ}
    (h : i = i') (k : ℕ) (x : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i' k)
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t X) h)) x) z
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + k) X A) h))
          ((Work.Thom.mixedCupC ℚ A i k) x z) := by
  cases h; rfl

private lemma mixedCupC_cast_right' {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    {k k' : ℕ} (h : k = k') (a : Work.Thom.Coh ℚ m X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m k') a
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t X A) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (m + t) X A) h))
          ((Work.Thom.mixedCupC ℚ A m k) a z) := by
  cases h; rfl

private lemma mixedCup_add_arg {X : Type} [TopologicalSpace X] (A : Set X) (i k : ℕ)
    (x y : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i k) (x + y) z
      = (Work.Thom.mixedCupC ℚ A i k) x z + (Work.Thom.mixedCupC ℚ A i k) y z := by
  rw [map_add, LinearMap.add_apply]

private lemma mixedCup_smul_arg {X : Type} [TopologicalSpace X] (A : Set X) (i k : ℕ)
    (c : ℚ) (x : Work.Thom.Coh ℚ i X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A i k) (c • x) z = c • ((Work.Thom.mixedCupC ℚ A i k) x z) := by
  rw [map_smul]
  rfl

private lemma CollRC_cast_comp (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j k : ℕ} (h : i = j)
    (h' : j = k) (z : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h'))
        ((CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) (h.trans h'))) z := by
  cases h; cases h'; rfl

private lemma CollRC_cast_congr (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ}
    (h h' : i = j) (z : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) z
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h')) z := by
  rw [Subsingleton.elim h h']

private lemma CollRC_cast_symm (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (x : (CollRC b Y).homology j) (y : (CollRC b Y).homology i)
    (hxy : x = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) y) :
    y = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h.symm)) x := by
  rw [hxy]
  exact ((CollRC_cast_comp b Y h h.symm y).trans (by
    rw [CollRC_cast_congr b Y (h.trans h.symm) rfl]; rfl)).symm

private lemma CollRC_cast_add (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (x y : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) (x + y)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) x
        + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) y := by
  rw [map_add]

private lemma CollRC_cast_smul (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (c : ℚ) (x : (CollRC b Y).homology i) :
    (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) (c • x)
      = c • ((CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) h)) x) := by
  rw [map_smul]

private lemma dPair_transT (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (z : (CollKC b Y).homology i) :
    dPair b Y j (transT ↥(sphLoopCollarProd b Y) h z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (congrArg (fun t => t + 1) h)) (dPair b Y i z)
          : (CollRC b Y).homology (j + 1)) := by
  rw [transT_eq_eqToHom]
  cases h; rfl

private lemma dPair_eqToHom_cast (b : ℕ) (Y : Type) [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (z : (CollKCx b Y).homology i) :
    dPair b Y j
        ((CategoryTheory.eqToHom (congrArg (fun t => (CollKCx b Y).homology t) h)) z)
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (congrArg (fun t => t + 1) h)) (dPair b Y i z)
          : (CollRC b Y).homology (j + 1)) := by
  cases h; rfl

private lemma dPair_add (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (x y : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥(CollA b Y))).homology k) :
    dPair b Y k (x + y) = dPair b Y k x + dPair b Y k y := by
  rw [map_add]

private lemma dPair_smul (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) (c : ℚ)
    (z : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥(CollA b Y))).homology k) :
    dPair b Y k (c • z) = c • dPair b Y k z := by
  rw [map_smul]


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

/-- The definition of `collarSigma`, in the `pairδ` spelling. -/
private lemma collarSigma_eq (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ) (m : ℕ)
    (z : (CollKC b Y).homology (m + b)) :
    collarSigma b hb Y τ hτ m z
      = (LinearEquiv.ofBijective (collarPhi b Y τ (m + 1)) (hτ (m + 1))).symm
          (collarRelEq b Y m (collarDelta b Y m z)) := rfl

/-- The computation rule of `relCohZeroAdd`. -/
private lemma relCohZeroAdd_eqToHom (b : ℕ) (Y : Type) [TopologicalSpace Y]
    (z : (CollRC b Y).homology b) :
    relCohZeroAdd (Y := Y) b z
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (Nat.zero_add b).symm)) z := rfl

/-- The computation rule of `collarDeltaLow`. -/
private lemma collarDeltaLow_eqToHom (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (x : (CollKC b Y).homology (b - 1)) :
    collarDeltaLow b hb Y x
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (lowCast b hb))) (dPair b Y (b - 1) x) := rfl

/-! ## The `δ`-computation in degree `b - 1` -/

/-- **The one-sided derivation property in the top fibre degree.** -/
private lemma collarDPairCupLow_priv (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : Work.StemsB.Rat.cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (X X' : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y)) :
    dPair b Y ((b - 1) + (b - 1)) ((Work.Cohomology.cupH' ℚ
        (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) X X')
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            (piStar b Y (b - 1) (sgStar b (by omega) Y (b - 1) X))
            (dPair b Y (b - 1) X'))
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            (piStar b Y (b - 1) (sgStar b (by omega) Y (b - 1) X'))
            (dPair b Y (b - 1) X)) :=
  Work.StemsB.Rat.collarDPairCupLow b hb Y τ hτ s hs hssq hσ X X'
/-! ## The main theorem -/

theorem collarSigma_cup_low (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y)
          (Work.StemsB.sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (X X' : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y)) :
    Work.StemsB.Rat.transT Y (by omega : (b - 2) + 1 = (b - 1) + 0)
        (Work.StemsB.Rat.collarSigma b (by omega) (Y := Y) τ hτ (b - 2)
          (Work.StemsB.Rat.transT ↥(Work.StemsB.sphLoopCollarProd b Y)
            (by omega : (b - 1) + (b - 1) = (b - 2) + b)
            (Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (b - 1) X X')))
      = ((-1 : ℚ) ^ (b - 1)) •
          Work.StemsB.Rat.cupT Y (b - 1) 0
            ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (b - 1)).hom X)
            (Work.StemsB.Rat.collarSigmaLow b (by omega) Y τ hτ X')
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
            Work.StemsB.Rat.transT Y (rfl : (b - 1) + 0 = (b - 1) + 0)
              (Work.StemsB.Rat.cupT Y (b - 1) 0
                ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (b - 1)).hom X')
                (Work.StemsB.Rat.collarSigmaLow b (by omega) Y τ hτ X)) := by
  have hb1 : 1 ≤ b := by omega
  -- the degree identities
  have h1 : (b - 1) + (b - 1) = (b - 2) + b := by omega
  have h2 : (b - 2) + 1 = (b - 1) + 0 := by omega
  have hcar : ((b - 2) + b) + 1 = ((b - 2) + 1) + b := by omega
  have hcar1' : (b - 1) + 1 = 0 + b := by omega
  have hcar2' : (b - 1) + 1 = 0 + b := by omega
  have hg1 : ((b - 1) + 0) + b = ((b - 2) + 1) + b := by omega
  have hg2 : ((b - 1) + 0) + b = ((b - 2) + 1) + b := by omega
  have hA1eq : ((b - 1) + 0) + b = (b - 1) + ((b - 1) + 1) := by omega
  have hA2eq : ((b - 1) + 0) + b = (b - 1) + ((b - 1) + 1) := by omega
  -- the collar class
  set W : (CollKCx b Y).homology ((b - 1) + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) X X' with hW
  set Wc : (CollKC b Y).homology ((b - 2) + b) :=
    transT ↥(sphLoopCollarProd b Y) h1 W with hWc
  -- the two sphere-cup terms
  set T1 : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (TopCat.of Y))).homology ((b - 1) + 0) :=
    (Work.StemsB.Rat.cupT Y (b - 1) 0) (sgStar b hb1 Y (b - 1) X)
      (collarSigmaLow b hb1 Y τ hτ X') with hT1
  set T2 : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (TopCat.of Y))).homology ((b - 1) + 0) :=
    (Work.StemsB.Rat.cupT Y (b - 1) 0) (sgStar b hb1 Y (b - 1) X')
      (collarSigmaLow b hb1 Y τ hτ X) with hT2
  -- the pushed-forward target value, at degree `(b - 2) + 1`
  set U : Work.Thom.Coh ℚ ((b - 2) + 1) Y :=
    ((-1 : ℚ) ^ (b - 1)) • (transT Y h2.symm T1)
      + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) • (transT Y h2.symm T2) with hU
  -- the two relative classes the computation ends at
  set Z1 : Work.Thom.RelCoh ℚ (((b - 1) + 0) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((b - 1) + 0) b)
      (piStar b Y ((b - 1) + 0) T1) τ with hZ1
  set Z2 : Work.Thom.RelCoh ℚ (((b - 1) + 0) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((b - 1) + 0) b)
      (piStar b Y ((b - 1) + 0) T2) τ with hZ2
  -- the common final form
  set Xfin : Work.Thom.RelCoh ℚ (((b - 2) + 1) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    ((-1 : ℚ) ^ (b - 1)) •
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hg1)) Z1)
      + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hg2)) Z2) with hXfin
  -- the core terms of the `δ`-computation
  set M1 : Work.Thom.RelCoh ℚ ((b - 1) + ((b - 1) + 1)) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (b - 1) ((b - 1) + 1))
      (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X)) (dPair b Y (b - 1) X') with hM1def
  set M2 : Work.Thom.RelCoh ℚ ((b - 1) + ((b - 1) + 1)) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (b - 1) ((b - 1) + 1))
      (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X')) (dPair b Y (b - 1) X) with hM2def
  -- the two `δ`-images
  set Z1' : Work.Thom.RelCoh ℚ (0 + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X') with hZ1'
  set Z2' : Work.Thom.RelCoh ℚ (0 + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X) with hZ2'
  -- ### The left-hand chain
  have hL : collarPhi b Y τ ((b - 2) + 1) U = Xfin := by
    rw [hU, collarPhi_apply]
    have hp : piStar b Y ((b - 2) + 1)
          (((-1 : ℚ) ^ (b - 1)) • (transT Y h2.symm T1)
            + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) • (transT Y h2.symm T2))
        = ((-1 : ℚ) ^ (b - 1)) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) h2.symm)) ((piStar b Y ((b - 1) + 0)) T1))
          + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) h2.symm)) ((piStar b Y ((b - 1) + 0)) T2)) := by
      rw [map_add, map_smul, map_smul, piStar_transT, piStar_transT]
    rw [hp]
    have f1 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((b - 2) + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) h2.symm)) ((piStar b Y ((b - 1) + 0)) T1)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) h2.symm b
        ((piStar b Y ((b - 1) + 0)) T1), ← hZ1]
    have f2 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((b - 2) + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) h2.symm)) ((piStar b Y ((b - 1) + 0)) T2)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z2 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) h2.symm b
        ((piStar b Y ((b - 1) + 0)) T2), ← hZ2]
    have gg1 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hg1)) Z1 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) h2.symm hg1 Z1
    have gg2 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z2
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hg2)) Z2 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) h2.symm hg2 Z2
    rw [mixedCup_add_arg, mixedCup_smul_arg, mixedCup_smul_arg, f1, f2, gg1, gg2, hXfin]
  -- ### The core `δ`-computation
  have hcore : dPair b Y ((b - 1) + (b - 1)) ((Work.Cohomology.cupH' ℚ
      (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) X X')
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X))
            (dPair b Y (b - 1) X'))
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X'))
            (dPair b Y (b - 1) X)) := by
    exact collarDPairCupLow_priv b hb Y τ hτ s hs hssq hσ X X'
  -- ### The right-hand chain
  have hR : collarRelEq b Y (b - 2) (collarDelta b Y (b - 2) Wc) = Xfin := by
    rw [show collarDelta b Y (b - 2) = dPair b Y ((b - 2) + b) from rfl]
    rw [collarRelEq_apply b Y (b - 2) hcar]
    rw [show Wc = transT ↥(sphLoopCollarProd b Y) h1 W from hWc]
    rw [dPair_transT b Y h1 W]
    rw [CollRC_cast_comp b Y (congrArg (fun t => t + 1) h1) hcar
      (dPair b Y ((b - 1) + (b - 1)) W)]
    have e3 : dPair b Y ((b - 1) + (b - 1)) W
        = ((-1 : ℚ) ^ (b - 1)) • M1
          + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) • M2 := by
      rw [hW, hM1def, hM2def]
      exact hcore
    rw [e3]
    rw [CollRC_cast_add (b := b) (Y := Y) ((congrArg (fun t => t + 1) h1).trans hcar),
        CollRC_cast_smul (b := b) (Y := Y) ((congrArg (fun t => t + 1) h1).trans hcar),
        CollRC_cast_smul (b := b) (Y := Y) ((congrArg (fun t => t + 1) h1).trans hcar)]
    -- compute the two `δ`-images
    have hd1 : dPair b Y (b - 1) X'
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar2'.symm)) Z1' := by
      refine CollRC_cast_symm b Y hcar2' Z1' (dPair b Y (b - 1) X') ?_
      rw [show Z1' = collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X') from hZ1']
      rw [collarSigmaLow_spec b hb1 Y τ hτ X', relCohZeroAdd_eqToHom, collarDeltaLow_eqToHom]
      exact (CollRC_cast_comp b Y (lowCast b hb1) (Nat.zero_add b).symm
        (dPair b Y (b - 1) X')).trans
        (CollRC_cast_congr b Y ((lowCast b hb1).trans (Nat.zero_add b).symm) hcar2'
          (dPair b Y (b - 1) X'))
    have hd2 : dPair b Y (b - 1) X
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar1'.symm)) Z2' := by
      refine CollRC_cast_symm b Y hcar1' Z2' (dPair b Y (b - 1) X) ?_
      rw [show Z2' = collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X) from hZ2']
      rw [collarSigmaLow_spec b hb1 Y τ hτ X, relCohZeroAdd_eqToHom, collarDeltaLow_eqToHom]
      exact (CollRC_cast_comp b Y (lowCast b hb1) (Nat.zero_add b).symm
        (dPair b Y (b - 1) X)).trans
        (CollRC_cast_congr b Y ((lowCast b hb1).trans (Nat.zero_add b).symm) hcar1'
          (dPair b Y (b - 1) X))
    have hM1c : M1 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA1eq)) Z1 := by
      rw [hM1def, hd1]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (b - 1) hcar2'.symm
        ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X)) Z1']
      rw [show Z1' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
            ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X')) τ from by
          rw [hZ1', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (b - 1) 0 b
        ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X))
        ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X')) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar2'.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (b - 1) 0 b)
        (congrArg (fun t => (b - 1) + t) hcar2'.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (b - 1) 0)
            ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X))
            ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X'))
          = (piStar b Y ((b - 1) + 0)) T1 from by
        rw [hT1]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (b - 1) 0 ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b hb1) ℚ (b - 1)).hom X)
          (collarSigmaLow b hb1 Y τ hτ X')).symm]
    have hM2c : M2 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA2eq)) Z2 := by
      rw [hM2def, hd2]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (b - 1) hcar1'.symm
        ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X')) Z2']
      rw [show Z2' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
            ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X)) τ from by
          rw [hZ2', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (b - 1) 0 b
        ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X'))
        ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X)) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar1'.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (b - 1) 0 b)
        (congrArg (fun t => (b - 1) + t) hcar1'.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (b - 1) 0)
            ((piStar b Y (b - 1)) (sgStar b hb1 Y (b - 1) X'))
            ((piStar b Y 0) (collarSigmaLow b hb1 Y τ hτ X))
          = (piStar b Y ((b - 1) + 0)) T2 from by
        rw [hT2]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (b - 1) 0 ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b hb1) ℚ (b - 1)).hom X')
          (collarSigmaLow b hb1 Y τ hτ X)).symm]
    have h1eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) h1).trans hcar))) M1
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hg1)) Z1 := by
      rw [hM1c]
      exact (CollRC_cast_comp b Y hA1eq ((congrArg (fun t => t + 1) h1).trans hcar) Z1).trans
        (CollRC_cast_congr b Y (hA1eq.trans ((congrArg (fun t => t + 1) h1).trans hcar)) hg1 Z1)
    have h2eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) h1).trans hcar))) M2
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hg2)) Z2 := by
      rw [hM2c]
      exact (CollRC_cast_comp b Y hA2eq ((congrArg (fun t => t + 1) h1).trans hcar) Z2).trans
        (CollRC_cast_congr b Y (hA2eq.trans ((congrArg (fun t => t + 1) h1).trans hcar)) hg2 Z2)
    rw [h1eq, h2eq, hXfin]
  -- ### Assembly
  have hmain : collarPhi b Y τ ((b - 2) + 1) U
      = collarRelEq b Y (b - 2) (collarDelta b Y (b - 2) Wc) := hL.trans hR.symm
  have hSig : collarSigma b hb1 Y τ hτ (b - 2) Wc = U := by
    rw [collarSigma_eq b hb1 Y τ hτ (b - 2)]
    rw [show (LinearEquiv.ofBijective (collarPhi b Y τ ((b - 2) + 1))
          (hτ ((b - 2) + 1))).symm
        (collarRelEq b Y (b - 2) (collarDelta b Y (b - 2) Wc)) = U from by
      rw [← hmain]
      exact LinearEquiv.symm_apply_apply
        (LinearEquiv.ofBijective (collarPhi b Y τ ((b - 2) + 1)) (hτ ((b - 2) + 1))) U]
  have hUgoal : transT Y h2 U
      = ((-1 : ℚ) ^ (b - 1)) • T1
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
            transT Y (rfl : (b - 1) + 0 = (b - 1) + 0) T2 := by
    rw [hU, transT_add, transT_smul, transT_smul, transT_comp, transT_comp]
    rw [transT_congr (h2.symm.trans h2) rfl T1, transT_self rfl T1]
  show transT Y h2 (collarSigma b hb1 Y τ hτ (b - 2) Wc)
      = ((-1 : ℚ) ^ (b - 1)) • T1
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
            transT Y (rfl : (b - 1) + 0 = (b - 1) + 0) T2
  rw [hSig, hUgoal]

end

end Work.StemsB.Rat
