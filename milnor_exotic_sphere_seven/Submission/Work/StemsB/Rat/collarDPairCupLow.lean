import Mathlib
import Submission.Work.StemsB.Rat.CollarSigmaLow
import Submission.Work.StemsB.pairDelta_mixedCup_general_R
import Submission.Work.Cohomology.gradedComm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB.Rat

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

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



/-! ## The `δ`-computation in the top degree -/

/-- `σ^* ∘ i^*` is the pullback along the section of the inner cube. -/
private lemma collarSection_collarRestr_low (b : ℕ) (hb : 1 ≤ b) (n : ℕ)
    (z : Work.Thom.Coh ℚ n (↥(sphLoopBig b) × Y)) :
    (Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b hb) ℚ n).hom
        (collarRestr (Y := Y) b n z)
      = (Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ n).hom z := by
  have h' : ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
        (TopCat.of (↥(sphLoopBig b) × Y))
        (TopCat.ofHom (Work.StemsB.collarSectionIncl (Y := Y) b hb)) n).hom)
      = ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b hb)) n).hom).comp
        ((Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(sphLoopCollarProd b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) n).hom) := by
    have h := Work.Cohomology.singularCohomologyMap_comp ℚ
      (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b hb))
      (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) n
    rw [Work.StemsB.collarSection_comp_subtypeIncl (Y := Y) b hb] at h
    have h2 := congrArg ModuleCat.Hom.hom h
    simpa only [ModuleCat.hom_comp] using h2
  rw [show collarRestr (Y := Y) b n
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(sphLoopCollarProd b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y))
            (sphLoopCollarProd b Y)) n).hom from rfl]
  rw [show (Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ n).hom
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y) (TopCat.of (↥(sphLoopBig b) × Y))
          (TopCat.ofHom (Work.StemsB.collarSectionIncl (Y := Y) b hb)) n).hom from rfl]
  rw [h']
  rfl

/-- `π^* ∘ (σ^* ∘ i^*) = id`: the section is a homotopy section of the projection. -/
private lemma collarSectionIncl_collarProjY_low (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    ((Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ n).hom).comp
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ n).hom) = LinearMap.id := by
  have hmap : (collarProjY (Y := Y) b).comp (Work.StemsB.collarSectionIncl (Y := Y) b hb)
      = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro y
    exact rfl
  have h : Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ n
        ≫ Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ n
      = 𝟙 (Work.Thom.Coh ℚ n Y) := by
    rw [← Work.Thom.CohMap_comp (Work.StemsB.collarSectionIncl (Y := Y) b hb)
      (collarProjY (Y := Y) b) ℚ n, hmap, Work.Thom.CohMap_id]
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp] at h2
  exact h2

/-- `▸`-transport of `0`. -/
private lemma cast_zero_apply {F : ℕ → Type*} [∀ n, Zero (F n)] {a b : ℕ} (h : a = b) :
    h ▸ (0 : F a) = (0 : F b) := by cases h; rfl

/-- `▸`-transports of `0` compose. -/
private lemma cast_cast_zero {F : ℕ → Type*} [∀ n, Zero (F n)] {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) : h₂ ▸ (h₁ ▸ (0 : F a)) = (0 : F c) := by
  rw [cast_zero_apply, cast_zero_apply]

/-- `h ▸ x = y` implies `x = h.symm ▸ y`. -/
private lemma cast_eq_of_cast_eq {F : ℕ → Type*} {a b : ℕ} (h : a = b) {x : F a} {y : F b}
    (hxy : h ▸ x = y) : x = h.symm ▸ y := by cases h; simpa using hxy

/-- `▸`-transport along a self-equality is the identity. -/
private lemma cast_self_apply {F : ℕ → Type*} {a : ℕ} (h : a = a) (x : F a) : (h ▸ x) = x := by
  rw [Subsingleton.elim h rfl]

/-- `eqToHom`-transports along a degree equality are `▸`-transports, in the
`singularCohomology` spelling. -/
private lemma eqToHom_singCoh_eq_cast {C : TopCat} {a b : ℕ} (h : a = b)
    (x : Work.Cohomology.singularCohomology ℚ a C) :
    (CategoryTheory.eqToHom (congrArg (fun t => Work.Cohomology.singularCohomology ℚ t C) h)) x
      = (h ▸ x : Work.Cohomology.singularCohomology ℚ b C) := by cases h; rfl

/-- Pullback commutes with degree transports (in the `singularCohomology` spelling). -/
private lemma CohMap_eqToHom_homology_sing {X' Y' : Type} [TopologicalSpace X']
    [TopologicalSpace Y'] (f : C(X', Y')) {i j : ℕ} (h : i = j)
    (z : Work.Cohomology.singularCohomology ℚ i (TopCat.of Y')) :
    (Work.Thom.CohMap f ℚ j).hom
        (CategoryTheory.eqToHom (congrArg (fun t =>
          Work.Cohomology.singularCohomology ℚ t (TopCat.of Y')) h) z)
      = CategoryTheory.eqToHom (congrArg (fun t =>
          Work.Cohomology.singularCohomology ℚ t (TopCat.of X')) h)
          ((Work.Thom.CohMap f ℚ i).hom z) := by
  cases h; rfl

/-- `δ (i^*z) = 0`. -/
private lemma dPair_iStar (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Work.Thom.Coh ℚ k (↥(sphLoopBig b) × Y)) :
    dPair b Y k (iStar b Y k z) = 0 := by
  have h' : ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) k).hom).comp (iStar b Y k) = 0 := by
    have h := congrArg ModuleCat.Hom.hom
      (Work.Cohomology.pair_comp_δ ℚ (CollQ b Y) (CollA b Y) k)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h
  have h2 := LinearMap.congr_fun h' z
  simpa only [dPair, LinearMap.comp_apply, LinearMap.zero_apply] using h2

/-- `i^*` is a ring map. -/
private lemma iStar_cup (b : ℕ) (Y : Type) [TopologicalSpace Y] (m m' : ℕ)
    (a : Work.Thom.Coh ℚ m (↥(sphLoopBig b) × Y))
    (a' : Work.Thom.Coh ℚ m' (↥(sphLoopBig b) × Y)) :
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) m m')
        (iStar b Y m a) (iStar b Y m' a')
      = iStar b Y (m + m')
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) m m') a a') := by
  rw [show iStar b Y m
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m).hom
      from rfl]
  rw [show iStar b Y m'
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m').hom
      from rfl]
  rw [show iStar b Y (m + m')
      = (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of ↥(CollA b Y))
          (TopCat.of (↥(sphLoopBig b) × Y))
          (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y))
          (m + m')).hom from rfl]
  exact (Work.Cohomology.cupNaturalH ℚ
    (Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y)) (CollA b Y)) m m' a a').symm

/-- **The first cross term vanishes**: `δ (i^*a ⌣ i^*a') = 0`. -/
private lemma delta_restr_cup (b : ℕ) (Y : Type) [TopologicalSpace Y] (k k' : ℕ)
    (a : Work.Thom.Coh ℚ k (↥(sphLoopBig b) × Y))
    (a' : Work.Thom.Coh ℚ k' (↥(sphLoopBig b) × Y)) :
    dPair b Y (k + k') ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) k k')
        (iStar b Y k a) (iStar b Y k' a')) = 0 := by
  rw [iStar_cup b Y k k' a a']
  exact dPair_iStar b Y (k + k') _

/-! ## Casts in the cup of two `s`-parts -/

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

/-- **The square of an `s`-part**: `(A ⌣ s) ⌣ (B ⌣ s) = 0` when `s ⌣ s = 0`. -/
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
    rw [h1, smul_zero]
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

/-- **The product of two top-degree `s`-parts vanishes.** -/
private lemma zeta_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (X X' : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y)) :
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
      (collarSPartLow b hb Y τ hτ s X) (collarSPartLow b hb Y τ hτ s X') = 0 := by
  have hk : 0 + (b - 1) = b - 1 := Nat.zero_add (b - 1)
  set A : Work.Thom.Coh ℚ 0 ↥(sphLoopCollarProd b Y) :=
    collarProjC (Y := Y) b 0 (collarSigmaLow b hb Y τ hτ X) with hA
  set A' : Work.Thom.Coh ℚ 0 ↥(sphLoopCollarProd b Y) :=
    collarProjC (Y := Y) b 0 (collarSigmaLow b hb Y τ hτ X') with hA'
  set W : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (0 + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) 0 (b - 1)) A s with hW
  set W' : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (0 + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) 0 (b - 1)) A' s with hW'
  have hu : collarSPartLow b hb Y τ hτ s X
      = (hk ▸ W : (Work.Cohomology.SSetCochainComplex ℚ
          (TopCat.toSSet.obj (CollC b Y))).homology (b - 1)) := by
    rw [collarSPartLow_apply]
    rw [← hA, ← hW]
    exact eqToHom_singCoh_eq_cast hk W
  have hv : collarSPartLow b hb Y τ hτ s X'
      = (hk ▸ W' : (Work.Cohomology.SSetCochainComplex ℚ
          (TopCat.toSSet.obj (CollC b Y))).homology (b - 1)) := by
    rw [collarSPartLow_apply]
    rw [← hA', ← hW']
    exact eqToHom_singCoh_eq_cast hk W'
  have hssq' : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y))
      (b - 1) (b - 1)) s s = 0 := hssq
  rw [hu, hv]
  rw [cupH'_cast_left hk, cupH'_cast_right hk]
  rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y))
        (0 + (b - 1)) (0 + (b - 1))) W W' = 0 from
      cupH'_sq_kill 0 0 (b - 1) A A' s hssq']
  exact cast_cast_zero
    (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology k) _ _

/-! ## The section and the base part of the splitting -/

/-- **The collar section kills the `s`-part.** -/
private lemma zeta_sgStar (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b hb)) (b - 1)).hom s = 0)
    (X : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y)) :
    sgStar b hb Y (b - 1) (collarSPartLow b hb Y τ hτ s X) = 0 := by
  rw [collarSPartLow_apply]
  rw [CohMap_eqToHom_homology_sing (f := Work.StemsB.collarSection (Y := Y) b hb)
    (h := Nat.zero_add (b - 1))]
  rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b hb))
    0 (b - 1) (collarProjC (Y := Y) b 0 (collarSigmaLow b hb Y τ hτ X)) s]
  rw [hσ, Work.Cohomology.cupH'_zero_right, map_zero]

/-- **The base part of the splitting**: if `X - π^*(ΣX) ⌣ s = i^*a` then `a = π^*(σ^*X)`. -/
private lemma split_base_low (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b hb)) (b - 1)).hom s = 0)
    (X : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (a : Work.Thom.Coh ℚ (b - 1) (↥(sphLoopBig b) × Y))
    (ha : X - collarSPartLow b hb Y τ hτ s X = collarRestr (Y := Y) b (b - 1) a) :
    a = piStar b Y (b - 1) (sgStar b hb Y (b - 1) X) := by
  have hsg : sgStar b hb Y (b - 1) (collarRestr (Y := Y) b (b - 1) a)
      = sgStar b hb Y (b - 1) X := by
    rw [← ha, map_sub, zeta_sgStar b hb Y τ hτ s hσ X, sub_zero]
  have h1 : (Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ (b - 1)).hom a
      = sgStar b hb Y (b - 1) X := by
    rw [← collarSection_collarRestr_low b hb (b - 1) a]
    exact hsg
  haveI hI : IsIso (Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ (b - 1)) :=
    Work.StemsB.isIso_collarSectionIncl (Y := Y) b hb (b - 1)
  have hinj : Function.Injective
      (Work.Thom.CohMap (Work.StemsB.collarSectionIncl (Y := Y) b hb) ℚ (b - 1)).hom := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  apply hinj
  rw [← LinearMap.comp_apply, collarSectionIncl_collarProjY_low b hb (b - 1), LinearMap.id_apply]
  exact h1

/-! ## The two cross terms -/

/-- **The cross term with the `s`-part on the right.** -/
private lemma delta_restr_zeta (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (X' : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (a : Work.Thom.Coh ℚ (b - 1) (↥(sphLoopBig b) × Y)) :
    dPair b Y ((b - 1) + (b - 1))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (iStar b Y (b - 1) a) (collarSPartLow b hb Y τ hτ s X'))
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            a (dPair b Y (b - 1) X')) := by
  have hC := Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (b - 1) (b - 1)
    a (collarSPartLow b hb Y τ hτ s X')
  rw [hC]
  rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
        (collarSPartLow b hb Y τ hτ s X')
      = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom X' from
    pairδ_collarSPartLow b hb Y τ hτ s hs X']

/-- **The cross term with the `s`-part on the left.** -/
private lemma delta_zeta_restr (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (X : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1))
    (a' : Work.Thom.Coh ℚ (b - 1) (↥(sphLoopBig b) × Y)) :
    dPair b Y ((b - 1) + (b - 1))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (collarSPartLow b hb Y τ hτ s X) (iStar b Y (b - 1) a'))
      = ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            a' (dPair b Y (b - 1) X)) := by
  have hgc := Work.Cohomology.gradedComm ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)
    (collarSPartLow b hb Y τ hτ s X) (iStar b Y (b - 1) a')
  have hgc' : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
        (collarSPartLow b hb Y τ hτ s X) (iStar b Y (b - 1) a')
      = ((-1 : ℚ) ^ ((b - 1) * (b - 1))) •
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
            (iStar b Y (b - 1) a') (collarSPartLow b hb Y τ hτ s X)) := by
    have hself := (cast_self_apply
      (F := fun k => (Work.Cohomology.SSetCochainComplex ℚ
        (TopCat.toSSet.obj (CollC b Y))).homology k) (Nat.add_comm (b - 1) (b - 1))
      ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
        (collarSPartLow b hb Y τ hτ s X) (iStar b Y (b - 1) a'))).symm
    exact hself.trans hgc
  rw [hgc', dPair_smul]
  rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) ((b - 1) + (b - 1))).hom
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (iStar b Y (b - 1) a') (collarSPartLow b hb Y τ hτ s X))
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((b - 1) + 1))
            a' ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
              (collarSPartLow b hb Y τ hτ s X))) from
    Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (b - 1) (b - 1)
      a' (collarSPartLow b hb Y τ hτ s X)]
  rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
        (collarSPartLow b hb Y τ hτ s X)
      = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom X from
    pairδ_collarSPartLow b hb Y τ hτ s hs X]
  rw [smul_smul, ← pow_add]

/-- **The `s`-`s` term vanishes.** -/
private lemma delta_zeta_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.SSetCochainComplex ℚ
      (TopCat.toSSet.obj (CollC b Y))).homology (b - 1))
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (X X' : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y)) :
    dPair b Y ((b - 1) + (b - 1))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (collarSPartLow b hb Y τ hτ s X) (collarSPartLow b hb Y τ hτ s X')) = 0 := by
  rw [zeta_cup b hb Y τ hτ s hssq X X']
  exact map_zero _

/-! ## The main theorem -/

theorem collarDPairCupLow (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y) (Work.StemsB.sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (X X' : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y)) :
    (Work.Cohomology.pairδ ℚ (Work.StemsB.Rat.CollQ b Y) (Work.StemsB.Rat.CollA b Y)
        ((b - 1) + (b - 1))).hom
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (Work.StemsB.Rat.CollC b Y))
          (b - 1) (b - 1)) X X')
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (Work.StemsB.Rat.CollQ b Y) (Work.StemsB.Rat.CollA b Y)
            (b - 1) ((b - 1) + 1))
            ((Work.Thom.CohMap (Work.StemsB.Rat.collarProjY (Y := Y) b) ℚ (b - 1)).hom
              ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (b - 1)).hom X))
            ((Work.Cohomology.pairδ ℚ (Work.StemsB.Rat.CollQ b Y)
              (Work.StemsB.Rat.CollA b Y) (b - 1)).hom X'))
        + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) •
          ((Work.Cohomology.mixedCupR ℚ (Work.StemsB.Rat.CollQ b Y) (Work.StemsB.Rat.CollA b Y)
            (b - 1) ((b - 1) + 1))
            ((Work.Thom.CohMap (Work.StemsB.Rat.collarProjY (Y := Y) b) ℚ (b - 1)).hom
              ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (b - 1)).hom X'))
            ((Work.Cohomology.pairδ ℚ (Work.StemsB.Rat.CollQ b Y)
              (Work.StemsB.Rat.CollA b Y) (b - 1)).hom X)) := by
  have hb1 : 1 ≤ b := by omega
  obtain ⟨a, ha⟩ := collarSplitLow b hb1 Y τ hτ s hs X
  obtain ⟨b0, hb0⟩ := collarSplitLow b hb1 Y τ hτ s hs X'
  set u : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) :=
    collarSPartLow b hb1 Y τ hτ s X with hu
  set v : (Work.Cohomology.singularCochainComplex ℚ
      (TopCat.of ↥(sphLoopCollarProd b Y))).homology (b - 1) :=
    collarSPartLow b hb1 Y τ hτ s X' with hv
  have hae : a = piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X) :=
    split_base_low b hb1 Y τ hτ s hσ X a (by rw [← hu]; exact ha)
  have hbe : b0 = piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X') :=
    split_base_low b hb1 Y τ hτ s hσ X' b0 (by rw [← hv]; exact hb0)
  have hX : X = iStar b Y (b - 1) a + u := by
    rw [← sub_eq_iff_eq_add]; exact ha
  have hX' : X' = iStar b Y (b - 1) b0 + v := by
    rw [← sub_eq_iff_eq_add]; exact hb0
  have hW : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) X X'
      = (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (iStar b Y (b - 1) a) (iStar b Y (b - 1) b0)
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
          (iStar b Y (b - 1) a) v
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) u
          (iStar b Y (b - 1) b0)
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) u v := by
    rw [hX, hX', Work.Cohomology.cupH'_add_left, Work.Cohomology.cupH'_add_right,
      Work.Cohomology.cupH'_add_right]
    abel
  have hD : dPair b Y ((b - 1) + (b - 1))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) X X')
      = dPair b Y ((b - 1) + (b - 1))
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
            (iStar b Y (b - 1) a) (iStar b Y (b - 1) b0))
        + dPair b Y ((b - 1) + (b - 1))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1))
              (iStar b Y (b - 1) a) v)
        + dPair b Y ((b - 1) + (b - 1))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) u
              (iStar b Y (b - 1) b0))
        + dPair b Y ((b - 1) + (b - 1))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (b - 1)) u v) := by
    rw [hW, dPair_add, dPair_add, dPair_add]
  rw [hD, hu, hv]
  rw [delta_restr_cup b Y (b - 1) (b - 1) a b0,
    delta_restr_zeta b hb1 Y τ hτ s hs X' a,
    delta_zeta_restr b hb1 Y τ hτ s hs X b0,
    delta_zeta_cup b hb1 Y τ hτ s hssq X X']
  rw [hae, hbe]
  simp only [zero_add, add_zero]

end

end Work.StemsB.Rat
