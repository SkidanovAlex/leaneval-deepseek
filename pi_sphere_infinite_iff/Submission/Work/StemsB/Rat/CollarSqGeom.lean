import Mathlib
import Submission.Work.StemsB.CollarRat
import Submission.Work.StemsB.serreSphere_collar_les_degenerates
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSuspClass
import Submission.Work.Thom.pairDeltaNatural
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Cohomology.punit
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.PairSequence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.StemsB.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## Cast lemmas -/

/-- **A degree transport of the second variable of the mixed cup product.** -/
theorem mixedCupC_cast_right {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ) {k k' : ℕ}
    (h : k' = k) (a : Work.Thom.Coh ℚ m X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m k' a (h ▸ z))
      = (congrArg (fun t => m + t) h) ▸ ((Work.Thom.mixedCupC ℚ A m k) a z) := by
  cases h
  rfl

/-- **Cancelling a degree transport with its inverse** (for the homology of a cochain complex). -/
theorem eqToHom_symm_hom {K : CochainComplex (ModuleCat ℚ) ℕ} {a b : ℕ} (h : a = b)
    (x : K.homology a) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h.symm))
      ((CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h)) x) = x := by
  have h' : CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h.symm)
      = (CategoryTheory.eqToIso (congrArg (fun t => K.homology t) h)).inv := rfl
  rw [h']
  exact CategoryTheory.Iso.hom_inv_id_apply _ x

/-- **The pullback of relative cohomology commutes with degree transports.** -/
theorem relCohMap_relEq {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : Set X) (A' : Set X') (f : C(X, X')) (hf : ∀ x ∈ A, f x ∈ A') {i j : ℕ} (h : i = j)
    (x : Work.Thom.RelCoh ℚ i X' A') :
    (Work.Thom.relCohMap f A A' hf ℚ j).hom
        (h ▸ x : Work.Thom.RelCoh ℚ j X' A')
      = (h ▸ ((Work.Thom.relCohMap f A A' hf ℚ i).hom x) :
          Work.Thom.RelCoh ℚ j X A) := by
  cases h
  rfl

/-- **The degree transport of relative cohomology, as a linear equivalence.** -/
def relDegEquiv {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b) :
    Work.Thom.RelCoh ℚ a X A ≃ₗ[ℚ] Work.Thom.RelCoh ℚ b X A where
  toFun x := h ▸ x
  invFun x := h.symm ▸ x
  left_inv x := by cases h; rfl
  right_inv x := by cases h; rfl
  map_add' x y := by cases h; rfl
  map_smul' c x := by cases h; rfl

/-- A degree transport of relative cohomology preserves triviality of the group. -/
theorem subsingleton_relDegEquiv {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ}
    (h : a = b) (hsub : Subsingleton (Work.Thom.RelCoh ℚ a X A)) :
    Subsingleton (Work.Thom.RelCoh ℚ b X A) :=
  ⟨fun x y => by
    have h1 : (relDegEquiv A h).symm x = (relDegEquiv A h).symm y := Subsingleton.elim _ _
    have h2 : (relDegEquiv A h) ((relDegEquiv A h).symm x)
        = (relDegEquiv A h) ((relDegEquiv A h).symm y) := congrArg _ h1
    rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2⟩

/-! ## The comparison maps between the collar pair over `Y` and the collar pair over `PUnit` -/

/-- The projection `↥(sphLoopBig b) × Y → ↥(sphLoopBig b) × PUnit`. -/
def collarDrop (b : ℕ) : C(↥(sphLoopBig b) × Y, ↥(sphLoopBig b) × PUnit) :=
  ⟨fun z => (z.1, PUnit.unit), by fun_prop⟩

/-- The fibre inclusion `↥(sphLoopBig b) × PUnit → ↥(sphLoopBig b) × Y` over `y : Y`. -/
def collarFib (b : ℕ) (y : Y) : C(↥(sphLoopBig b) × PUnit, ↥(sphLoopBig b) × Y) :=
  ⟨fun z => (z.1, y), by fun_prop⟩

@[simp] theorem collarDrop_apply (b : ℕ) (z : ↥(sphLoopBig b) × Y) :
    collarDrop (Y := Y) b z = (z.1, PUnit.unit) := rfl

@[simp] theorem collarFib_apply (b : ℕ) (y : Y) (z : ↥(sphLoopBig b) × PUnit) :
    collarFib (Y := Y) b y z = (z.1, y) := rfl

/-- `collarDrop` carries the collar over `Y` into the collar over `PUnit`. -/
theorem collarDrop_mem (b : ℕ) :
    ∀ z ∈ sphLoopCollarProd b Y, collarDrop (Y := Y) b z ∈ sphLoopCollarProd b PUnit :=
  fun z hz => hz

/-- The fibre inclusion carries the collar over `PUnit` into the collar over `Y`. -/
theorem collarFib_mem (b : ℕ) (y : Y) :
    ∀ z ∈ sphLoopCollarProd b PUnit, collarFib (Y := Y) b y z ∈ sphLoopCollarProd b Y :=
  fun z hz => hz

/-- The fibre inclusion is a section of `collarDrop`. -/
theorem collarDrop_comp_collarFib (b : ℕ) (y : Y) :
    (collarDrop (Y := Y) b).comp (collarFib (Y := Y) b y) = ContinuousMap.id _ := by
  ext z
  rfl

/-- The restriction of `collarDrop` to the collars. -/
def collarDropSub (b : ℕ) :
    C(↥(sphLoopCollarProd b Y), ↥(sphLoopCollarProd b PUnit)) :=
  ⟨fun z => ⟨(z.1.1, PUnit.unit), z.2⟩, by fun_prop⟩

/-- The restriction of a fibre inclusion to the collars. -/
def collarFibSub (b : ℕ) (y : Y) :
    C(↥(sphLoopCollarProd b PUnit), ↥(sphLoopCollarProd b Y)) :=
  ⟨fun z => ⟨(z.1.1, y), z.2⟩, by fun_prop⟩

@[simp] theorem collarDropSub_apply (b : ℕ) (z : ↥(sphLoopCollarProd b Y)) :
    collarDropSub (Y := Y) b z = ⟨(z.1.1, PUnit.unit), z.2⟩ := rfl

@[simp] theorem collarFibSub_apply (b : ℕ) (y : Y) (z : ↥(sphLoopCollarProd b PUnit)) :
    collarFibSub (Y := Y) b y z = ⟨(z.1.1, y), z.2⟩ := rfl

/-- The restriction of a fibre inclusion is a section of the restricted projection. -/
theorem collarDropSub_comp_collarFibSub (b : ℕ) (y : Y) :
    (collarDropSub (Y := Y) b).comp (collarFibSub (Y := Y) b y) = ContinuousMap.id _ := by
  ext z
  rfl

/-- The constant map at `y : Y`, as a continuous map out of `↥(sphLoopBig b) × PUnit`. -/
def collarFibBase (b : ℕ) (y : Y) : C(↥(sphLoopBig b) × PUnit, Y) :=
  ⟨fun _ => y, continuous_const⟩

@[simp] theorem collarFibBase_apply (b : ℕ) (y : Y) (z : ↥(sphLoopBig b) × PUnit) :
    collarFibBase (Y := Y) b y z = y := rfl

/-- The pair of base maps for the fibre inclusion. -/
theorem collarProjY_comp_collarFib (b : ℕ) (y : Y) :
    (collarProjY (Y := Y) b).comp (collarFib (Y := Y) b y) = collarFibBase (Y := Y) b y := by
  ext z
  rfl

/-! ## Cohomology facts about the collar pair over `PUnit` -/

/-- The singular cohomology of `↥(sphLoopBig b) × PUnit` vanishes in positive degrees (the cube is
contractible). -/
theorem subsingleton_Coh_collarQ_pt (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    Subsingleton (Work.Thom.Coh ℚ n (↥(sphLoopBig b) × PUnit)) := by
  have hzero : IsZero (Work.Thom.Coh ℚ n PUnit) := by
    have h := Work.Cohomology.punit ℚ (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    exact h
  haveI hiso : IsIso (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of PUnit)
      (TopCat.of (↥(sphLoopBig b) × PUnit))
      (TopCat.ofHom (collarSectionIncl (Y := PUnit) b hb)) n) :=
    isIso_collarSectionIncl (Y := PUnit) b hb n
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_iso hzero
    (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of PUnit)
      (TopCat.of (↥(sphLoopBig b) × PUnit))
      (TopCat.ofHom (collarSectionIncl (Y := PUnit) b hb)) n)))

/-- The relative cohomology of the collar pair over `PUnit` vanishes in degree `j + b` for
`j ≥ 1`. -/
theorem subsingleton_RelCoh_collar_pt (b j : ℕ) (hb : 1 ≤ b) (hj : 1 ≤ j) :
    Subsingleton (Work.Thom.RelCoh ℚ (j + b) (↥(sphLoopBig b) × PUnit)
      (sphLoopCollarProd b PUnit)) := by
  obtain ⟨e⟩ := cohomology_collar_iso_rat b hb PUnit j
  have hzero : IsZero (Work.Thom.Coh ℚ j PUnit) := by
    have h := Work.Cohomology.punit ℚ (j - 1)
    rw [Nat.sub_add_cancel hj] at h
    exact h
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_iso hzero e)

/-- The relative cohomology of the collar pair over `PUnit` in degree `(b-1) + b`. -/
theorem subsingleton_RelCoh_collar_pt_b (b : ℕ) (hb : 2 ≤ b) :
    Subsingleton (Work.Thom.RelCoh ℚ ((b - 1) + b) (↥(sphLoopBig b) × PUnit)
      (sphLoopCollarProd b PUnit)) :=
  subsingleton_RelCoh_collar_pt b (b - 1) (by omega) (by omega)

/-- The relative cohomology of the collar pair over `PUnit` in degree `(b-1)+(b-1)+1`. -/
theorem subsingleton_RelCoh_collar_pt_b_succ (b : ℕ) (hb : 2 ≤ b) :
    Subsingleton (Work.Thom.RelCoh ℚ (((b - 1) + (b - 1)) + 1) (↥(sphLoopBig b) × PUnit)
      (sphLoopCollarProd b PUnit)) :=
  subsingleton_relDegEquiv (sphLoopCollarProd b PUnit)
    (by omega : (b - 1) + b = ((b - 1) + (b - 1)) + 1) (subsingleton_RelCoh_collar_pt_b b hb)

/-- **The cohomology of the collar over `PUnit` in the middle degree `(b-1)+(b-1)` vanishes.** -/
theorem subsingleton_Coh_collar_pt_middle (b : ℕ) (hb : 2 ≤ b) :
    Subsingleton (Work.Thom.Coh ℚ ((b - 1) + (b - 1)) (↥(sphLoopCollarProd b PUnit))) := by
  haveI hQ := subsingleton_Coh_collarQ_pt b ((b - 1) + (b - 1)) (by omega) (by omega)
  haveI hR := subsingleton_RelCoh_collar_pt_b_succ b hb
  have h := ShortComplex.Exact.moduleCat_range_eq_ker
    (Work.Cohomology.pair_exact₃ ℚ (TopCat.of (↥(sphLoopBig b) × PUnit))
      (sphLoopCollarProd b PUnit) ((b - 1) + (b - 1)))
  have hrestr : (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ
      (TopCat.of (↥(sphLoopBig b) × PUnit)) (sphLoopCollarProd b PUnit))
      ((b - 1) + (b - 1))).hom = 0 := by
    ext x
    have hx : x = 0 := @Subsingleton.elim _ hQ x 0
    rw [hx]
    simp
  have hker : (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × PUnit))
      (sphLoopCollarProd b PUnit) ((b - 1) + (b - 1))).hom.ker = ⊥ := by
    rw [← h]
    exact LinearMap.range_eq_bot.mpr hrestr
  exact ⟨fun x y => (LinearMap.ker_eq_bot.mp hker) (@Subsingleton.elim _ hR _ _)⟩

/-- **The top-degree relative cohomology of the collar pair over `PUnit` is `ℚ`.** -/
theorem nonempty_RelCoh_collar_pt_top (b : ℕ) (hb : 1 ≤ b) :
    Nonempty (Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit)
      ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := cohomology_collar_iso_rat b hb PUnit 0
  obtain ⟨e0⟩ := Work.Cohomology.singularCohomology_zero ℚ (TopCat.of PUnit)
  exact ⟨(((relDegEquiv (sphLoopCollarProd b PUnit) (Nat.zero_add b)).symm).trans
    ((e ≪≫ e0).toLinearEquiv)).toModuleIso⟩

end

end Work.StemsB.Rat
