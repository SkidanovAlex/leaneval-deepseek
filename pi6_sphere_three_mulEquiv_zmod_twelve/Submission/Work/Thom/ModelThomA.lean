import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.subsingleton_relComplex_euclidean_punctured
import Submission.Work.Thom.modelSphereBundleStep
import Submission.Work.Thom.Relocate.TrivProductHomeo
import Submission.Work.Thom.LineThomClass
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.CapChainA
import Submission.Work.Thom.capRelCohIsoA
import Submission.Work.Thom.spherePuncturedA
import Submission.Work.Thom.discFullA

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

/-!
# The model Thom class of the trivial bundle, in the island of `Submission/Work/TangentClasses/`

This file is the clean port of `Submission/{Work/Thom/ModelThomDefs,ModelThomBase,ModelThomStep,ModelThomTransfer}.lean`:
the model induction constructing the Thom class of the trivial bundle `B × ℝⁿ → B`, avoiding the
`Submission.Work.Cohomology.dualZ` island.  The transfer tool is `Work.Thom.cupMap_transfer_*A`
(`Submission/Work/Thom/ATools.lean`), the identification of the cap map is
`Work.Thom.CleanA.capRelCohIso` (`Submission/Work/Thom/capRelCohIsoA.lean`), and the disc/sphere
homotopy equivalences are `Work.Thom.bijective_relCohMap_{discFull,spherePunctured}`
(`Submission/Work/Thom/{discFullA,spherePuncturedA}.lean`).
-/

namespace Work.Thom
namespace CleanA

open CategoryTheory
open Work.TangentClasses

noncomputable section

def ModelThom (B : Type) [TopologicalSpace B] (n : ℕ) : Prop :=
  ∃ τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) {p | p.2 ∈ mSph n},
    ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} k n)
        ((CohMap (projFstA B n) ℤ k).hom x) τ)

variable {B : Type} [TopologicalSpace B]

theorem sph_subset_punctured (n : ℕ) :
    ∀ p ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n},
      p ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} := by
  intro p hp
  intro h0
  have hp' : ‖p.2‖ = 1 := hp
  rw [h0, norm_zero] at hp'
  exact zero_ne_one hp'

/-- **The base case of the model induction**: the rank-one model Thom class. -/
theorem modelThom_base (B : Type) [TopologicalSpace B] (ι : Type) [Inhabited ι] :
    ModelThom B 1 := by
  obtain ⟨T⟩ := nonempty_thomClass_trivial_line (B := B) (ι₀ := ι)
  -- step 1: `(E, E∖0) → (B × ℝ, B × ℝ^*)`
  have hf₁ : ∀ p ∈ (zeroComplement (RealBundle.trivial B ℝ ι)),
      (trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)) p
        ∈ {q : B × ℝ | q.2 ≠ 0} :=
    fun p hp => (trivProductHomeo_zeroComplement B ℝ ι p).mp hp
  have hfb₁ : ∀ m, Function.Bijective (relCohMap
      (trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ))
      (zeroComplement (RealBundle.trivial B ℝ ι)) {q : B × ℝ | q.2 ≠ 0} hf₁ ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA
      (zeroComplement (RealBundle.trivial B ℝ ι)) {q : B × ℝ | q.2 ≠ 0}
      (trivProductHomeo B ℝ ι) (fun p => trivProductHomeo_zeroComplement B ℝ ι p) ℤ m
  have hpi₁ : (⟨Prod.fst, continuous_fst⟩ : C(B × ℝ, B)).comp
      ((trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)))
      = bundleProj (RealBundle.trivial B ℝ ι) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg Prod.fst (trivProductHomeo_apply B ℝ ι p)
  obtain ⟨τ₁, _, hτ₁⟩ :=
    cupMap_transfer_bwdA
      ((trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)))
      {q : B × ℝ | q.2 ≠ 0}
      (zeroComplement (RealBundle.trivial B ℝ ι))
      hf₁ hfb₁
      ⟨Prod.fst, continuous_fst⟩ (bundleProj (RealBundle.trivial B ℝ ι))
      hpi₁ 1 T.τ (fun k => T.isThom k)
  -- step 2: `(B × ℝ) → (B × ℝ¹)`
  have hf₂ : ∀ q ∈ {q : B × ℝ | q.2 ≠ 0},
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1))) q
        ∈ {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} := by
    intro q hq
    simp only [Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_apply,
      Set.mem_setOf_eq]
    exact fun h => hq (eucOneHomeo_symm_eq_zero.mp h)
  have hfb₂ : ∀ m, Function.Bijective (relCohMap
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      {q : B × ℝ | q.2 ≠ 0} {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} hf₂ ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA
        {q : B × ℝ | q.2 ≠ 0} {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
        (Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm)
        (fun q => by
          simp only [Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_apply,
            Set.mem_setOf_eq]
          exact ⟨fun h h0 => h (eucOneHomeo_symm_eq_zero.mp h0),
            fun h h0 => h (eucOneHomeo_symm_eq_zero.mpr h0)⟩)
        ℤ m
  have hpi₂ : (⟨Prod.fst, continuous_fst⟩ : C(B × EuclideanSpace ℝ (Fin 1), B)).comp
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      = ⟨Prod.fst, continuous_fst⟩ := by
    apply ContinuousMap.ext
    intro q
    simp only [ContinuousMap.comp_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
      Homeomorph.refl_apply]
    rfl
  obtain ⟨τ₂, _, hτ₂⟩ :=
    cupMap_transfer_bwdA
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
      {q : B × ℝ | q.2 ≠ 0}
      hf₂ hfb₂
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ hpi₂
      1 τ₁ hτ₁
  -- step 3: `(B × ℝ¹, B × ℝ^*) → (B × ℝ¹, B × S⁰)`
  have hf₃ : ∀ q ∈ {p : B × EuclideanSpace ℝ (Fin 1) | p.2 ∈ mSph 1},
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin 1))) q
        ∈ {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} :=
    sph_subset_punctured 1
  have hτ₃ := cupMap_transfer_fwdA (ContinuousMap.id (B × EuclideanSpace ℝ (Fin 1)))
      {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
      {p : B × EuclideanSpace ℝ (Fin 1) | p.2 ∈ mSph 1}
      hf₃
      (bijective_relCohMap_spherePunctured B 1)
      (projFstA B 1) (projFstA B 1) (by ext q; rfl)
      1 τ₂ hτ₂
  exact ⟨_, hτ₃⟩

variable {X : Type} [TopologicalSpace X]

theorem suspensionStep_cup' (A₁ A : Set X) (m n : ℕ) (x : Coh ℤ m X)
    (z : RelCoh ℤ n A (subSubset A₁ A)) :
    ((pairδC A (m + n)).hom) (((relToAbs ℤ (subSubset A₁ A) (m + n)).hom)
        (((mixedCupC ℤ (subSubset A₁ A) m n) ((CohMap (subtypeMap A) ℤ m).hom x)) z))
      = ((-1 : ℤ) ^ m) •
        (((mixedCupC ℤ A m (n + 1)) x)
          (((pairδC A n).hom) (((relToAbs ℤ (subSubset A₁ A) n).hom) z))) := by
  have h1 := congrArg (fun w => ((pairδC A (m + n)).hom) w)
    (mixedCup_relToAbs (X := A) (subSubset A₁ A) m n ((CohMap (subtypeMap A) ℤ m).hom x) z)
  have h2 := Work.Sph3Disc.pairDelta_mixedCup_general (TopCat.of X) A m n x
    ((relToAbs ℤ (subSubset A₁ A) n).hom z)
  rw [h1]
  exact h2

/-- The inclusion of pairs `(B × Dⁿ, B × S^{n-1}) → (B × ℝⁿ, B × S^{n-1})`. -/
def discFullMap (B : Type) [TopologicalSpace B] (n : ℕ) :
    C(B × MBall n, B × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun q => (q.1, q.2.1),
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

@[simp] theorem discFullMap_apply (B : Type) [TopologicalSpace B] (n : ℕ) (q : B × MBall n) :
    discFullMap B n q = (q.1, q.2.1) := rfl

/-- The pair condition of `discFullMap`. -/
theorem discFullMap_mem (B : Type) [TopologicalSpace B] (n : ℕ) :
    ∀ q ∈ {q : B × MBall n | q.2.1 ∈ mSph n},
      discFullMap B n q ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} :=
  fun _ hq => hq

/-- The pair condition of the cap map `capMapPairSph`: it carries the sphere bundle of rank `n`
into the lower band `mLower n` of the sphere of rank `n+1`. -/
theorem capMapPairSph_mem_mLower {B : Type} [TopologicalSpace B] (n : ℕ) :
    ∀ q ∈ {q : B × MBall n | q.2.1 ∈ mSph n},
      capMapPairSph B n q ∈ {p : B × MSph (n + 1) | p.2.1 ∈ mLower n} := by
  intro q hq
  exact equator_subset_mLower n (capMap_mem_equator n hq)

/-- The pair condition of the homeomorphism `prodSubsetHomeoA`. -/
theorem prodSubsetHomeoA_mem {B : Type} [TopologicalSpace B] (n : ℕ) :
    ∀ q ∈ {p : B × MSph (n + 1) | p.2.1 ∈ mLower n},
      (prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
          C(B × MSph (n + 1), {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)})) q
        ∈ subSubset {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n}
            {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} := by
  intro q hq
  simpa [subSubset, prodSubsetHomeoA_apply] using hq

/-- The homeomorphism `prodSubsetHomeoA` commutes with the projections to the base. -/
theorem prodSubsetHomeoA_comp_fst {B : Type} [TopologicalSpace B] (n : ℕ) :
    ((⟨fun q : {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} =>
          (q : B × EuclideanSpace ℝ (Fin (n + 1))).1,
        continuous_fst.comp continuous_subtype_val⟩ :
        C({p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}, B)).comp
      (prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
        C(B × MSph (n + 1), {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)})))
    = ⟨Prod.fst, continuous_fst⟩ := by
  ext q
  rfl

/-- **The inductive step of the model induction.**  From a model Thom class of rank `n` (`n ≥ 1`)
we build one of rank `n+1`, with the same control over the cup map. -/
theorem modelThom_step (B : Type) [TopologicalSpace B] (n : ℕ) (hn : 1 ≤ n)
    (h : ModelThom B n) : ModelThom B (n + 1) := by
  obtain ⟨τn, hτn⟩ := h
  set Aset : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} with hAset
  set A₁set : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} with hA₁set
  obtain ⟨hρ, hres⟩ := modelSphereBundleStep B n
  -- Step A: the model class is a class of the disc pair
  let τdisc : RelCoh ℤ n (B × MBall n) {q : B × MBall n | q.2.1 ∈ mSph n} :=
    (relCohMap (discFullMap B n) {q : B × MBall n | q.2.1 ∈ mSph n}
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} (discFullMap_mem B n) ℤ n).hom τn
  have hτdisc : ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ {q : B × MBall n | q.2.1 ∈ mSph n} k n)
        ((CohMap ⟨Prod.fst, continuous_fst⟩ ℤ k).hom x) τdisc) :=
    cupMap_transfer_fwdA (discFullMap B n)
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
      {q : B × MBall n | q.2.1 ∈ mSph n}
      (discFullMap_mem B n) (bijective_relCohMap_discFull B n)
      (projFstA B n) ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl) n τn hτn
  -- Step B: the cap map identifies the disc pair of rank `n` with `(B × Sⁿ, B × lower)`
  obtain ⟨τsph, _, hτsph⟩ :=
    cupMap_transfer_bwdA (capMapPairSph B n)
      {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
      {q : B × MBall n | q.2.1 ∈ mSph n}
      (capMapPairSph_mem_mLower n) (capRelCohIso B n)
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τdisc hτdisc
  -- Step C: the product of subtypes is the subtype of the product
  obtain ⟨τA, _, hτA⟩ :=
    cupMap_transfer_bwdA
      (prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
        C(B × MSph (n + 1), {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}))
      (subSubset A₁set Aset)
      {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
      (prodSubsetHomeoA_mem n)
      (fun m => bijective_relCohMap_of_homeomorphA
        {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
        (subSubset A₁set Aset)
        (prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)))
        (fun q => Iff.rfl) ℤ m)
      ((projFstA B (n + 1)).comp (subtypeMap Aset))
      ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τsph hτsph
  -- Step D: apply the suspension isomorphism
  have hCohπ : ∀ (k : ℕ) (b : Coh ℤ k B),
      (CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)
        = (CohMap ((projFstA B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b := fun k b =>
    LinearMap.congr_fun (CohMap_linear_comp (subtypeMap Aset) (projFstA B (n + 1)) ℤ k) b
  refine ⟨((pairδC Aset n).hom) ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA), fun k => ?_⟩
  have hΘk : Function.Bijective
      (((pairδC Aset (k + n)).hom).comp ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom)) := by
    have h0 := suspensionStep_bijective A₁set Aset (k + n - 1) hρ hres
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k + n)] at h0
    exact h0
  have key : ∀ b : Coh ℤ k B,
      (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)) τA)))
        = ((-1 : ℤ) ^ k) •
            ((mixedCupC ℤ Aset k (n + 1)) ((CohMap (projFstA B (n + 1)) ℤ k).hom b)
              (((pairδC Aset n).hom) ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA))) := by
    intro b
    have h0 := suspensionStep_cup' A₁set Aset k n
      ((CohMap (projFstA B (n + 1)) ℤ k).hom b) τA
    simpa using h0
  have hcupA : Function.Bijective (fun b : Coh ℤ k B =>
      (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)) τA) := by
    have h := hτA k
    rwa [show (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap ((projFstA B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b) τA)
        = (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)) τA)
        from funext (fun b => by rw [hCohπ k b])] at h
  have hsmul_inj : Function.Injective
      (fun y : RelCoh ℤ (k + n + 1) (B × EuclideanSpace ℝ (Fin (n + 1))) Aset =>
        ((-1 : ℤ) ^ k) • y) := by
    intro a b hab
    have h2 := congrArg (fun z => ((-1 : ℤ) ^ k) • z) hab
    simp only at h2
    rw [smul_smul, smul_smul, Work.Thom.negOnePow_mul_self k] at h2
    simpa using h2
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · have h' : (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom a)) τA)))
        = (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)) τA))) := by
      rw [key a, key b]
      exact congrArg (fun z => ((-1 : ℤ) ^ k) • z) hab
    exact hcupA.1 (hΘk.1 h')
  · obtain ⟨u, hu⟩ := hΘk.2 (((-1 : ℤ) ^ k) • b)
    obtain ⟨c, hc⟩ := hcupA.2 u
    dsimp only at hc
    refine ⟨c, hsmul_inj ?_⟩
    simp only []
    rw [← key c, hc]
    simpa only [LinearMap.comp_apply] using hu

/-- **Every positive rank carries a model Thom class.** -/
theorem modelThom_all (B : Type) [TopologicalSpace B] (ι : Type) [Inhabited ι] {n : ℕ}
    (hn : 1 ≤ n) : ModelThom B n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction k with
  | zero => exact modelThom_base B ι
  | succ j ih => exact modelThom_step B (j + 1) (by omega) (ih (by omega))

variable {B : Type} [TopologicalSpace B]

theorem modelThom_to_thomClass (n : ℕ) (ι : Type) [Inhabited ι] (h : ModelThom B n) :
    Nonempty (ThomClass (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι) n) := by
  obtain ⟨τ, hτ⟩ := h
  -- Step 1: `(B × ℝⁿ, B × S^{n-1}) → (B × ℝⁿ, B × ℝⁿ∖0)`
  have hf₁ : ∀ q ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n},
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) q
        ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} :=
    sph_subset_punctured (B := B) n
  obtain ⟨τp, _, hτp⟩ :=
    cupMap_transfer_bwdA (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
      hf₁
      (bijective_relCohMap_spherePunctured B n)
      (projFstA B n) (projFstA B n) (by ext q; rfl) n τ hτ
  -- Step 2: `(B × ℝⁿ, B × ℝⁿ∖0) → (E, E∖0)`
  have hf₂ : ∀ p ∈ (zeroComplement (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι)),
      (trivProductHomeo B (EuclideanSpace ℝ (Fin n)) ι :
        C((RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι).TotalSpace,
          B × EuclideanSpace ℝ (Fin n))) p
        ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} :=
    fun p hp => (trivProductHomeo_zeroComplement B (EuclideanSpace ℝ (Fin n)) ι p).mp hp
  have hfb₂ : ∀ m, Function.Bijective (relCohMap
      (trivProductHomeo B (EuclideanSpace ℝ (Fin n)) ι :
        C((RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι).TotalSpace,
          B × EuclideanSpace ℝ (Fin n)))
      (zeroComplement (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} hf₂ ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA
      (zeroComplement (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      (trivProductHomeo B (EuclideanSpace ℝ (Fin n)) ι)
      (fun p => trivProductHomeo_zeroComplement B (EuclideanSpace ℝ (Fin n)) ι p) ℤ m
  have hpi₂ : (⟨fun q : B × EuclideanSpace ℝ (Fin n) => q.1, continuous_fst⟩ :
        C(B × EuclideanSpace ℝ (Fin n), B)).comp
      ((trivProductHomeo B (EuclideanSpace ℝ (Fin n)) ι :
        C((RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι).TotalSpace,
          B × EuclideanSpace ℝ (Fin n))))
      = bundleProj (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg Prod.fst (trivProductHomeo_apply B (EuclideanSpace ℝ (Fin n)) ι p)
  exact ⟨_,
    cupMap_transfer_fwdA
      ((trivProductHomeo B (EuclideanSpace ℝ (Fin n)) ι :
        C((RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι).TotalSpace,
          B × EuclideanSpace ℝ (Fin n))))
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0}
      (zeroComplement (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι))
      hf₂ hfb₂
      (projFstA B n) (bundleProj (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) ι))
      hpi₂ n τp hτp⟩

end

end CleanA

end Work.Thom
