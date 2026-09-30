import Mathlib
import Submission.Work.Thom.ModelThomDefs
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.modelSphereBundleStep
import Submission.Work.Thom.capRelCohIso
import Submission.Work.Thom.bijective_relCohMap_discFull
import Submission.Work.Thom.LineThomClass

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

/-!
# The suspension step of the model induction

This module proves the inductive step of `Work.Thom.ModelThom`: from a Thom class of the rank-`n`
model pair `(B × ℝⁿ, B × S^{n-1})` we build one of the rank-`(n+1)` model pair
`(B × ℝ^{n+1}, B × Sⁿ)`, controlling the *specific* cup map `x ↦ π^*(x) ⌣ τ` throughout.

The chain of identifications is

`(B × ℝⁿ, B × S^{n-1})` --inclusion--> `(B × Dⁿ, B × S^{n-1})` --cap map--> `(B × Sⁿ, B × lower)`,

and then the suspension isomorphism `δ ∘ relToAbs` of `Work.Thom.suspensionStep_bijective`, whose
compatibility with the cup product is `Work.Thom.suspensionStep_cup'` below.
`Work.Thom.cupMap_transfer_fwd` / `cupMap_transfer_bwd` transport the bijectivity of the cup map
through each of the first two maps, and the Leibniz rule of the connecting homomorphism handles the
last one.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The Leibniz rule of the suspension isomorphism**, in the degree convention `H^n(A,A₁) →
H^{n+1}(X,A)` (the version `Work.Thom.suspensionStep_cup` is stated for the shifted degree
`n+1`). -/
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

/-- The pair condition of the homeomorphism `prodSubsetHomeo`. -/
theorem prodSubsetHomeo_mem {B : Type} [TopologicalSpace B] (n : ℕ) :
    ∀ q ∈ {p : B × MSph (n + 1) | p.2.1 ∈ mLower n},
      (prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
          C(B × MSph (n + 1), {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)})) q
        ∈ subSubset {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n}
            {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} := by
  intro q hq
  simpa [subSubset, prodSubsetHomeo_apply] using hq

/-- The homeomorphism `prodSubsetHomeo` commutes with the projections to the base. -/
theorem prodSubsetHomeo_comp_fst {B : Type} [TopologicalSpace B] (n : ℕ) :
    ((⟨fun q : {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} =>
          (q : B × EuclideanSpace ℝ (Fin (n + 1))).1,
        continuous_fst.comp continuous_subtype_val⟩ :
        C({p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}, B)).comp
      (prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
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
    cupMap_transfer_fwd (discFullMap B n)
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
      {q : B × MBall n | q.2.1 ∈ mSph n}
      (discFullMap_mem B n) (bijective_relCohMap_discFull B n)
      (projFst B n) ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl) n τn hτn
  -- Step B: the cap map identifies the disc pair of rank `n` with `(B × Sⁿ, B × lower)`
  obtain ⟨τsph, _, hτsph⟩ :=
    cupMap_transfer_bwd (capMapPairSph B n)
      {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
      {q : B × MBall n | q.2.1 ∈ mSph n}
      (capMapPairSph_mem_mLower n) (capRelCohIso B n)
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τdisc hτdisc
  -- Step C: the product of subtypes is the subtype of the product
  obtain ⟨τA, _, hτA⟩ :=
    cupMap_transfer_bwd
      (prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)) :
        C(B × MSph (n + 1), {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)}))
      (subSubset A₁set Aset)
      {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
      (prodSubsetHomeo_mem n)
      (fun m => bijective_relCohMap_of_homeomorph
        {p : B × MSph (n + 1) | p.2.1 ∈ mLower n}
        (subSubset A₁set Aset)
        (prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1)))
        (fun q => Iff.rfl) ℤ m)
      ((projFst B (n + 1)).comp (subtypeMap Aset))
      ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τsph hτsph
  -- Step D: apply the suspension isomorphism
  have hCohπ : ∀ (k : ℕ) (b : Coh ℤ k B),
      (CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom b)
        = (CohMap ((projFst B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b := fun k b =>
    LinearMap.congr_fun (CohMap_linear_comp (subtypeMap Aset) (projFst B (n + 1)) ℤ k) b
  refine ⟨((pairδC Aset n).hom) ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA), fun k => ?_⟩
  have hΘk : Function.Bijective
      (((pairδC Aset (k + n)).hom).comp ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom)) := by
    have h0 := suspensionStep_bijective A₁set Aset (k + n - 1) hρ hres
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k + n)] at h0
    exact h0
  have key : ∀ b : Coh ℤ k B,
      (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom b)) τA)))
        = ((-1 : ℤ) ^ k) •
            ((mixedCupC ℤ Aset k (n + 1)) ((CohMap (projFst B (n + 1)) ℤ k).hom b)
              (((pairδC Aset n).hom) ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA))) := by
    intro b
    have h0 := suspensionStep_cup' A₁set Aset k n
      ((CohMap (projFst B (n + 1)) ℤ k).hom b) τA
    simpa using h0
  have hcupA : Function.Bijective (fun b : Coh ℤ k B =>
      (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom b)) τA) := by
    have h := hτA k
    rwa [show (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap ((projFst B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b) τA)
        = (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom b)) τA)
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
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom a)) τA)))
        = (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFst B (n + 1)) ℤ k).hom b)) τA))) := by
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

end

end Work.Thom
