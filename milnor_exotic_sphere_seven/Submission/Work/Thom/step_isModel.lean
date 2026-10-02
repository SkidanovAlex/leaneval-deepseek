import Mathlib
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.suspensionStep_bijective_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 8000000

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- **The inductive step preserves the defining property of a model class.**  If `τ` is a model
Thom class of the trivial bundle of rank `n` over `B` (i.e. the cup map `x ↦ π^*(x) ⌣ τ` is
bijective in every degree), then so is `Work.Thom.step B n τ` for rank `n+1`.  This is the content
of `Work.Thom.CleanA.modelThom_step`, with the class pinned down as the explicit `step`. -/
theorem step_isModel (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : Work.Thom.RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Work.Thom.Sph B n))
    (hτ : ∀ k, Function.Bijective (fun x : Work.Thom.Coh ℤ k B =>
      (Work.Thom.mixedCupC ℤ (Work.Thom.Sph B n) k n)
        ((Work.Thom.CohMap (Work.Thom.projFstA B n) ℤ k).hom x) τ)) :
    ∀ k, Function.Bijective (fun x : Work.Thom.Coh ℤ k B =>
      (Work.Thom.mixedCupC ℤ (Work.Thom.Sph B (n+1)) k (n+1))
        ((Work.Thom.CohMap (Work.Thom.projFstA B (n+1)) ℤ k).hom x) (Work.Thom.step B n τ)) := by
  intro k
  classical
  set Aset : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} with hAset
  set A₁set : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} with hA₁set
  let homeo : B × MSph (n + 1) ≃ₜ Aset :=
    prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))
  let fwd : C(B × MSph (n + 1), Aset) := homeo
  let bwd : C(Aset, B × MSph (n + 1)) := homeo.symm
  obtain ⟨hρ, hres⟩ := modelSphereBundleStep B n
  -- Step A: transfer the model class from the pair `(B × ℝⁿ, B × Sⁿ⁻¹)` to the disc pair
  have hτdisc : ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ (DiscB B n) k n)
        ((CohMap ⟨Prod.fst, continuous_fst⟩ ℤ k).hom x) (stepDisc B n τ)) :=
    cupMap_transfer_fwdA (CleanA.discFullMap B n) (Sph B n) (DiscB B n)
      (CleanA.discFullMap_mem B n) (bijective_relCohMap_discFull B n)
      (projFstA B n) ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl) n τ hτ
  -- Step B: the cap map identifies the disc pair of rank `n` with `(B × Sⁿ, B × lower)`
  obtain ⟨τsph', hτsph'_spec, hτsph'⟩ :=
    cupMap_transfer_bwdA (capMapPairSph B n) (SphB B n) (DiscB B n)
      (CleanA.capMapPairSph_mem_mLower n) (CleanA.capRelCohIso B n)
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n (stepDisc B n τ) hτdisc
  have hτsph_eq : τsph' = stepSph B n τ := by
    apply (CleanA.capRelCohIso B n n).1
    rw [hτsph'_spec, stepSph_spec]
  have hτsph : ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ (SphB B n) k n)
        ((CohMap ⟨Prod.fst, continuous_fst⟩ ℤ k).hom x) (stepSph B n τ)) := by
    intro k
    rw [← hτsph_eq]
    exact hτsph' k
  -- Step C: the product of subtypes is the subtype of the product
  obtain ⟨τA, hτA_spec, hτA⟩ :=
    cupMap_transfer_bwdA fwd (subSubset A₁set Aset) (SphB B n)
      (CleanA.prodSubsetHomeoA_mem n)
      (fun m => bijective_relCohMap_of_homeomorphA
        (SphB B n) (subSubset A₁set Aset) homeo (fun q => Iff.rfl) ℤ m)
      ((projFstA B (n + 1)).comp (subtypeMap Aset))
      ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n (stepSph B n τ) hτsph
  -- Step D: apply the suspension isomorphism
  have hnat : (relToAbs ℤ (SphB B n) n).hom
      ((relCohMap fwd (SphB B n) (subSubset A₁set Aset) (CleanA.prodSubsetHomeoA_mem n) ℤ n).hom
        τA)
      = (CohMap fwd ℤ n).hom ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA) := by
    have h2 := congrArg ModuleCat.Hom.hom
      (relCohMap_relToAbs (f := fwd) (SphB B n) (subSubset A₁set Aset)
        (CleanA.prodSubsetHomeoA_mem n) ℤ n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
    exact LinearMap.congr_fun h2 τA
  have hcomp : (CohMap bwd ℤ n).hom.comp (CohMap fwd ℤ n).hom = LinearMap.id := by
    rw [CohMap_linear_comp]
    have hid : fwd.comp bwd = ContinuousMap.id Aset :=
      ContinuousMap.ext (fun y => homeo.apply_symm_apply y)
    rw [hid, CohMap_id]
    rfl
  have hrel : (CohMap bwd ℤ n).hom ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))
      = (relToAbs ℤ (subSubset A₁set Aset) n).hom τA := by
    rw [← hτA_spec, hnat]
    have h := LinearMap.congr_fun hcomp ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have hstep : step B n τ
      = (pairδC Aset n).hom ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA) := by
    show (pairδC Aset n).hom ((CohMap bwd ℤ n).hom ((relToAbs ℤ (SphB B n) n).hom
      (stepSph B n τ))) = (pairδC Aset n).hom ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA)
    rw [hrel]
  rw [hstep]
  have hCohπ : ∀ (k : ℕ) (b : Coh ℤ k B),
      (CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b)
        = (CohMap ((projFstA B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b := fun k b =>
    LinearMap.congr_fun (CohMap_linear_comp (subtypeMap Aset) (projFstA B (n + 1)) ℤ k) b
  have hΘ : ∀ j, Function.Bijective
      ((pairδC Aset j).hom.comp (relToAbs ℤ (subSubset A₁set Aset) j).hom) := by
    intro j
    rcases j with _ | m
    · exact suspensionStep_bijective_zero A₁set Aset hρ hres
    · exact suspensionStep_bijective A₁set Aset m hρ hres
  have key : ∀ b : Coh ℤ k B,
      (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b))
          τA)))
        = ((-1 : ℤ) ^ k) •
            ((mixedCupC ℤ Aset k (n + 1)) ((CohMap (projFstA B (n + 1)) ℤ k).hom b)
              (((pairδC Aset n).hom) ((relToAbs ℤ (subSubset A₁set Aset) n).hom τA))) := by
    intro b
    have h0 := CleanA.suspensionStep_cup' A₁set Aset k n
      ((CohMap (projFstA B (n + 1)) ℤ k).hom b) τA
    simpa using h0
  have hcupA : Function.Bijective (fun b : Coh ℤ k B =>
      (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b))
        τA) := by
    have h := hτA k
    rwa [show (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap ((projFstA B (n + 1)).comp (subtypeMap Aset)) ℤ k).hom b) τA)
        = (fun b : Coh ℤ k B => (mixedCupC ℤ (subSubset A₁set Aset) k n)
        ((CohMap (subtypeMap Aset) ℤ k).hom ((CohMap (projFstA B (n + 1)) ℤ k).hom b))
        τA)
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
          ((CohMap (subtypeMap Aset) ℤ k).hom
            ((CohMap (projFstA B (n + 1)) ℤ k).hom a)) τA)))
        = (((pairδC Aset (k + n)).hom) ((relToAbs ℤ (subSubset A₁set Aset) (k + n)).hom
        ((mixedCupC ℤ (subSubset A₁set Aset) k n)
          ((CohMap (subtypeMap Aset) ℤ k).hom
            ((CohMap (projFstA B (n + 1)) ℤ k).hom b)) τA))) := by
      rw [key a, key b]
      exact congrArg (fun z => ((-1 : ℤ) ^ k) • z) hab
    exact hcupA.1 ((hΘ (k + n)).1 h')
  · obtain ⟨u, hu⟩ := (hΘ (k + n)).2 (((-1 : ℤ) ^ k) • b)
    obtain ⟨c, hc⟩ := hcupA.2 u
    dsimp only at hc
    refine ⟨c, hsmul_inj ?_⟩
    simp only []
    rw [← key c, hc]
    simpa only [LinearMap.comp_apply] using hu

end

end Work.Thom
