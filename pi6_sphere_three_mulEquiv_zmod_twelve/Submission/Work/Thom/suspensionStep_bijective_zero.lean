import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Pair
import Submission.Work.Thom.SuspensionStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- `relToAbs` is injective in degree zero.  This is special to degree zero: in degree `0` the
homology is a kernel, and the degree-zero component of `relIncl` is the inclusion of the kernel
submodule `relKern R X A 0`, hence injective. -/
theorem relToAbs_zero_injective (R : Type) [CommRing R] {B : Type} [TopologicalSpace B]
    (A : Set B) : Function.Injective (relToAbs R A 0).hom := by
  haveI hm : Mono (((Work.Cohomology.relIncl R (TopCat.of B) A).f 0)) := by
    rw [Work.Cohomology.relIncl_f]
    exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hj : ∀ i : ℕ, ¬ (ComplexShape.up ℕ).Rel i 0 := by
    intro i h
    exact Nat.succ_ne_zero i h
  have hmono := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (Work.Cohomology.relIncl R (TopCat.of B) A) 0 (C := ModuleCat R) (c := ComplexShape.up ℕ) hj
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- **The degree-zero suspension isomorphism.**  Under the same hypotheses as
`Work.Thom.suspensionStep_bijective` (the restriction `H^*(X) → H^*(A)` is injective and the
composite `H^*(X) → H^*(A) → H^*(A₁)` is bijective), the degree-zero version of the suspension map
`δ ∘ relToAbs : H^0(A,A₁) → H^1(X,A)` is bijective.  This is the case missing from
`suspensionStep_bijective`, which starts in degree one. -/
theorem suspensionStep_bijective_zero {X : Type} [TopologicalSpace X] (A₁ A : Set X)
    (hρ : ∀ m, Function.Injective (Work.Thom.CohMap (Work.Thom.subtypeMap A) ℤ m).hom)
    (hres : ∀ m, Function.Bijective
      (((Work.Thom.CohMap (Work.Thom.subtypeMap (Work.Thom.subSubset A₁ A)) ℤ m).hom).comp
        ((Work.Thom.CohMap (Work.Thom.subtypeMap A) ℤ m).hom))) :
    Function.Bijective
      (((Work.Thom.pairδC A 0).hom).comp ((Work.Thom.relToAbs ℤ (Work.Thom.subSubset A₁ A) 0).hom)) := by
  classical
  set ρ : ∀ m, Coh ℤ m X ⟶ Coh ℤ m A := fun m => CohMap (subtypeMap A) ℤ m with hρdef
  set res : ∀ m, Coh ℤ m A ⟶ Coh ℤ m (subSubset A₁ A) :=
    fun m => CohMap (subtypeMap (subSubset A₁ A)) ℤ m with hresdef
  have hres_surj : ∀ m, Function.Surjective (res m).hom := by
    intro m y
    obtain ⟨x, hx⟩ := (hres m).2 y
    exact ⟨(ρ m).hom x, hx⟩
  -- `im ρ` meets `ker res` trivially
  have hdisj : ∀ m, ∀ y, y ∈ (ρ m).hom.range → y ∈ (res m).hom.ker → y = 0 := by
    intro m y hy hyk
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    have h0 : (res m).hom ((ρ m).hom x) = 0 := hyk
    have hinj : Function.Injective (((res m).hom).comp ((ρ m).hom)) := (hres m).1
    have hx0 : x = 0 := hinj (by simp only [LinearMap.comp_apply, h0, map_zero])
    rw [hx0, map_zero]
  -- `H^m(A) = im ρ + ker res` in every degree
  have hsum : ∀ m, (ρ m).hom.range ⊔ (res m).hom.ker = ⊤ := by
    intro m
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨x, hx⟩ : ∃ x, (res m).hom ((ρ m).hom x) = (res m).hom y :=
      (hres m).2 ((res m).hom y)
    rw [Submodule.mem_sup]
    refine ⟨(ρ m).hom x, LinearMap.mem_range.mpr ⟨x, rfl⟩, y - (ρ m).hom x, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  -- the connecting homomorphism of `(X,A)` in degree zero is surjective with kernel `im ρ`
  have hδ_ker : (pairδC A 0).hom.ker = (ρ 0).hom.range := by
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₃ A 0)
    rw [← h]
  have hδ_surj : Function.Surjective (pairδC A 0).hom := by
    have hrel0 : (relToAbs ℤ A 1).hom = 0 := by
      refine LinearMap.range_eq_bot.mp ?_
      have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₂ A 1)
      rw [h]
      exact LinearMap.ker_eq_bot.mpr (hρ 1)
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₁ A 0)
    rw [hrel0, LinearMap.ker_zero, LinearMap.range_eq_top] at h
    exact h
  -- `relToAbs` for the pair `(A,A₁)` in degree zero has image `ker res`
  have hrel_range : (relToAbs ℤ (subSubset A₁ A) 0).hom.range = (res 0).hom.ker := by
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₂ (subSubset A₁ A) 0)
    rw [h]
  -- `relToAbs` for the pair `(A,A₁)` in degree zero is injective
  have hrel_inj : Function.Injective (relToAbs ℤ (subSubset A₁ A) 0).hom :=
    relToAbs_zero_injective ℤ (subSubset A₁ A)
  constructor
  · rintro z z' hzz'
    have hzz'' : (pairδC A 0).hom ((relToAbs ℤ (subSubset A₁ A) 0).hom z)
        = (pairδC A 0).hom ((relToAbs ℤ (subSubset A₁ A) 0).hom z') := hzz'
    have hk : (relToAbs ℤ (subSubset A₁ A) 0).hom z
        - (relToAbs ℤ (subSubset A₁ A) 0).hom z' ∈ (pairδC A 0).hom.ker := by
      rw [LinearMap.mem_ker, map_sub, hzz'', sub_self]
    rw [hδ_ker] at hk
    have hk2 : (relToAbs ℤ (subSubset A₁ A) 0).hom z
        - (relToAbs ℤ (subSubset A₁ A) 0).hom z' ∈ (res 0).hom.ker := by
      rw [← hrel_range]
      exact Submodule.sub_mem _ (LinearMap.mem_range.mpr ⟨z, rfl⟩)
        (LinearMap.mem_range.mpr ⟨z', rfl⟩)
    exact hrel_inj (sub_eq_zero.mp (hdisj 0 _ hk hk2))
  · intro w
    have hw : w ∈ (pairδC A 0).hom.range := LinearMap.mem_range.mpr (hδ_surj w)
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
    have hu' : u ∈ (ρ 0).hom.range ⊔ (res 0).hom.ker := by
      rw [hsum]; exact Submodule.mem_top
    obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.mp hu'
    have hδp : (pairδC A 0).hom p = 0 := by
      have : p ∈ (pairδC A 0).hom.ker := by rw [hδ_ker]; exact hp
      exact this
    have hv' : v ∈ (relToAbs ℤ (subSubset A₁ A) 0).hom.range := by
      rw [hrel_range]; exact hv
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hv'
    refine ⟨z, ?_⟩
    have hv_eq : v = u - p := by rw [← hpv]; abel
    rw [LinearMap.comp_apply, hz, hv_eq, map_sub, hδp, sub_zero, hu]

end

end Work.Thom
