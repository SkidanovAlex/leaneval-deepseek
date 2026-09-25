import Mathlib
import Submission.NK.CFTLib.normQuotientSetup
import Submission.NK.CFTLib.exists_normQuotientClPart_surjection
import Submission.NK.CFTLib.pRank_normQuotientUnitImage_le

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory TensorProduct

noncomputable section

namespace NK.CFTLib

/-! ## An exact-sequence inequality for `Module.finrank`

Mathlib's `LinearMap.finrank_range_add_finrank_ker` needs `FiniteDimensional` of the source.  For
the application below the source may well be infinite dimensional, but there `Module.finrank`
vanishes, so the inequality still holds.  This is the "one-sided" version, valid with no finiteness
hypothesis at all. -/

theorem finrank_le_finrank_ker_add_finrank_range {K : Type*} [DivisionRing K]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) :
    Module.finrank K V ≤ Module.finrank K ↥(f.ker) + Module.finrank K ↥(f.range) := by
  by_cases hV : Module.Finite K V
  · haveI := hV
    have h := LinearMap.finrank_range_add_finrank_ker f
    omega
  · have hrank : Cardinal.aleph0 ≤ Module.rank K V := by
      rw [← not_lt]
      intro hlt
      exact hV (Module.rank_lt_aleph0_iff.mp hlt)
    have h0 : Module.finrank K V = 0 := by
      show (Module.rank K V).toNat = 0
      rw [Cardinal.toNat_eq_zero]
      exact Or.inr hrank
    rw [h0]
    exact Nat.zero_le _

/-! ## The exact-sequence inequality for `pRank` with a finitely generated kernel -/

/-- **The exact-sequence inequality for `pRank`** for a surjective additive homomorphism whose
kernel is finitely generated as a `ℤ`-module: `pRank` of the source is at most `pRank` of the kernel
plus `pRank` of the target.  The source itself is not required to be finitely generated. -/
theorem pRank_le_add_ker_hom_of_finite_ker {p : ℕ} [Fact p.Prime] {G Q : Type*}
    [AddCommGroup G] [AddCommGroup Q] (f : G →+ Q) (hf : Function.Surjective f)
    (hfin : Module.Finite ℤ ↥(f.ker)) :
    pRank p G ≤ pRank p ↥(f.ker) + pRank p Q := by
  haveI := hfin
  have hbaseK : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) :=
    Module.Finite.base_change ℤ (ZMod p) ↥(f.ker)
  let g : G →ₗ[ℤ] Q := f.toIntLinearMap
  have hg : Function.Surjective g := hf
  let k : ↥(f.ker) →ₗ[ℤ] G := (AddSubgroup.subtype f.ker).toIntLinearMap
  have hkg : Function.Exact ⇑k ⇑g := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  let F : TensorProduct ℤ (ZMod p) G →ₗ[ZMod p] TensorProduct ℤ (ZMod p) Q :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) g
  let K : TensorProduct ℤ (ZMod p) ↥(f.ker) →ₗ[ZMod p] TensorProduct ℤ (ZMod p) G :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) k
  have hfunF : ⇑F = ⇑(LinearMap.lTensor (ZMod p) g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hfunK : ⇑K = ⇑(LinearMap.lTensor (ZMod p) k) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hexact := lTensor_exact (R := ℤ) (Q := ZMod p) hkg hg
  have hker : F.ker = K.range := by
    ext x
    constructor
    · intro hx
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := by
        rw [← congr_fun hfunF x]; exact hx
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := by
        rw [← Function.Exact.linearMap_ker_eq hexact]
        exact (LinearMap.mem_ker).mpr hx2
      obtain ⟨y, hy⟩ := hx4
      exact ⟨y, by rw [congr_fun hfunK y]; exact hy⟩
    · rintro ⟨y, hy⟩
      have hy1 : (LinearMap.lTensor (ZMod p) k) y = x := by
        rw [← congr_fun hfunK y]; exact hy
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := ⟨y, hy1⟩
      have hx3 : x ∈ (LinearMap.lTensor (ZMod p) g).ker := by
        rw [Function.Exact.linearMap_ker_eq hexact]; exact hx4
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := hx3
      rw [← congr_fun hfunF x] at hx2
      exact hx2
  have hFsurj : Function.Surjective F := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero F⟩
    | add x y hx hy =>
        obtain ⟨u, hu⟩ := hx
        obtain ⟨v, hv⟩ := hy
        exact ⟨u + v, by rw [map_add, hu, hv]⟩
    | tmul a n =>
        obtain ⟨m, rfl⟩ := hg n
        exact ⟨a ⊗ₜ[ℤ] m, by
          show (TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) g)
            (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] g m
          rw [TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩
  have h1 : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) G) ≤
      Module.finrank (ZMod p) ↥F.ker + Module.finrank (ZMod p) ↥F.range :=
    finrank_le_finrank_ker_add_finrank_range F
  have h2 : Module.finrank (ZMod p) ↥F.ker ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) := by
    rw [hker]
    exact LinearMap.finrank_range_le K
  have h3 : Module.finrank (ZMod p) ↥F.range ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) Q) := by
    rw [LinearMap.range_eq_top.mpr hFsurj]
    exact le_of_eq (LinearEquiv.finrank_eq
      (Submodule.topEquiv (R := ZMod p) (M := TensorProduct ℤ (ZMod p) Q)))
  change Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) G) ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) +
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) Q)
  linarith

/-! ## The unit part of the norm quotient is finitely generated

`normQuotientUnitImage F K` is the image, in `normQuotient F K`, of the subgroup
`unitsInF F ⊓ normPrincipalPreimage F K` — a subgroup of the finitely generated group
`(𝓞 F)ˣ` (Dirichlet).  Hence it is finitely generated as a `ℤ`-module. -/

/-- Lean v4.34: instance search no longer finds `AddCommGroup.toIntModule` for this subtype on its
own (the `AddSubgroup` lives over `QuotientAddGroup.Quotient.addGroup`, not `AddCommGroup.toAddGroup`); provide it. -/
noncomputable local instance moduleInt_addSubgroup_normQuotient (F K : Type) [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
    (S : AddSubgroup (normQuotient F K)) : Module ℤ ↥S :=
  AddCommGroup.toIntModule ↥S

theorem moduleFinite_normQuotientUnitImage (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] :
    Module.Finite ℤ ↥(normQuotientUnitImage F K) := by
  classical
  set P : Subgroup Fˣ := normPrincipalPreimage F K with hP
  set U : Subgroup Fˣ := unitsNormSubgroup F K with hU
  set B : Subgroup Fˣ := unitsInF F ⊓ P with hB
  have hBP : B ≤ P := inf_le_right
  have hUP : U ≤ P := unitsNormSubgroup_le_normPrincipalPreimage F K
  set N : AddSubgroup (Additive ↥P) := (U.subgroupOf P).toAddSubgroup with hN
  have hbot : (U.subgroupOf P).toAddSubgroup.map (QuotientAddGroup.mk' N) = ⊥ :=
    (AddSubgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientAddGroup.ker_mk' N).symm)
  have hsup : ((U ⊔ B).subgroupOf P).toAddSubgroup
      = (U.subgroupOf P).toAddSubgroup ⊔ (B.subgroupOf P).toAddSubgroup := by
    rw [Subgroup.subgroupOf_sup hUP hBP]
    exact OrderIso.map_sup Subgroup.toAddSubgroup _ _
  have hstar : normQuotientUnitImage F K
      = (B.subgroupOf P).toAddSubgroup.map (QuotientAddGroup.mk' N) := by
    rw [show normQuotientUnitImage F K
        = ((U ⊔ B).subgroupOf P).toAddSubgroup.map (QuotientAddGroup.mk' N) from rfl,
      hsup, AddSubgroup.map_sup, hbot]
    simp
  rw [hstar]
  haveI hfinB : Module.Finite ℤ (Additive ↥B) := finite_subgroup_unitsInF F B inf_le_left
  set f : Additive ↥B →ₗ[ℤ] normQuotient F K :=
    (AddMonoidHom.toIntLinearMap (QuotientAddGroup.mk' N)).comp
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Subgroup.inclusion hBP))) with hf
  have hrange : f.range.toAddSubgroup
      = (B.subgroupOf P).toAddSubgroup.map (QuotientAddGroup.mk' N) := by
    ext y
    rw [Submodule.mem_toAddSubgroup]
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
      refine AddSubgroup.mem_map.mpr ⟨Additive.ofMul (Subgroup.inclusion hBP x.toMul), ?_, ?_⟩
      · rw [Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf]
        exact x.toMul.2
      · rw [← hx]
        rfl
    · intro hy
      obtain ⟨z, hz, hzy⟩ := AddSubgroup.mem_map.mp hy
      refine LinearMap.mem_range.mpr ⟨Additive.ofMul ⟨(z.toMul : Fˣ), hz⟩, ?_⟩
      rw [← hzy]
      rfl
  rw [← hrange]
  haveI hfin_range : Module.Finite ℤ ↥f.range := by
    refine Module.Finite.of_surjective
      (f.codRestrict f.range fun x => LinearMap.mem_range_self f x) ?_
    intro y
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  exact hfin_range

theorem pRank_normQuotient_le_units_add_card (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (K ≃ₐ[F] K))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hunr : _root_.CFTLib.IsUnramified F K) (hT : _root_.CFTLib.SplitsAt F K T)
    (hclass : _root_.CFTLib.ClassCond F K p T) :
    NK.CFTLib.pRank p (NK.CFTLib.normQuotient F K) ≤
      NK.CFTLib.pRank p ↥(NK.CFTLib.normQuotientUnitImage F K) + T.card := by
  obtain ⟨Q, hQ, f, hf, hker, hrank⟩ :=
    exists_normQuotientClPart_surjection F K p hG T hunr hT hclass
  letI := hQ
  have hfin : Module.Finite ℤ ↥(f.ker) := by
    rw [hker]
    exact moduleFinite_normQuotientUnitImage F K
  have hmain := pRank_le_add_ker_hom_of_finite_ker (p := p)
    (G := NK.CFTLib.normQuotient F K) (Q := Q) f hf hfin
  rw [hker] at hmain
  linarith

end NK.CFTLib
