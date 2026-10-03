import Mathlib
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.Flat.quasiIsoAugment

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.ORHomAlg.Tor

universe u

/-- **Shifting homology.**  If `D = K.augment f w` is the complex obtained from `K` by inserting a
new object in degree `0` (and shifting everything else up by one), then for `k ≥ 1` the homology of
`D` in degree `k + 1` agrees with the homology of `K` in degree `k`: the extra term in degree `0`
does not contribute.  Applying an additive functor `F` does not change this. -/
noncomputable def homologyAugmentIso {C : Type*} [Category* C] [Abelian C] {D : Type*}
    [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) {X : C}
    (f : K.X 0 ⟶ X) (w : K.d 1 0 ≫ f = 0) (k : ℕ) (hk : 1 ≤ k) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.augment f w)).homology (k + 1) ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology k := by
  have hk' : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
  rw [hk']
  set m : ℕ := k - 1
  let A : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.augment f w)
  let B : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  have e1 : A.homology (m + 1 + 1) ≅ (A.sc' (m + 3) (m + 2) (m + 1)).homology :=
    HomologicalComplex.homologyIsoSc' A (m + 3) (m + 2) (m + 1) (ChainComplex.prev ℕ (m + 2))
      (ChainComplex.next_nat_succ (m + 1))
  have e2 : (A.sc' (m + 3) (m + 2) (m + 1)).homology ≅ (B.sc' (m + 2) (m + 1) m).homology :=
    Iso.refl _
  have e3 : (B.sc' (m + 2) (m + 1) m).homology ≅ B.homology (m + 1) :=
    (HomologicalComplex.homologyIsoSc' B (m + 2) (m + 1) m (ChainComplex.prev ℕ (m + 1))
      (ChainComplex.next_nat_succ m)).symm
  exact e1 ≪≫ e2 ≪≫ e3

section Horseshoe

variable {R : Type u} [Ring R]

/-- The map `P.complex.X 0 → N₂` along which the projective resolution `P` of `N₁` is augmented
by `N₂`, for a map `f : N₁ → N₂`. -/
noncomputable def torAugmentationMap {N₁ : Type u} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂)
    (P : ProjectiveResolution (ModuleCat.of R N₁)) : P.complex.X 0 ⟶ ModuleCat.of R N₂ :=
  P.π.f 0 ≫ ModuleCat.ofHom f

/-- The augmentation map is a cycle. -/
theorem torAugmentationMap_comp_d {N₁ : Type u} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂)
    (P : ProjectiveResolution (ModuleCat.of R N₁)) :
    P.complex.d 1 0 ≫ torAugmentationMap f P = 0 := by
  rw [torAugmentationMap, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]

/-- **The horseshoe/augmented projective resolution.**  For a short exact sequence
`0 → N₁ →f N₂ →g N₃ → 0` with `N₂` projective, and a projective resolution `P` of `N₁`, the
complex `... → P.complex.X 1 → P.complex.X 0 → N₂ → 0` (i.e. `P.complex` augmented by `N₂`) is a
projective resolution of `N₃`. -/
noncomputable def torAugmentedResolution {N₁ : Type u} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module R N₂] {N₃ : Type u} [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) (hf : Function.Injective f)
    (h : Function.Exact f g) (hg : Function.Surjective g) [Module.Projective R N₂]
    (P : ProjectiveResolution (ModuleCat.of R N₁)) :
    ProjectiveResolution (ModuleCat.of R N₃) := by
  classical
  let Q : ChainComplex (ModuleCat.{u} R) ℕ := P.complex
  let πP : Q.X 0 ⟶ ModuleCat.of R N₁ := P.π.f 0
  let fM : ModuleCat.of R N₁ ⟶ ModuleCat.of R N₂ := ModuleCat.ofHom f
  let gM : ModuleCat.of R N₂ ⟶ ModuleCat.of R N₃ := ModuleCat.ofHom g
  have hQπ : Q.d 1 0 ≫ πP = 0 := P.complex_d_comp_π_f_zero
  have hkerfg : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.1 h
  have hfg : g.comp f = 0 := by
    apply LinearMap.ext
    intro x
    have hx : f x ∈ LinearMap.ker g := by rw [hkerfg]; exact ⟨x, rfl⟩
    simpa using hx
  have hfgM : fM ≫ gM = 0 := by
    apply ModuleCat.hom_ext
    exact hfg
  let hh : Q.X 0 ⟶ ModuleCat.of R N₂ := πP ≫ fM
  have w : Q.d 1 0 ≫ hh = 0 := by
    show Q.d 1 0 ≫ (πP ≫ fM) = 0
    rw [← Category.assoc, hQπ, zero_comp]
  let D : ChainComplex (ModuleCat.{u} R) ℕ := ChainComplex.augment Q hh w
  have hC : ∀ n : ℕ, Q.ExactAt (n + 1) := fun n => P.complex_exactAt_succ n
  have hEpi : Epi πP := by
    change Epi (P.π.f 0)
    infer_instance
  have hsurjπ : Function.Surjective (πP.hom) := by
    have h1 : Function.Surjective ⇑(ConcreteCategory.hom πP) :=
      (ModuleCat.epi_iff_surjective πP).1 hEpi
    exact h1
  have hexact_dπ : Function.Exact (Q.d 1 0).hom (πP.hom) := by
    have h1 : (ShortComplex.mk (Q.d 1 0) πP hQπ).Exact :=
      (ShortComplex.mk (Q.d 1 0) πP hQπ).exact_of_g_is_cokernel P.isColimitCokernelCofork
    have h2 : LinearMap.range (Q.d 1 0).hom = LinearMap.ker (πP.hom) :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h1
    exact LinearMap.exact_iff.2 h2.symm
  have hhg : hh ≫ gM = 0 := by
    show (πP ≫ fM) ≫ gM = 0
    rw [Category.assoc, hfgM, comp_zero]
  have hex1 : (ShortComplex.mk (Q.d 1 0) hh w).Exact := by
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2 ?_
    have h2 : LinearMap.range (Q.d 1 0).hom = LinearMap.ker (πP.hom) :=
      (LinearMap.exact_iff.1 hexact_dπ).symm
    show LinearMap.range (Q.d 1 0).hom = LinearMap.ker (fM.hom.comp πP.hom)
    rw [h2]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [LinearMap.mem_ker] at hx ⊢
      rw [LinearMap.comp_apply, hx, map_zero]
    · rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
      rw [LinearMap.mem_ker]
      refine hf ?_
      show fM.hom ((πP.hom) x) = fM.hom 0
      rw [hx, map_zero]
  have hex0 : (ShortComplex.mk hh gM hhg).Exact := by
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2 ?_
    show LinearMap.range (fM.hom.comp πP.hom) = LinearMap.ker (gM.hom)
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurjπ, Submodule.map_top]
    exact hkerfg.symm
  have hepi_g : Epi gM := (ModuleCat.epi_iff_surjective gM).2 hg
  have hQI : QuasiIso ((ChainComplex.toSingle₀Equiv D (ModuleCat.of R N₃)).symm
      ⟨gM, by rw [ChainComplex.augment_d_one_zero]; exact hhg⟩) :=
    Work.ORHomAlg.Flat.quasiIsoAugment Q hh w gM hhg hC hex1 hex0 hepi_g
  exact
    { complex := D
      projective := by
        intro n
        cases n with
        | zero => exact (inferInstance : Projective (ModuleCat.of R N₂))
        | succ n => exact P.projective n
      π := (ChainComplex.toSingle₀Equiv D (ModuleCat.of R N₃)).symm
        ⟨gM, by rw [ChainComplex.augment_d_one_zero]; exact hhg⟩
      quasiIso := hQI }

end Horseshoe

theorem torDimensionShift {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {N₁ : Type u} [AddCommGroup N₁] [Module R N₁] {N₂ : Type u} [AddCommGroup N₂] [Module R N₂]
    {N₃ : Type u} [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) (hf : Function.Injective f)
    (h : Function.Exact f g) (hg : Function.Surjective g) [Module.Projective R N₂] (n : ℕ) :
    Nonempty (Work.ORHomAlg.Tor (R := R) (n + 2) M N₃ ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := R) (n + 1) M N₁) := by
  classical
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} ℤ := tensorLeftFunctor (R := R) M
  let P : ProjectiveResolution (ModuleCat.of R N₁) := ProjectiveResolution.of (ModuleCat.of R N₁)
  have hDc : (torAugmentedResolution f g hf h hg P).complex =
      ChainComplex.augment P.complex (torAugmentationMap f P) (torAugmentationMap_comp_d f P) := rfl
  have e1 : (F.leftDerived (n + 2)).obj (ModuleCat.of R N₃) ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ChainComplex.augment P.complex (torAugmentationMap f P) (torAugmentationMap_comp_d f P))).homology (n + 2) := by
    have h1 := (torAugmentedResolution f g hf h hg P).isoLeftDerivedObj F (n + 2)
    rw [hDc] at h1
    exact h1
  have e2 := homologyAugmentIso F P.complex (torAugmentationMap f P) (torAugmentationMap_comp_d f P) (n + 1)
    (Nat.le_add_left 1 n)
  have e3 : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 1) ≅
      (F.leftDerived (n + 1)).obj (ModuleCat.of R N₁) := (P.isoLeftDerivedObj F (n + 1)).symm
  exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩

end Work.ORHomAlg.Tor
