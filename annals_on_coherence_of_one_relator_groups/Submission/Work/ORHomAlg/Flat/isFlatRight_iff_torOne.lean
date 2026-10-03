import Mathlib
import Submission.Work.ORHomAlg.Flat
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.Exactness.lTensor_surjective
import Submission.Work.ORHomAlg.Flat.lTensor_range_eq_ker
import Submission.Work.ORHomAlg.Tor.lTensor_exact_of_surjective
import Submission.Work.ORHomAlg.Flat.quasiIsoAugment
import Submission.Work.ORHomAlg.Flat.exists_sigma_of_injective

namespace Work.ORHomAlg.Flat

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- If the kernel of a `ℤ`-linear map is a subsingleton then the map is injective. -/
private lemma injective_of_subsingleton_ker {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (f : X →ₗ[ℤ] Y) (h : Subsingleton (LinearMap.ker f)) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have h1 : (⟨x, hx⟩ : LinearMap.ker f) = ⟨0, by simp⟩ := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

/-- The kernel of an injective `ℤ`-linear map is a subsingleton. -/
private lemma subsingleton_ker_of_injective {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (f : X →ₗ[ℤ] Y) (hf : Function.Injective f) : Subsingleton (LinearMap.ker f) :=
  ⟨fun a b => by
    refine Subtype.ext (hf ?_)
    rw [a.property, b.property]⟩

/-- Tensoring the zero map gives the zero map. -/
private lemma lTensor_zero' {N N' : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] :
    BalancedTensor.lTensor (M := M) (0 : N →ₗ[R] N') = 0 := by
  rw [BalancedTensor.lTensor, BalancedTensor.map_zero_right]

/-- `Tor_1^R(M, N)` computed from a projective presentation `π : P →ₗ[R] N`. -/
private theorem torOneKerSelf {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {P : Type u} [AddCommGroup P] [Module R P] {N : Type u} [AddCommGroup N] [Module R N]
    (π : P →ₗ[R] N) (hπ : Function.Surjective π) [Module.Projective R P] :
    Nonempty (Work.ORHomAlg.Tor (R := R) 1 M N ≃ₗ[ℤ]
      LinearMap.ker
        (Work.ORHomAlg.BalancedTensor.lTensor (M := M) (LinearMap.ker π).subtype).toIntLinearMap) := by
  classical
  let f : (LinearMap.ker π) →ₗ[R] P := (LinearMap.ker π).subtype
  have hf : Function.Injective f := (LinearMap.ker π).injective_subtype
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} ℤ := tensorLeftFunctor (R := R) M
  let R₁ : ProjectiveResolution (ModuleCat.of R (LinearMap.ker π)) :=
    ProjectiveResolution.of (ModuleCat.of R (LinearMap.ker π))
  let Q : ChainComplex (ModuleCat.{u} R) ℕ := R₁.complex
  let πP : Q.X 0 ⟶ ModuleCat.of R (LinearMap.ker π) := R₁.π.f 0
  have hQπ : Q.d 1 0 ≫ πP = 0 := R₁.complex_d_comp_π_f_zero
  have hsurjπ : Function.Surjective (πP.hom) := by
    have hEpi : Epi πP := by
      change Epi (R₁.π.f 0)
      infer_instance
    exact (ModuleCat.epi_iff_surjective πP).mp hEpi
  have hC : ∀ n : ℕ, Q.ExactAt (n + 1) := fun n => R₁.complex_exactAt_succ n
  have hexact_dπ : Function.Exact (Q.d 1 0).hom (πP.hom) := by
    have h1 : (ShortComplex.mk (Q.d 1 0) πP hQπ).Exact :=
      (ShortComplex.mk (Q.d 1 0) πP hQπ).exact_of_g_is_cokernel R₁.isColimitCokernelCofork
    have h2 : LinearMap.range (Q.d 1 0).hom = LinearMap.ker (πP.hom) :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h1
    exact LinearMap.exact_iff.2 h2.symm
  let fM : ModuleCat.of R (LinearMap.ker π) ⟶ ModuleCat.of R P := ModuleCat.ofHom f
  let gM : ModuleCat.of R P ⟶ ModuleCat.of R N := ModuleCat.ofHom π
  have hfg : gM.hom.comp fM.hom = 0 := by
    ext x
    exact x.property
  have hfgM : fM ≫ gM = 0 := ModuleCat.hom_ext hfg
  let hh : Q.X 0 ⟶ ModuleCat.of R P := πP ≫ fM
  have w : Q.d 1 0 ≫ hh = 0 := by
    show Q.d 1 0 ≫ (πP ≫ fM) = 0
    rw [← Category.assoc, hQπ, zero_comp]
  let D : ChainComplex (ModuleCat.{u} R) ℕ := Q.augment hh w
  have hD10 : D.d 1 0 = hh := ChainComplex.augment_d_one_zero Q hh w
  have hD21 : D.d 2 1 = Q.d 1 0 := ChainComplex.augment_d_succ_succ Q hh w 1 0
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
    show LinearMap.range ((LinearMap.ker π).subtype) = LinearMap.ker π
    exact Submodule.range_subtype _
  have hepi_g : Epi gM := (ModuleCat.epi_iff_surjective gM).2 hπ
  have hQI : QuasiIso ((ChainComplex.toSingle₀Equiv D (ModuleCat.of R N)).symm
      ⟨gM, by rw [ChainComplex.augment_d_one_zero]; exact hhg⟩) :=
    quasiIsoAugment Q hh w gM hhg hC hex1 hex0 hepi_g
  let pres : ProjectiveResolution (ModuleCat.of R N) :=
    { complex := D
      projective := by
        intro n
        cases n with
        | zero => exact (inferInstance : Projective (ModuleCat.of R P))
        | succ n => exact R₁.projective n
      π := (ChainComplex.toSingle₀Equiv D (ModuleCat.of R N)).symm
        ⟨gM, by rw [ChainComplex.augment_d_one_zero]; exact hhg⟩
      quasiIso := hQI }
  let K : ChainComplex (ModuleCat.{u} ℤ) ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have hKd : ∀ i j : ℕ, K.d i j = F.map (D.d i j) :=
    fun i j => Functor.mapHomologicalComplex_obj_d F (ComplexShape.down ℕ) D i j
  have e1 : (F.leftDerived 1).obj (ModuleCat.of R N) ≅ K.homology 1 :=
    pres.isoLeftDerivedObj F 1
  let S : ShortComplex (ModuleCat.{u} ℤ) :=
    ShortComplex.mk (K.d 2 1) (K.d 1 0) (K.d_comp_d 2 1 0)
  have hSf : S.f = K.d 2 1 := rfl
  have hSg : S.g = K.d 1 0 := rfl
  have e2a : K.homology 1 ≅ S.homology :=
    K.homologyIsoSc' 2 1 0 (ComplexShape.prev_eq' _ (by rfl)) (ComplexShape.next_eq' _ (by rfl))
  have hSMf : S.f.hom = (F.map (Q.d 1 0)).hom := by
    rw [hSf, hKd, hD21]
    rfl
  have hSMg : S.g.hom = (F.map fM).hom.comp (F.map πP).hom := by
    rw [hSg, hKd, hD10]
    show (F.map (πP ≫ fM)).hom = _
    rw [F.map_comp, ModuleCat.hom_comp]
  have e2 : S.homology ≅ S.moduleCatLeftHomologyData.H := S.moduleCatHomologyIso
  have hrange : LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
    show (LinearMap.codRestrict (LinearMap.ker S.g.hom) S.f.hom _).range = _
    exact LinearMap.range_codRestrict (LinearMap.ker S.g.hom) S.f.hom _
  have e3 : S.moduleCatLeftHomologyData.H ≅ ModuleCat.of ℤ (LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype) :=
    LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ hrange)
  let Tsub : Submodule ℤ (BalancedTensor R M (LinearMap.ker π)) :=
    LinearMap.ker (BalancedTensor.lTensor (M := M) f).toIntLinearMap
  let T : Type u := ↥Tsub
  have hFf : (F.map fM).hom =
      (BalancedTensor.lTensor (M := M) f).toIntLinearMap := rfl
  have hFp_surj : Function.Surjective ((F.map πP).hom) := by
    have h1 : Function.Surjective
        (⇑(BalancedTensor.lTensor (M := M) (πP.hom)).toIntLinearMap) :=
      Work.ORHomAlg.Exactness.lTensor_surjective (M := M) (πP.hom) hsurjπ
    exact h1
  have hrange_eq : LinearMap.range S.f.hom = LinearMap.ker ((F.map πP).hom) := by
    rw [hSMf]
    have hA : Function.Exact
        (⇑(BalancedTensor.lTensor (M := M) (Q.d 1 0).hom).toIntLinearMap)
        (⇑(BalancedTensor.lTensor (M := M) (πP.hom)).toIntLinearMap) :=
      Work.ORHomAlg.Tor.lTensor_exact_of_surjective (Q.d 1 0).hom (πP.hom) hsurjπ hexact_dπ
    exact (LinearMap.exact_iff.1 hA).symm
  have hgen : ∀ y : ↥(F.obj (Q.X 0)), S.g.hom y = 0 →
      (BalancedTensor.lTensor (M := M) f).toIntLinearMap ((F.map πP).hom y) = 0 := by
    intro y hy
    have hy1 : ((F.map fM).hom.comp (F.map πP).hom) y = 0 := hSMg ▸ hy
    rw [LinearMap.comp_apply] at hy1
    rw [hFf] at hy1
    exact hy1
  let φ : ↥(LinearMap.ker S.g.hom) →ₗ[ℤ] ↥Tsub :=
    ((F.map πP).hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict Tsub
      (fun x => by
        show (BalancedTensor.lTensor (M := M) f).toIntLinearMap
          ((F.map πP).hom x.1) = 0
        exact hgen x.1 x.2)
  have hsurjφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hFp_surj y.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · have hx2 : ((F.map fM).hom.comp (F.map πP).hom) x = 0 := by
        rw [LinearMap.comp_apply, hx, hFf]
        exact y.2
      exact hSMg.symm ▸ hx2
    · apply Subtype.ext
      exact hx
  have hkerφ : φ.ker = (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
    ext x
    constructor
    · intro hx
      have h1 : (F.map πP).hom x.1 = 0 := Subtype.ext_iff.mp hx
      have h2 : x.1 ∈ LinearMap.ker (F.map πP).hom := h1
      exact hrange_eq.symm ▸ h2
    · intro hx
      have h2 : x.1 ∈ LinearMap.ker (F.map πP).hom := hrange_eq ▸ hx
      exact Subtype.ext_iff.mpr h2
  have e4a : (↥(S.g.hom.ker) ⧸ (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype)
      ≃ₗ[ℤ] (↥(S.g.hom.ker) ⧸ φ.ker) :=
    Submodule.quotEquivOfEq _ _ hkerφ.symm
  have e4b : (↥(S.g.hom.ker) ⧸ φ.ker) ≃ₗ[ℤ] T :=
    LinearMap.quotKerEquivOfSurjective φ hsurjφ
  have e4 : ModuleCat.of ℤ (LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype) ≅ ModuleCat.of ℤ T :=
    LinearEquiv.toModuleIso (e4a.trans e4b)
  exact ⟨(e1 ≪≫ e2a ≪≫ e2 ≪≫ e3 ≪≫ e4).toLinearEquiv⟩

/-- A right `R`-module `M` is flat if and only if `Tor_1^R(M, -)` vanishes. -/
theorem isFlatRight_iff_torOne {R : Type u} [Ring R] {M : Type u} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] :
    Work.ORHomAlg.IsFlatRight R M ↔
      ∀ (N : Type u) [AddCommGroup N] [Module R N],
        Subsingleton (Work.ORHomAlg.Tor (R := R) 1 M N) := by
  constructor
  · intro hflat N _ _
    let P : ModuleCat.{u} R := Projective.over (ModuleCat.of R N)
    let π : P →ₗ[R] N := (Projective.π (ModuleCat.of R N)).hom
    have hπ : Function.Surjective π := by
      have hepi : Epi (Projective.π (ModuleCat.of R N)) := inferInstance
      exact (ModuleCat.epi_iff_surjective _).mp hepi
    have hinj : Function.Injective ((LinearMap.ker π).subtype) := (LinearMap.ker π).injective_subtype
    have hli : Function.Injective (BalancedTensor.lTensor (M := M) (LinearMap.ker π).subtype) :=
      hflat (LinearMap.ker π).subtype hinj
    have hsub : Subsingleton
        (LinearMap.ker (BalancedTensor.lTensor (M := M) (LinearMap.ker π).subtype).toIntLinearMap) :=
      subsingleton_ker_of_injective _ hli
    obtain ⟨e⟩ := torOneKerSelf (R := R) (M := M) π hπ
    exact ⟨fun a b => e.injective (hsub.elim (e a) (e b))⟩
  · intro htor N N' _ _ _ _ g hg
    let C := N' ⧸ LinearMap.range g
    let g' : N' →ₗ[R] C := Submodule.mkQ (LinearMap.range g)
    let P : ModuleCat.{u} R := Projective.over (ModuleCat.of R N')
    let π' : P →ₗ[R] N' := (Projective.π (ModuleCat.of R N')).hom
    have hπ' : Function.Surjective π' := by
      have hepi : Epi (Projective.π (ModuleCat.of R N')) := inferInstance
      exact (ModuleCat.epi_iff_surjective _).mp hepi
    have hg' : Function.Surjective g' := Submodule.mkQ_surjective _
    let πC : P →ₗ[R] C := g'.comp π'
    have hπC : Function.Surjective πC := hg'.comp hπ'
    obtain ⟨eC⟩ := torOneKerSelf (R := R) (M := M) πC hπC
    have hsub : Subsingleton
        (LinearMap.ker
          (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype).toIntLinearMap) :=
      ⟨fun a b => by
        have h : eC.symm a = eC.symm b := Subsingleton.elim _ _
        calc a = eC (eC.symm a) := (LinearEquiv.apply_symm_apply eC a).symm
          _ = eC (eC.symm b) := by rw [h]
          _ = b := LinearEquiv.apply_symm_apply eC b⟩
    have hQinj : Function.Injective
        (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype) :=
      injective_of_subsingleton_ker _ hsub
    obtain ⟨σ, hσsq, hσsurj, hσker⟩ := exists_sigma_of_injective g hg π' hπ'
    have hKQ : LinearMap.ker π' ≤ LinearMap.ker πC := by
      intro p hp
      rw [LinearMap.mem_ker] at hp ⊢
      show g' (π' p) = 0
      rw [hp, map_zero]
    let γ : (LinearMap.ker π') →ₗ[R] (LinearMap.ker πC) :=
      (LinearMap.ker π').subtype.codRestrict (LinearMap.ker πC) (fun c => hKQ c.property)
    have hγcomp : (LinearMap.ker πC).subtype.comp γ = (LinearMap.ker π').subtype := by
      ext k
      rfl
    have hγ : γ.range = LinearMap.ker σ := by
      ext q
      constructor
      · rintro ⟨k, hk⟩
        rw [← hk, LinearMap.mem_ker]
        exact (hσker (γ k)).mpr k.property
      · intro hq
        rw [LinearMap.mem_ker] at hq
        exact ⟨⟨(q : P), (hσker q).mp hq⟩, Subtype.ext rfl⟩
    have hex1 : (BalancedTensor.lTensor (M := M) γ).range
        = (BalancedTensor.lTensor (M := M) σ).ker :=
      lTensor_range_eq_ker (M := M) γ σ hσsurj hγ
    have hex2 : (BalancedTensor.lTensor (M := M) (LinearMap.ker π').subtype).range
        = (BalancedTensor.lTensor (M := M) π').ker :=
      lTensor_range_eq_ker (M := M) (LinearMap.ker π').subtype π' hπ'
        (Submodule.range_subtype _)
    intro a b hab
    have hz : BalancedTensor.lTensor (M := M) g (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨y, hy⟩ := Work.ORHomAlg.Exactness.lTensor_surjective (M := M) σ hσsurj (a - b)
    have hcomp : (BalancedTensor.lTensor (M := M) π').comp
        (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype)
        = (BalancedTensor.lTensor (M := M) g).comp (BalancedTensor.lTensor (M := M) σ) := by
      rw [← BalancedTensor.lTensor_comp, ← BalancedTensor.lTensor_comp, hσsq]
    have h1 : BalancedTensor.lTensor (M := M) π'
        (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype y) = 0 := by
      rw [show BalancedTensor.lTensor (M := M) π'
            (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype y)
          = ((BalancedTensor.lTensor (M := M) π').comp
              (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype)) y from rfl,
        hcomp]
      rw [show ((BalancedTensor.lTensor (M := M) g).comp
            (BalancedTensor.lTensor (M := M) σ)) y
          = BalancedTensor.lTensor (M := M) g (BalancedTensor.lTensor (M := M) σ y) from rfl,
        hy, hz]
    have h2 : BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype y
        ∈ (BalancedTensor.lTensor (M := M) (LinearMap.ker π').subtype).range := by
      rw [hex2, AddMonoidHom.mem_ker]
      exact h1
    obtain ⟨k, hk⟩ := h2
    have hcomp2 : (BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype).comp
        (BalancedTensor.lTensor (M := M) γ)
        = BalancedTensor.lTensor (M := M) (LinearMap.ker π').subtype := by
      rw [← BalancedTensor.lTensor_comp, hγcomp]
    have h3 : y = BalancedTensor.lTensor (M := M) γ k := by
      refine hQinj ?_
      rw [show BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype
              (BalancedTensor.lTensor (M := M) γ k)
            = ((BalancedTensor.lTensor (M := M) (LinearMap.ker πC).subtype).comp
                (BalancedTensor.lTensor (M := M) γ)) k from rfl, hcomp2, ← hk]
    have hσγ : σ.comp γ = 0 := by
      ext k
      rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, ← hγ]
      exact ⟨k, rfl⟩
    have h4 : a - b = 0 := by
      rw [← hy, h3]
      rw [show BalancedTensor.lTensor (M := M) σ (BalancedTensor.lTensor (M := M) γ k)
            = ((BalancedTensor.lTensor (M := M) σ).comp
                (BalancedTensor.lTensor (M := M) γ)) k from rfl,
        ← BalancedTensor.lTensor_comp, hσγ, lTensor_zero']
      rfl
    exact sub_eq_zero.mp h4

end Work.ORHomAlg.Flat
