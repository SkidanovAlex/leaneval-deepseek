import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.Basic
import Submission.Work.ORHomAlg.Flat.isFlatRight_iff_torOne
import Submission.Work.ORFlatness.injective_of_tor1Vanishes_right
import Submission.Work.ORFlatness.tor1Vanishes_of_shortExact_right
import Submission.Work.ORFlatness.leftFlat_iff_isFlatLeft
import Submission.Work.ORFlatness.leftFlat_of_projective
import Submission.Work.ORFlatness.projPres_exists

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORBridgeTor

/-!
Route hint for the prover (this is a vocabulary bridge, both directions are dimension shifting).

Recall
* `Work.ORFlatness.Tor1Vanishes R X N` is `∃ P : ProjPres R X, Injective (BalTensor.map R P.K.subtype id)`;
* `Work.ORHomAlg.Tor R 1 X N` is the first left derived functor of `X ⊠[R] -`;
* `Work.ORHomAlg.Flat.isFlatRight_iff_torOne` already proves the analogous bridge in the form
  `IsFlatRight R X ↔ ∀ N, Subsingleton (Tor R 1 X N)`, and its proof contains a private lemma
  `torOneKerSelf : Nonempty (Tor R 1 M N ≃ₗ[ℤ] LinearMap.ker (BalancedTensor.lTensor (ker π).subtype))`
  for any surjection `π : P →ₗ[R] N` with `P` projective — copied below.

Suggested route for `→` (given a projective presentation `0 → K → P → X → 0` of `X` with
`BalTensor.map R K.subtype id` injective, show `Subsingleton (Tor R 1 X N)`):
take a projective covering `π : P' →ₗ[R] N` of `N` (`Projective.over`), use `torOneKerSelf` to
identify `Tor R 1 X N` with `ker (X ⊠[R] K' → X ⊠[R] P')`, and get the injectivity of that map from
`Work.ORFlatness.injective_of_tor1Vanishes_right` applied to the short exact sequence
`0 → K' → P' → N → 0` (using `BalTensor`/`BalancedTensor` transport via
`Work.ORFlatness.baltensorEquiv`, `Work.ORFlatness.leftFlat_iff_isFlatLeft` and
`Work.ORFlatness.baltensorEquiv_mk`).

Suggested route for `←` (`Subsingleton (Tor R 1 X N) → Tor1Vanishes R X N`): with a projective
covering `π' : P' →ₗ[R] N` of `N`, `torOneKerSelf` turns the hypothesis into injectivity of
`X ⊠[R] K' → X ⊠[R] P'`; then `Work.ORFlatness.tor1Vanishes_of_shortExact_right` applied to
`0 → K' → P' → N → 0` gives `Tor1Vanishes R X N`, its hypothesis `Tor1Vanishes R X P'` following
from `Work.ORFlatness.leftFlat_of_projective` and `Work.ORFlatness.projPres_exists` since `P'` is
projective (hence the left module `P'` is left flat).
-/
open TensorProduct MulOpposite

universe u

/-! ## The transport between the two balanced tensor products

The two balanced tensor products `Work.ORFlatness.BalTensor` and `Work.ORHomAlg.BalancedTensor`
agree through `Work.ORFlatness.baltensorEquiv`, which is natural in the first variable
(`Work.ORFlatness.baltensorEquiv_map`).  Here we record naturality in the **second** variable,
which is what the `Tor`-vs-flatness bridge needs, and deduce that injectivity of
`X ⊠[R] f` is the same statement in either vocabulary. -/

/-- `Work.ORFlatness.baltensorEquiv` is natural in the second variable. -/
theorem baltensorEquiv_map_right (R : Type u) [Ring R] {X : Type u} [AddCommGroup X]
    [Module Rᵐᵒᵖ X] {N : Type u} [AddCommGroup N] [Module R N] {N' : Type u} [AddCommGroup N']
    [Module R N'] (g : N →ₗ[R] N') (z : Work.ORFlatness.BalTensor R X N) :
    Work.ORFlatness.baltensorEquiv R X N'
        (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g z) =
      Work.ORHomAlg.BalancedTensor.lTensor (M := X) g
        (Work.ORFlatness.baltensorEquiv R X N z) := by
  let u : Work.ORFlatness.BalTensor R X N →+ Work.ORHomAlg.BalancedTensor R X N' :=
    ((Work.ORFlatness.baltensorEquiv R X N').toLinearMap.toAddMonoidHom).comp
      (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g)
  let v : Work.ORFlatness.BalTensor R X N →+ Work.ORHomAlg.BalancedTensor R X N' :=
    (Work.ORHomAlg.BalancedTensor.lTensor (M := X) g).comp
      ((Work.ORFlatness.baltensorEquiv R X N).toLinearMap.toAddMonoidHom)
  have huv : u = v := by
    apply Work.ORFlatness.BalTensor.ext R
    intro x n
    show Work.ORFlatness.baltensorEquiv R X N'
        (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g
          (Work.ORFlatness.BalTensor.mk R x n)) =
      Work.ORHomAlg.BalancedTensor.lTensor (M := X) g
        (Work.ORFlatness.baltensorEquiv R X N (Work.ORFlatness.BalTensor.mk R x n))
    simp only [Work.ORFlatness.BalTensor.map_mk, Work.ORFlatness.baltensorEquiv_mk,
      Work.ORHomAlg.BalancedTensor.lTensor_tmul, LinearMap.id_apply]
  exact congrFun (congrArg DFunLike.coe huv) z

/-- Injectivity of two maps related by a commutative square with bijections on the sides. -/
private theorem inj_iff_of_bijective {A A' B B' : Type*}
    (e : A → A') (e' : B → B') (he : Function.Bijective e) (he' : Function.Bijective e')
    (u : A → B) (v : A' → B') (h : ∀ a, e' (u a) = v (e a)) :
    Function.Injective u ↔ Function.Injective v := by
  constructor
  · intro hu a' b' hab
    obtain ⟨a, rfl⟩ := he.2 a'
    obtain ⟨b, rfl⟩ := he.2 b'
    have h1 : a = b := hu (he'.1 (by
      show e' (u a) = e' (u b)
      rw [h a, h b]
      exact hab))
    rw [h1]
  · intro hv a b hab
    have h2 : v (e a) = v (e b) := by
      rw [← h a, ← h b, hab]
    exact he.1 (hv h2)

/-- Injectivity of `X ⊠[R] f` is the same in the two vocabularies. -/
theorem injective_lTensor_iff (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] {N₁ : Type u} [AddCommGroup N₁] [Module R N₁] {N₂ : Type u}
    [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂) :
    Function.Injective (Work.ORHomAlg.BalancedTensor.lTensor (M := X) f) ↔
      Function.Injective
        (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f) :=
  (inj_iff_of_bijective
    (⇑(Work.ORFlatness.baltensorEquiv R X N₁))
    (⇑(Work.ORFlatness.baltensorEquiv R X N₂))
    (Work.ORFlatness.baltensorEquiv R X N₁).bijective
    (Work.ORFlatness.baltensorEquiv R X N₂).bijective
    (⇑(Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f))
    (⇑(Work.ORHomAlg.BalancedTensor.lTensor (M := X) f))
    (fun z => baltensorEquiv_map_right R f z)).symm

/-- An injective `ℤ`-linear map has subsingleton kernel. -/
private theorem subsingleton_ker_of_injective_lm {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →ₗ[ℤ] B) (hf : Function.Injective f) :
    Subsingleton (LinearMap.ker f) :=
  ⟨fun a b => by
    refine Subtype.ext (hf ?_)
    rw [a.property, b.property]⟩

/-- An additive map with injective underlying function has subsingleton kernel. -/
private theorem subsingleton_ker_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (h : Function.Injective φ) :
    Subsingleton (LinearMap.ker φ.toIntLinearMap) :=
  subsingleton_ker_of_injective_lm φ.toIntLinearMap h

/-- A `ℤ`-linear map with subsingleton kernel is injective. -/
private theorem injective_of_subsingleton_ker_lm {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →ₗ[ℤ] B) (h : Subsingleton (LinearMap.ker f)) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have h1 : (⟨x, hx⟩ : LinearMap.ker f) = ⟨0, by simp⟩ := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

/-- An additive map with subsingleton kernel is injective. -/
private theorem injective_of_subsingleton_ker {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (h : Subsingleton (LinearMap.ker φ.toIntLinearMap)) :
    Function.Injective φ := by
  intro a b hab
  exact injective_of_subsingleton_ker_lm φ.toIntLinearMap h hab

/-- A left flat module `M` has `Tor₁^R(X, M) = 0` for every right module `X`: any projective
presentation of `X` witnesses it, since its kernel inclusion is injective. -/
theorem tor1Vanishes_of_leftFlat (R : Type u) [Ring R] {M : Type u} [AddCommGroup M]
    [Module R M] (hM : Work.ORFlatness.LeftFlat R M) (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] : Work.ORFlatness.Tor1Vanishes R X M := by
  obtain ⟨P⟩ := Work.ORFlatness.projPres_exists (R := R) X
  exact ⟨P, hM (Submodule.subtype P.K) (Submodule.injective_subtype P.K)⟩

section TorOneKerSelf

open CategoryTheory CategoryTheory.Limits
open Work.ORHomAlg
open Work.ORHomAlg.Flat

theorem torOneKerSelf {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
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

end TorOneKerSelf

/-- Dimension shifting, forward direction: if `Tor₁^R(X, N)` vanishes in the sense of the
dimension criterion (witnessed by some projective presentation of `X`), and `0 → K → P → N → 0`
is any presentation of `N` with `P` projective, then the map `X ⊠[R] K → X ⊠[R] P` is injective,
so `Tor₁^R(X, N)` — the kernel of that map — is trivial. -/
theorem subsingleton_tor_of_tor1Vanishes (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P]
    {N : Type u} [AddCommGroup N] [Module R N] (π : P →ₗ[R] N)
    (hπ : Function.Surjective π) (htor : Work.ORFlatness.Tor1Vanishes R X N) :
    Subsingleton (Work.ORHomAlg.Tor (R := R) 1 X N) := by
  let ι := (LinearMap.ker π).subtype
  obtain ⟨e⟩ := torOneKerSelf (R := R) (M := X) π hπ
  have hf : Function.Injective ι := Submodule.injective_subtype _
  have hfg : ι.range = LinearMap.ker π := Submodule.range_subtype _
  have hinjBal := Work.ORFlatness.injective_of_tor1Vanishes_right ι π hf hπ hfg X htor
  have hinjL := (injective_lTensor_iff R X ι).mpr hinjBal
  have hsub := subsingleton_ker_of_injective _ hinjL
  exact ⟨fun a b => e.injective (hsub.elim (e a) (e b))⟩

/-- Dimension shifting, backward direction: if `Tor₁^R(X, N)` is trivial and `0 → K → P → N → 0`
is a presentation of `N` with `P` projective, then `X ⊠[R] K → X ⊠[R] P` is injective; together
with `Tor₁^R(X, P) = 0` (as `P` is projective, hence left flat) this shows that the presentation
of `X` given by `0 → K → P → N → 0` witnesses `Tor1Vanishes R X N`. -/
theorem tor1Vanishes_of_subsingleton_tor (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P]
    {N : Type u} [AddCommGroup N] [Module R N] (π : P →ₗ[R] N)
    (hπ : Function.Surjective π) (hT : Subsingleton (Work.ORHomAlg.Tor (R := R) 1 X N)) :
    Work.ORFlatness.Tor1Vanishes R X N := by
  let ι := (LinearMap.ker π).subtype
  obtain ⟨e⟩ := torOneKerSelf (R := R) (M := X) π hπ
  have hinjL : Function.Injective (Work.ORHomAlg.BalancedTensor.lTensor (M := X) ι) := by
    refine injective_of_subsingleton_ker_lm
      (Work.ORHomAlg.BalancedTensor.lTensor (M := X) ι).toIntLinearMap ?_
    refine ⟨fun a b => ?_⟩
    have h : e.symm a = e.symm b := hT.elim _ _
    calc a = e (e.symm a) := (LinearEquiv.apply_symm_apply e a).symm
      _ = e (e.symm b) := by rw [h]
      _ = b := LinearEquiv.apply_symm_apply e b
  have hinjBal := (injective_lTensor_iff R X ι).mp hinjL
  have hfg : ι.range = LinearMap.ker π := Submodule.range_subtype _
  have hflat : Work.ORFlatness.Tor1Vanishes R X P :=
    tor1Vanishes_of_leftFlat (R := R) (M := P)
      (Work.ORFlatness.leftFlat_of_projective (R := R) (M := P)) X
  exact Work.ORFlatness.tor1Vanishes_of_shortExact_right ι π hπ hfg X hflat hinjBal

/-- `Tor₁^R(X, N) = 0` (in the sense of the dimension criterion `Tor1Vanishes`, i.e. vanishing of
the first left derived functor of `X ⊠[R] -`) if and only if the group `Tor₁^R(X, N)` itself is
trivial.  Both directions are dimension shifting along a projective presentation of `N`, using
that `Tor₁^R(X, N)` is the kernel of `X ⊠[R] K → X ⊠[R] P` for `0 → K → P → N → 0`. -/
theorem tor1Vanishes_iff_tor (R : Type u) [Ring R]
    (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (N : Type u) [AddCommGroup N] [Module R N] :
    Work.ORFlatness.Tor1Vanishes R X N ↔
      Subsingleton (Work.ORHomAlg.Tor (R := R) 1 X N) := by
  constructor
  · intro htor
    let π : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (id : N → N)
    have hπ : Function.Surjective π := by
      show Function.Surjective (Finsupp.linearCombination R (id : N → N))
      exact Finsupp.linearCombination_id_surjective (R := R) N
    exact subsingleton_tor_of_tor1Vanishes (R := R) (X := X) (P := ↑(N →₀ R)) (N := N)
      π hπ htor
  · intro hT
    let π : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (id : N → N)
    have hπ : Function.Surjective π := by
      show Function.Surjective (Finsupp.linearCombination R (id : N → N))
      exact Finsupp.linearCombination_id_surjective (R := R) N
    exact tor1Vanishes_of_subsingleton_tor (R := R) (X := X) (P := ↑(N →₀ R)) (N := N)
      π hπ hT

end Work.ORBridgeTor
