import Mathlib
import Submission.Work.SSGRoute.SSGDescentDefs
import Submission.Work.SSGRoute.homRep_unitsK_formula
import Submission.Work.SSGRoute.homRep_unitsK_formula_natural
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.SSGRoute.isDiscreteModule_homCoind
import Submission.Work.SSGRoute.homCoind_H0_restrict_ker_conj
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact
import Submission.Work.SSGRoute.ext_h1_bridge
import Submission.Work.SSGRoute.closure_eq_top_of_module_finite_ulift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] homCoind.instDistribMulActionAlgEquiv

/-! ## The spelling equivalence between `ssgHom` and `homCoind`

`SSGDescent.ssgHom L M K N` is the *linear-map* spelling
`(infl N).V →ₗ[Coeff] Mˣ` of `Hom_ℤ(infl N, Mˣ)`, whereas `homCoind L M K N` is the
*additive-map* spelling `N.V →+ Mˣ`.  Since `Coeff = ULift ℤ` acts through `zsmul`, the two
spellings are the same abelian group, and the conjugation action is the same; the two lemmas
below record the additive equivalence and its equivariance. -/

/-- `Coeff = ULift ℤ`-linear maps are additive maps, as abelian groups. -/
def coeffLinEquivAdd (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    (A →ₗ[SSGRoute.PTExt.Coeff] B) ≃+ (A →+ B) where
  toFun f := f.toAddMonoidHom
  invFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => f.map_zsmul c.down x }
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl

/-- **The spelling equivalence** `ssgHom L M K N ≃+ homCoind L M K N`. -/
noncomputable def ssgHomEquiv (L M : Type) [Field L] [Field M] [Algebra L M]
    (K : IntermediateField L M) [Normal L ↥K] (N : Rep.{0} Coeff (K ≃ₐ[L] K)) :
    Work.SSGRoute.SSGDescent.ssgHom L M K N ≃+ Work.SSGRoute.homCoind L M K N where
  toFun f := f.toAddMonoidHom
  invFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => f.map_zsmul c.down x }
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl

/-- The `AddEquiv` `ssgHomEquiv` is equivariant for the conjugation actions. -/
theorem ssgHomEquiv_equivariant (L M : Type) [Field L] [Field M] [Algebra L M]
    (K : IntermediateField L M) [Normal L ↥K] (N : Rep.{0} Coeff (K ≃ₐ[L] K))
    (σ : M ≃ₐ[L] M) (f : Work.SSGRoute.SSGDescent.ssgHom L M K N) :
    ssgHomEquiv L M K N (σ • f) = σ • (ssgHomEquiv L M K N f) := by
  have hkey : ∀ a : Additive Mˣ, (SSGDescent.ssgCoeffM L M).ρ σ a
      = homCoind.smulHom (k := L) (Ω := M) σ a := fun a => rfl
  apply AddMonoidHom.ext
  intro x
  show (SSGDescent.ssgCoeffM L M).ρ σ (f ((N.ρ ((SSGDescent.ssgResHom L M K) σ⁻¹)) x))
      = homCoind.smulHom (k := L) (Ω := M) σ
          (f ((N.ρ ((SSGDescent.ssgResHom L M K) σ)⁻¹) x))
  rw [show (SSGDescent.ssgResHom L M K) σ⁻¹ = ((SSGDescent.ssgResHom L M K) σ)⁻¹ from
    map_inv _ _]
  exact hkey _

/-- The `AddEquiv` `ssgHomEquiv` is equivariant, in the inverse direction. -/
theorem ssgHomEquiv_symm_equivariant (L M : Type) [Field L] [Field M] [Algebra L M]
    (K : IntermediateField L M) [Normal L ↥K] (N : Rep.{0} Coeff (K ≃ₐ[L] K))
    (σ : M ≃ₐ[L] M) (f : Work.SSGRoute.homCoind L M K N) :
    (ssgHomEquiv L M K N).symm (σ • f) = σ • ((ssgHomEquiv L M K N).symm f) := by
  rw [show f = ssgHomEquiv L M K N ((ssgHomEquiv L M K N).symm f) from
    (AddEquiv.apply_symm_apply _ f).symm]
  rw [← ssgHomEquiv_equivariant L M K N σ ((ssgHomEquiv L M K N).symm f)]
  exact AddEquiv.symm_apply_apply _ _

/-! ## The main theorem (additive-map spelling) -/

/-- **The continuous descent for a finitely generated module, `homCoind` spelling.** -/
theorem ext_continuous_descent_fg_homCoind {L M : Type} [Field L] [CharZero L] [Field M]
    [Algebra L M] [IsAlgClosure L M] (K : IntermediateField L M) [FiniteDimensional L K]
    [IsGalois L K] (X : Rep.{0} Coeff (K ≃ₐ[L] K)) [Module.Finite (ULift ℤ) X.V] :
    Nonempty (CategoryTheory.Abelian.Ext X (SSGRoute.PTExt.unitsK L K) 1 ≃+
      Work.AbsoluteKummer.H1 (M ≃ₐ[L] M) (homCoind L M K X)) := by
  classical
  obtain ⟨s, hclos⟩ : ∃ s : Finset X.V, AddSubgroup.closure (s : Set X.V) = ⊤ := by
    haveI hfin : Module.Finite (ULift ℤ) X.V := ‹Module.Finite (ULift ℤ) X.V›
    obtain ⟨S, hSfin, hSspan⟩ :=
      Submodule.fg_def.mp (Module.Finite.fg_top (R := ULift ℤ) (M := X.V))
    refine ⟨hSfin.toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
    refine le_antisymm le_top ?_
    intro x _
    exact mem_addSubgroup_closure_of_mem_span S (by rw [hSspan]; exact Submodule.mem_top)
  let F : Rep.{0} Coeff (K ≃ₐ[L] K) := Rep.free Coeff (K ≃ₐ[L] K) ↥s
  let pic : F ⟶ X := Rep.freeLift Coeff (K ≃ₐ[L] K) X (fun i : ↥s => (i : X.V))
  haveI : Finite ↥s := inferInstance
  have hkey : ∀ y ∈ AddSubgroup.closure (s : Set X.V), ∃ u : F.V, Rep.Hom.hom pic u = y := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
        letI : Module Coeff X.V := X.hV2
        exact ⟨Finsupp.single ⟨z, hz⟩ (MonoidAlgebra.single 1 1), by
          show (Rep.Hom.hom pic) (Finsupp.single ⟨z, hz⟩ (MonoidAlgebra.single 1 1)) = z
          rw [show Rep.Hom.hom pic = Representation.freeLift X.ρ (fun i : ↥s => (i : X.V)) from
            rfl]
          rw [Representation.freeLift_single_single]
          simp only [map_one, LinearMap.id_apply]
          exact (ulift_up_smul_eq_zsmul (V := X.V) (1 : ℤ) z).trans (one_zsmul z)⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ia ib =>
        obtain ⟨u, hu⟩ := ia
        obtain ⟨v, hv⟩ := ib
        exact ⟨u + v, by rw [map_add, hu, hv]⟩
    | neg a _ ia =>
        obtain ⟨u, hu⟩ := ia
        exact ⟨-u, by rw [map_neg, hu]⟩
  have hfsurj : Function.Surjective (Rep.Hom.hom pic) := by
    intro y
    exact hkey y (by rw [hclos]; trivial)
  have hpic : Epi pic := (Rep.epi_iff_surjective pic).mpr hfsurj
  -- ===== the Ext side =====
  let S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[L] K)) :=
    ShortComplex.mk (Limits.kernel.ι pic) pic (Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  have hExt := ext_connecting_range_ker hS (unitsK L K)
  let ΦE : Abelian.Ext S.X₁ (unitsK L K) 0 →+ Abelian.Ext X (unitsK L K) 1 :=
    hS.extClass.precomp (unitsK L K) (by norm_num : 1 + 0 = 1)
  have hΦEsurj : Function.Surjective ΦE := (AddMonoidHom.range_eq_top).mp hExt.1
  let pre : Abelian.Ext S.X₂ (unitsK L K) 0 →+ Abelian.Ext S.X₁ (unitsK L K) 0 :=
    (Abelian.Ext.mk₀ S.f).precomp (unitsK L K) (by norm_num : 0 + 0 = 0)
  have hΦEker : ΦE.ker = pre.range := hExt.2
  -- ===== the cohomology side =====
  let uHom : S.X₁.V →+ S.X₂.V :=
    { toFun := fun x => Rep.Hom.hom S.f x
      map_zero' := map_zero (Rep.Hom.hom S.f)
      map_add' := fun a b => map_add (Rep.Hom.hom S.f) a b }
  let gFun : homCoind L M K S.X₂ →+ homCoind L M K S.X₁ :=
    { toFun := fun φ => φ.comp uHom
      map_zero' := by ext x; rfl
      map_add' := by intro a b; ext x; rfl }
  have hG : ∀ (ψ : homCoind L M K S.X₂) (y : S.X₁.V),
      gFun ψ y = ψ (Rep.Hom.hom S.f y) := fun ψ y => rfl
  have gFun_mem : ∀ φ ∈ (@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)),
      gFun φ ∈ (@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) := by
    intro φ hφ
    intro σ
    apply AddMonoidHom.ext
    intro x
    rw [show (σ • (gFun φ)) x
        = homCoind.smulHom (k := L) (Ω := M) σ
            ((gFun φ) (S.X₁.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ x)) from rfl]
    have h1 : gFun φ (S.X₁.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ x)
        = φ (S.X₂.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ (Rep.Hom.hom S.f x)) := by
      rw [hG, Rep.hom_comm_apply]
    have h3 : homCoind.smulHom (k := L) (Ω := M) σ
          ((gFun φ) (S.X₁.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ x))
        = homCoind.smulHom (k := L) (Ω := M) σ
            (φ (S.X₂.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ (Rep.Hom.hom S.f x))) := by
      rw [h1]
    have h2 : homCoind.smulHom (k := L) (Ω := M) σ
          (φ (S.X₂.ρ ((SSGDescent.ssgResHom L M K σ))⁻¹ (Rep.Hom.hom S.f x)))
        = φ (Rep.Hom.hom S.f x) :=
      DFunLike.congr_fun (hφ σ) (Rep.Hom.hom S.f x)
    rw [h3, h2]
    exact (hG φ x).symm
  let g : ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) →+
      ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (gFun.comp (AddSubgroup.subtype _)).codRestrict _ (fun φ => gFun_mem φ.1 φ.2)
  have hg : ∀ (ψ : ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)))
      (x : S.X₁.V), Subtype.val (g ψ) x = Subtype.val ψ (Rep.Hom.hom S.f x) := by
    intro ψ x
    exact hG (ψ : homCoind L M K S.X₂) x
  haveI hsub : Subsingleton (@Work.AbsoluteKummer.H1 (M ≃ₐ[L] M)
      (homCoind L M K (Rep.free Coeff (K ≃ₐ[L] K) ↥s)) _ _
      (homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[L] K) ↥s))
      (homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[L] K) ↥s))) :=
    homCoind_H1_free_conj_v2 (k := L) (Ω := M) (K := K) (ι := ↥s)
  obtain ⟨δ, hδsurj, hδker⟩ :=
    homCoind_H0_restrict_ker_conj (k := L) (Ω := M) (K := K) (ι := ↥s) pic hfsurj g hg
  -- ===== the two `H⁰`'s are the same =====
  obtain ⟨ΦR, hΦR⟩ := homRep_unitsK_formula (k := L) (Ω := M) (K := K) S.X₁
  obtain ⟨ΦF, hΦF⟩ := homRep_unitsK_formula (k := L) (Ω := M) (K := K) S.X₂
  have hnat := homRep_unitsK_formula_natural (k := L) (Ω := M) (K := K) S.f ΦR ΦF hΦR hΦF g hg
  let ΨR : Abelian.Ext S.X₁ (unitsK L K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (Abelian.Ext.addEquiv₀).trans ΦR
  let ΨF : Abelian.Ext S.X₂ (unitsK L K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) :=
    (Abelian.Ext.addEquiv₀).trans ΦF
  have hpre1 : ∀ f : S.X₂ ⟶ unitsK L K,
      pre (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f) := by
    intro f
    change (Abelian.Ext.mk₀ S.f).precomp (unitsK L K) (by norm_num : 0 + 0 = 0)
        (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f)
    rw [ext_precomp_mk₀]
  have hΨR : ∀ f : S.X₁ ⟶ unitsK L K, ΨR (Abelian.Ext.mk₀ f) = ΦR f := by
    intro f
    show ΦR (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦR f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hΨF : ∀ f : S.X₂ ⟶ unitsK L K, ΨF (Abelian.Ext.mk₀ f) = ΦF f := by
    intro f
    show ΦF (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦF f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hpre : ∀ x : Abelian.Ext S.X₂ (unitsK L K) 0, ΨR (pre x) = g (ΨF x) := by
    intro x
    rw [show x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) from
      (Abelian.Ext.mk₀_addEquiv₀_apply x).symm]
    rw [hpre1 (Abelian.Ext.addEquiv₀ x), hΨR (S.f ≫ Abelian.Ext.addEquiv₀ x),
      hΨF (Abelian.Ext.addEquiv₀ x)]
    exact hnat (Abelian.Ext.addEquiv₀ x)
  have hmap : AddSubgroup.map ΨR.toAddMonoidHom ΦE.ker = δ.ker := by
    rw [hΦEker, hδker]
    have h1 : AddSubgroup.map ΨR.toAddMonoidHom pre.range =
        (ΨR.toAddMonoidHom.comp pre).range := by
      rw [AddMonoidHom.range_eq_map pre, AddSubgroup.map_map,
        ← AddMonoidHom.range_eq_map (ΨR.toAddMonoidHom.comp pre)]
    rw [h1]
    have h2 : ΨR.toAddMonoidHom.comp pre = g.comp ΨF.toAddMonoidHom := by
      apply AddMonoidHom.ext
      intro y
      exact hpre y
    rw [h2, AddMonoidHom.range_eq_map (g.comp ΨF.toAddMonoidHom), ← AddSubgroup.map_map,
      ← AddMonoidHom.range_eq_map ΨF.toAddMonoidHom,
      (AddMonoidHom.range_eq_top).mpr ΨF.surjective]
    exact (AddMonoidHom.range_eq_map g).symm
  -- ===== collecting the isomorphism =====
  let e1 : Abelian.Ext S.X₁ (unitsK L K) 0 ⧸ ΦE.ker ≃+ Abelian.Ext X (unitsK L K) 1 :=
    QuotientAddGroup.quotientKerEquivOfSurjective ΦE hΦEsurj
  let e2 : Abelian.Ext S.X₁ (unitsK L K) 0 ⧸ ΦE.ker ≃+
      ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker :=
    QuotientAddGroup.congr _ _ ΨR hmap
  let e3 : ↥(@Work.AbsoluteKummer.H0 (M ≃ₐ[L] M) (homCoind L M K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker ≃+
      @Work.AbsoluteKummer.H1 (M ≃ₐ[L] M) (homCoind L M K X) _ _
          (homCoind.instAddCommGroup X) (homCoind.instDistribMulActionAlgEquiv X) :=
    QuotientAddGroup.quotientKerEquivOfSurjective δ hδsurj
  exact ⟨e1.symm.trans (e2.trans e3)⟩

/-- **The continuous descent for a finitely generated module `X`.**

`L` of characteristic `0`, `M` an algebraic closure of `L`, `K ⊆ M` a finite Galois intermediate
field, `Q = Gal(K/L)`, `G = Gal(M/L)`.  For `X : Rep Coeff Q` whose underlying abelian group is
finitely generated (`Module.Finite (ULift ℤ) X.V`),

  `Ext¹_{ℤ[Q]}(X, Kˣ) ≅ H¹_cont(G, Hom_ℤ(infl X, Mˣ))`.

Route: `X` is finitely generated over `ℤ`, hence over `ℤ[Q]`, so take a presentation
`0 → R → F → X → 0` with `F = Rep.free Coeff Q ι` free of *finite* rank.
* *Ext side*: the contravariant long exact sequence gives
  `Ext¹_Q(X, Kˣ) ≅ Hom_Q(R, Kˣ)/im(Hom_Q(F, Kˣ))`.
* *continuous side*: `Mˣ` is divisible (`M` algebraically closed, characteristic `0`), so
  `Hom_ℤ(·, Mˣ)` is exact and `0 → A_X → A_F → A_R → 0` is short exact, with
  `A_N = SSGDescent.ssgHom L M K N`; `H¹_cont(G, A_F) = 0` for `F` free of finite rank; the
  connecting map is available because all three coefficient modules are discrete, giving
  `H¹_cont(G, A_X) ≅ coker(H⁰(G,A_F) → H⁰(G,A_R))`.
* The two cokernels agree by the identification `H⁰(G, A_N) ≅ Hom_Q(N, Kˣ)`. -/
theorem ext_continuous_descent_fg {L M : Type} [Field L] [CharZero L] [Field M] [Algebra L M]
    [IsAlgClosure L M] (K : IntermediateField L M) [FiniteDimensional L K] [IsGalois L K]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[L] K)) [Module.Finite (ULift ℤ) X.V] :
    Nonempty (CategoryTheory.Abelian.Ext X
        (Work.SSGRoute.SSGDescent.ssgCoeffK L M K) 1 ≃+
      Work.AbsoluteKummer.H1 (M ≃ₐ[L] M) (Work.SSGRoute.SSGDescent.ssgHom L M K X)) := by
  obtain ⟨e⟩ := ext_continuous_descent_fg_homCoind (L := L) (M := M) K X
  obtain ⟨e2⟩ :=
    h1_equiv_of_equiv (G := M ≃ₐ[L] M) (ssgHomEquiv L M K X).symm
      (fun σ f => ssgHomEquiv_symm_equivariant L M K X σ f)
  exact ⟨e.trans e2⟩

section Probe

example {L M : Type} [Field L] [CharZero L] [Field M] [Algebra L M] [IsAlgClosure L M]
    (K : IntermediateField L M) [FiniteDimensional L K] [IsGalois L K]
    (X : Rep.{0} Coeff (K ≃ₐ[L] K)) :
    (inferInstanceAs (DistribMulAction (M ≃ₐ[L] M) (SSGDescent.ssgHom L M K X)))
      = homRepDistribMulAction (Rep.res (SSGDescent.ssgResHom L M K) X)
          (SSGDescent.ssgCoeffM L M) := rfl

example {L M : Type} [Field L] [CharZero L] [Field M] [Algebra L M] [IsAlgClosure L M]
    (K : IntermediateField L M) [FiniteDimensional L K] [IsGalois L K]
    (X : Rep.{0} Coeff (K ≃ₐ[L] K)) :
    (inferInstanceAs (SMul (M ≃ₐ[L] M) (SSGDescent.ssgHom L M K X)))
      = homRepSMul (Rep.res (SSGDescent.ssgResHom L M K) X) (SSGDescent.ssgCoeffM L M) := rfl

example {L M : Type} [Field L] [Field M] [Algebra L M]
    (K : IntermediateField L M) [Normal L ↥K] (N : Rep.{0} Coeff (K ≃ₐ[L] K))
    (σ : M ≃ₐ[L] M) (φ : Work.SSGRoute.homCoind L M K N) (x : N.V) :
    (σ • φ) x = σ • φ ((N.ρ ((SSGDescent.ssgResHom L M K) σ)⁻¹) x) := rfl

end Probe

end Work.SSGRoute
