import Mathlib
import Submission.Work.SSGRoute.homCoindDefs
import Submission.Work.SSGRoute.addUnits_injective
import Submission.Work.SSGRoute.isDiscreteModule_homCoind
import Submission.Work.SSGRoute.isDiscreteModule_of_injective_addHom
import Submission.Work.SSGRoute.ker_hom_eq_range_kernel_iota
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact

open CategoryTheory

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

/-!
# The connecting map `H⁰(Gal(Ω/k), homCoind K Ker) → H¹(Gal(Ω/k), homCoind K M)`

Let `f : Rep.free Coeff Gal(K/k) ι ⟶ M` be a surjection of `Gal(K/k)`-modules and let `Ker` be its
categorical kernel, so that `0 → Ker → F → M → 0` is a short exact sequence in `Rep`.  Applying
`Hom_ℤ(-, Ωˣ)` — exact, because the units of the algebraically closed field `Ω` form a divisible
group — gives the short exact sequence of `Gal(Ω/k)`-modules

`0 → homCoind K M →^{ι} homCoind K F →^{π} homCoind K Ker → 0`,

where `ι` is precomposition with `f` and `π` is precomposition with the kernel inclusion.

The main theorem below produces the connecting map `δ : H⁰(homCoind K Ker) → H¹(homCoind K M)` of
the associated long exact sequence in continuous cohomology: it is surjective — because
`H¹(homCoind K F) = 0` by Shapiro + Hilbert 90 — and its kernel is the image of
`H⁰(π) : H⁰(homCoind K F) → H⁰(homCoind K Ker)`, which is the map `g` of the statement.
-/

/-! ## Precomposition on additive homomorphisms -/

/-- Precomposition `ψ ↦ ψ ∘ F` with an additive homomorphism `F : A →+ B`. -/
def precompAddHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (F : A →+ B) : (B →+ C) →+ (A →+ C) where
  toFun ψ := ψ.comp F
  map_zero' := by ext x; simp
  map_add' ψ ψ' := by ext x; simp [AddMonoidHom.add_comp]

@[simp] theorem precompAddHom_apply {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (F : A →+ B) (ψ : B →+ C) : precompAddHom F ψ = ψ.comp F := rfl

theorem precompAddHom_injective {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (F : A →+ B) (hF : Function.Surjective F) :
    Function.Injective (precompAddHom F : (B →+ C) →+ (A →+ C)) := by
  intro ψ ψ' h
  ext b
  obtain ⟨a, rfl⟩ := hF b
  exact congrArg (fun w : A →+ C => w a) h

/-- **Surjectivity of precomposition with an injective map into the units of `Ω`.**  `Ωˣ` is
divisible for algebraically closed `Ω`, hence injective in abelian groups, so every
`A →+ Ωˣ` extends along an injection `A ↪ B`. -/
theorem precompAddHom_surjective_addUnits {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {A B : Type} [AddCommGroup A] [AddCommGroup B] (F : A →+ B) (hF : Function.Injective F) :
    Function.Surjective (precompAddHom F : (B →+ Additive Ωˣ) →+ (A →+ Additive Ωˣ)) := by
  intro ψ
  obtain ⟨h, hh⟩ := addUnits_injective F hF ψ
  exact ⟨h, AddMonoidHom.ext hh⟩

/-- Transport of discreteness along a surjective equivariant additive map (the action on the
source being discrete). -/
theorem isDiscreteModule_of_surjective_addHom_aux {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N]
    (e : M →+ N) (he : Function.Surjective e)
    (heq : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (hM : Work.AbsoluteKummer.IsDiscreteModule G M) :
    Work.AbsoluteKummer.IsDiscreteModule G N := by
  intro n
  obtain ⟨m, rfl⟩ := he n
  have hsub : (MulAction.stabilizer G m : Set G) ⊆ MulAction.stabilizer G (e m) := by
    intro g hg
    rw [SetLike.mem_coe] at hg ⊢
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← heq g m, hg]
  have hmem : (MulAction.stabilizer G (e m) : Set G) ∈ nhds (1 : G) :=
    Filter.mem_of_superset ((hM m).mem_nhds (MulAction.mem_stabilizer_iff.mpr (one_smul G m))) hsub
  exact Subgroup.isOpen_of_mem_nhds _ hmem

/-! ## The main theorem -/

theorem homCoind_H0_restrict_ker_conj {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {ι : Type} [Finite ι] {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (f : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι ⟶ M) (hf : Function.Surjective (Rep.Hom.hom f)) [Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) _ _ (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)))] (g : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) _ (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))) →+ ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel f)) _ (Work.SSGRoute.homCoind.instAddCommGroup (CategoryTheory.Limits.kernel f)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (CategoryTheory.Limits.kernel f)))) (hg : ∀ (φ : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) _ (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)))) (x : (CategoryTheory.Limits.kernel f).V), Subtype.val (g φ) x = Subtype.val φ (CategoryTheory.Limits.kernel.ι f x)) : ∃ δ : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel f)) _ (Work.SSGRoute.homCoind.instAddCommGroup (CategoryTheory.Limits.kernel f)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (CategoryTheory.Limits.kernel f))) →+ @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K M) _ _ (Work.SSGRoute.homCoind.instAddCommGroup M) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv M), Function.Surjective δ ∧ AddMonoidHom.ker δ = AddMonoidHom.range g := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  let Free := Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι
  let Ker := CategoryTheory.Limits.kernel f
  -- Pin the coefficient structures to the instances named in the statement, so that all the
  -- intermediate types below are the ones occurring in the hypotheses and the conclusion.
  letI hACM : AddCommGroup (homCoind k Ω K M) := homCoind.instAddCommGroup M
  letI hDAM : DistribMulAction (Ω ≃ₐ[k] Ω) (homCoind k Ω K M) :=
    homCoind.instDistribMulActionAlgEquiv M
  letI hACF : AddCommGroup (homCoind k Ω K Free) := homCoind.instAddCommGroup Free
  letI hDAF : DistribMulAction (Ω ≃ₐ[k] Ω) (homCoind k Ω K Free) :=
    homCoind.instDistribMulActionAlgEquiv Free
  letI hACK : AddCommGroup (homCoind k Ω K Ker) := homCoind.instAddCommGroup Ker
  letI hDAK : DistribMulAction (Ω ≃ₐ[k] Ω) (homCoind k Ω K Ker) :=
    homCoind.instDistribMulActionAlgEquiv Ker
  haveI hsubB : Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (homCoind k Ω K Free) _ _
      (homCoind.instAddCommGroup Free)
      (homCoind.instDistribMulActionAlgEquiv Free)) := ‹_›
  -- the underlying additive maps of `f` and of the kernel inclusion
  let F : Free.V →+ M.V := (Rep.Hom.hom f).toAddMonoidHom
  let kι : Ker.V →+ Free.V := (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι f)).toAddMonoidHom
  have hF : Function.Surjective F := fun x => hf x
  have hFcomm : ∀ (γ : K ≃ₐ[k] K) (v : Free.V), F (Free.ρ γ v) = M.ρ γ (F v) :=
    fun γ v => Rep.hom_comm_apply f γ v
  have hkι : Function.Injective kι := by
    haveI : CategoryTheory.Mono (CategoryTheory.Limits.kernel.ι f) := inferInstance
    simpa [kι] using
      (Rep.mono_iff_injective (CategoryTheory.Limits.kernel.ι f)).mp inferInstance
  have hkιcomm : ∀ (γ : K ≃ₐ[k] K) (v : Ker.V), kι (Ker.ρ γ v) = Free.ρ γ (kι v) :=
    fun γ v => Rep.hom_comm_apply (CategoryTheory.Limits.kernel.ι f) γ v
  have hFkι : ∀ v : Ker.V, F (kι v) = 0 := by
    intro v
    have hcond : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.kernel.ι f) f = 0 :=
      CategoryTheory.Limits.kernel.condition f
    have h := congrArg (fun (m : Ker ⟶ M) => m v) hcond
    rw [Rep.comp_apply] at h
    simpa [F, kι] using h
  -- equivariance of precomposition with `f` and with the kernel inclusion
  have hiota_eq : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (precompAddHom F : homCoind k Ω K M →+ homCoind k Ω K Free) := by
    intro σ ψ
    apply AddMonoidHom.ext
    intro v
    rw [precompAddHom_apply, AddMonoidHom.comp_apply]
    simp only [homCoind.smul_apply]
    rw [precompAddHom_apply, AddMonoidHom.comp_apply]
    congr 1
    exact congrArg ψ (hFcomm ((SSGRoute.res k K) σ)⁻¹ v).symm
  have hpi_eq : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (precompAddHom kι : homCoind k Ω K Free →+ homCoind k Ω K Ker) := by
    intro σ ψ
    apply AddMonoidHom.ext
    intro v
    rw [precompAddHom_apply, AddMonoidHom.comp_apply]
    simp only [homCoind.smul_apply]
    rw [precompAddHom_apply, AddMonoidHom.comp_apply]
    congr 1
    exact congrArg ψ (hkιcomm ((SSGRoute.res k K) σ)⁻¹ v).symm
  have hiota_inj : Function.Injective
      (precompAddHom F : homCoind k Ω K M →+ homCoind k Ω K Free) :=
    precompAddHom_injective F hF
  have hpi_surj : Function.Surjective
      (precompAddHom kι : homCoind k Ω K Free →+ homCoind k Ω K Ker) :=
    precompAddHom_surjective_addUnits kι hkι
  -- exactness in the middle
  have hkerF : F.ker = kι.range := by
    simpa [F, kι] using ker_hom_eq_range_kernel_iota (K := K) f
  have hrange : (precompAddHom F : homCoind k Ω K M →+ homCoind k Ω K Free).range
      = (precompAddHom kι : homCoind k Ω K Free →+ homCoind k Ω K Ker).ker := by
    apply le_antisymm
    · rintro _ ⟨ψ, rfl⟩
      rw [AddMonoidHom.mem_ker]
      apply AddMonoidHom.ext
      intro v
      show ψ (F (kι v)) = 0
      rw [hFkι v]
      exact map_zero ψ
    · intro ψ hψ
      rw [AddMonoidHom.mem_ker] at hψ
      have hψv : ∀ v : Ker.V, ψ (kι v) = 0 := by
        intro v
        have h := congrArg (fun (w : Ker.V →+ Additive Ωˣ) => w v) hψ
        simpa [precompAddHom_apply, AddMonoidHom.comp_apply] using h
      have hle : F.ker ≤ ψ.ker := by
        rw [hkerF]
        intro x hx
        rw [AddMonoidHom.mem_ker]
        obtain ⟨v, rfl⟩ := hx
        exact hψv v
      let φ : M.V →+ Additive Ωˣ := (AddMonoidHom.liftOfSurjective F hF) ⟨ψ, hle⟩
      have hφ : ∀ x, φ (F x) = ψ x := fun x =>
        AddMonoidHom.liftOfRightInverse_comp_apply F (Function.surjInv hF)
          (Function.rightInverse_surjInv hF) ⟨ψ, hle⟩ x
      refine AddMonoidHom.mem_range.mpr ⟨φ, ?_⟩
      apply AddMonoidHom.ext
      intro x
      show φ (F x) = ψ x
      exact hφ x
  -- discreteness of the three coefficient modules
  have hdisF : Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (homCoind k Ω K Free) :=
    isDiscreteModule_homCoind (K := K) Free
  have hdisM : Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (homCoind k Ω K M) :=
    isDiscreteModule_of_injective_addHom (precompAddHom F) hiota_inj hiota_eq hdisF
  have hdisK : Work.AbsoluteKummer.IsDiscreteModule (Ω ≃ₐ[k] Ω) (homCoind k Ω K Ker) :=
    isDiscreteModule_of_surjective_addHom_aux (precompAddHom kι) hpi_surj hpi_eq hdisF
  -- the short exact sequence of coefficient modules
  let S : Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
      (homCoind k Ω K M) (homCoind k Ω K Free) (homCoind k Ω K Ker) :=
    { iota := precompAddHom F
      pi := precompAddHom kι
      iota_equivariant := hiota_eq
      pi_equivariant := hpi_eq
      iota_injective := hiota_inj
      pi_surjective := hpi_surj
      range_iota_eq_ker_pi := hrange
      isDiscreteM := hdisM
      isDiscreteN := hdisF
      isDiscreteP := hdisK }
  -- the hypothesis `g` is `H⁰` of the projection `π = S.pi`
  have hg_eq : g = Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω) S.pi S.pi_equivariant := by
    refine AddMonoidHom.ext fun φ => Subtype.ext ?_
    refine AddMonoidHom.ext fun x => ?_
    show Subtype.val (g φ) x
      = Subtype.val (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω) S.pi S.pi_equivariant φ) x
    rw [hg φ x]
    show Subtype.val φ ((CategoryTheory.Limits.kernel.ι f) x)
      = (precompAddHom kι (Subtype.val φ)) x
    rw [precompAddHom_apply, AddMonoidHom.comp_apply]
    rfl
  -- the connecting map of the long exact sequence
  obtain ⟨δ, hker, hrange'⟩ := Work.AbsoluteKummer.SES.exists_connecting_exact S
  have htop : δ.range = ⊤ := by
    rw [hrange', eq_top_iff]
    intro y _
    rw [AddMonoidHom.mem_ker]
    exact Subsingleton.elim _ 0
  exact ⟨δ, AddMonoidHom.range_eq_top.mp htop, by rw [← hker, hg_eq]⟩

end

end Work.SSGRoute
