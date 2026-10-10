import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.homCoind_H0_restrict_ker_conj

open CategoryTheory

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

noncomputable section

/-! ## Forcing the conjugation action on `homCoind`

`homCoind k Ω K M` is an abbreviation for `M.V →+ Additive Ωˣ`, so type class search sometimes
finds the *pointwise* `DistribMulAction` on `AddMonoidHom` (`(σ • φ) x = σ • φ x`) rather than the
conjugation action `(σ • φ) x = σ • φ (σ⁻¹ • x)` defined in `homCoindDefs`.  Every lemma of the
`homCoind` chapter — and the statement of `homCoind_SES` below, whose middle coefficient is
`homCoind k Ω K (Rep.free Coeff Gal(K/k) ι)` — is meant for the conjugation action; the same device
is used in `Submission/Work/SSGRoute/ext_h1_bridge.lean`.

The two actions are *not* definitionally equal (the conjugation action inserts
`(M.ρ (res σ))⁻¹`), so without the local instance below the statement of `homCoind_SES` would be
instantiated with the pointwise action on the middle coefficient, and would then be **false**: the
required equivariance of `precompAddHom F` would force `ψ (F ((res σ)⁻¹ • v)) = ψ (F v)` for *every*
additive `ψ : M.V →+ Ωˣ`, hence triviality of `σ` on the image of `F`.  Concretely take
`M = Rep.free Coeff Gal(K/k) ι`, `f = 𝟙`, `K/k` a nontrivial finite Galois extension, `ι` nonempty,
`σ` with nontrivial restriction to `K` and a `ℤ`-linear functional on the free `ℤ[G]`-module
`Free.V = ι →₀ ℤ[G]` separating the two distinct vectors `v` and `(res σ)⁻¹ • v`: then the
equivariance claim becomes `ψ ((res σ)⁻¹ • v) = ψ v`, a contradiction.

For the concrete argument `Rep.free Coeff Gal(K/k) ι` the conjugation *instance* is, moreover, not
even a candidate for type class search: `Rep.free` is an `abbrev`, so the type-class key of
`Hom_ℤ((Rep.free ⋯).V, Ωˣ)` is no longer of the shape `M.V →+ Ωˣ` (with `M` a metavariable), which
is why the action is pinned here by an explicit local instance — a high-priority
`attribute [local instance 10000]` on the instance itself is not enough for this argument. -/

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {ι : Type} [Finite ι]

/-- The conjugation action of `Γ = Gal(Ω/k)` on `Hom_ℤ((Rep.free Coeff Gal(K/k) ι).V, Ωˣ)`, pinned
so that type class search does not pick the pointwise action on `AddMonoidHom`. -/
abbrev instDistribMulActionHomCoindFree :
    DistribMulAction (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) :=
  Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv _

attribute [local instance 10000] instDistribMulActionHomCoindFree

/-!
# The short exact sequence `0 → homCoind K M → homCoind K F → homCoind K Ker → 0`

Let `f : Rep.free Coeff Gal(K/k) ι ⟶ M` be a surjection of `Gal(K/k)`-modules and let `Ker` be its
categorical kernel.  Applying `Hom_ℤ(-, Ωˣ)` — exact because `Ωˣ` is divisible for algebraically
closed `Ω` — to `0 → Ker → F → M → 0` gives a short exact sequence of `Gal(Ω/k)`-modules

`0 → homCoind K M →^{ι} homCoind K F →^{π} homCoind K Ker → 0`

whose maps are precomposition with `f` and with the kernel inclusion, the action of `Γ = Gal(Ω/k)`
on all three terms being the conjugation action `(σ · φ) x = σ · φ (σ⁻¹ · x)`.  This file
constructs that short exact sequence (`Work.AbsoluteKummer.ShortExactSeq`), keeping its `iota` and
`pi` definitionally the precomposition maps named in the statement.

`homCoind_SES_conj` below is the same statement with the three conjugation actions written out
explicitly; `homCoind_SES` is the requested statement (identical text, the conjugation action on
all three coefficients being pinned by the local instance above).
-/

theorem homCoind_SES_conj {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] {ι : Type} [Finite ι]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (f : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι ⟶ M)
    (hf : Function.Surjective (Rep.Hom.hom f)) :
    ∃ S : @Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω) _ _
        (Work.SSGRoute.homCoind k Ω K M)
        (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel f))
        (Work.SSGRoute.homCoind.instAddCommGroup M)
        (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
        (Work.SSGRoute.homCoind.instAddCommGroup (CategoryTheory.Limits.kernel f))
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv M)
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
          (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (CategoryTheory.Limits.kernel f)),
      S.iota = Work.SSGRoute.precompAddHom (Rep.Hom.hom f).toAddMonoidHom ∧
      S.pi = Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι f)).toAddMonoidHom := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  let Free := Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι
  let Ker := CategoryTheory.Limits.kernel f
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
  refine ⟨{ iota := precompAddHom F
            pi := precompAddHom kι
            iota_equivariant := hiota_eq
            pi_equivariant := hpi_eq
            iota_injective := hiota_inj
            pi_surjective := hpi_surj
            range_iota_eq_ker_pi := hrange
            isDiscreteM := hdisM
            isDiscreteN := hdisF
            isDiscreteP := hdisK }, rfl, rfl⟩

theorem homCoind_SES {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] {ι : Type} [Finite ι]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (f : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι ⟶ M)
    (hf : Function.Surjective (Rep.Hom.hom f)) :
    ∃ S : Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K M)
        (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel f)),
      S.iota = Work.SSGRoute.precompAddHom (Rep.Hom.hom f).toAddMonoidHom ∧
      S.pi = Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι f)).toAddMonoidHom :=
  homCoind_SES_conj f hf

end

end Work.SSGRoute.PT
