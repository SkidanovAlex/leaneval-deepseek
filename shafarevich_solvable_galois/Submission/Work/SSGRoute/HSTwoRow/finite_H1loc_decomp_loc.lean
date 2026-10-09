import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.HSRestrict
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HS.Basic
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.map_topologicalClosure_zpowers_subtype
import Submission.Work.SSGRoute.PT.Helpers
import Submission.Work.SSGRoute.HSTwoRow.exists_kills_I_representative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of `H¹_loc(D_A,M)` for a decomposition group

The local `H¹` of a decomposition group `D = decomp k A = I ⋊ C` (`C = closure (zpowers σ)`) is
finite whenever the local `H¹` of the closed subgroup `I` is, for coefficients in a finite
`𝔽_p[Gal(K/k)]`-module `M`.

The proof is the elementary half of the Hochschild–Serre exact sequence in the form needed for
finiteness: the restriction `res1 : H¹(D,M) → H¹(I,M)` has finite image (it lands in
`ker (conj₁ - 1) ⊆ H¹(I,M)`, which is finite by hypothesis), and its kernel is finite by an
explicit injection

  `ker (res1) → M^I ⧸ (σ - 1) M^I`,

which is finite because `M` is.  Concretely, an element of `ker (res1)` has a locally constant
cocycle representative `g` on `D` which is *zero on `I`*; such a representative takes the value
`g σ ∈ M^I`, and `g` is a coboundary as soon as `g σ ∈ (σ-1)M^I` — because then `g - δμ` is a
locally constant cocycle on `D` vanishing on `I` and at `σ`; its restriction to
`C = closure (zpowers σ)` is a locally constant cocycle on `C` vanishing at the topological
generator `σ`, hence vanishes on `C` and therefore on `D ≤ I ⊔ C`.
-/

open scoped Pointwise
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.HSTwoRow

noncomputable section

/-! ## Elementary lemmas about locally constant `1`-cocycles -/

/-- Fixing `m : M`, the function `γ ↦ res γ • m - m` is a `1`-coboundary, hence a locally constant
`1`-cocycle on every subgroup; subtracting it from a locally constant cocycle therefore keeps one
inside the locally constant cocycles. -/
lemma lcCocycles_sub_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (m : M) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M H) :
    (fun γ : Ω ≃ₐ[k] Ω => f γ - (SSGRoute.res k K γ • m - m)) ∈
      Work.SSGRoute.lcCocycles p k Ω K M H := by
  have hcob : (fun γ : Ω ≃ₐ[k] Ω => SSGRoute.res k K γ • m - m) ∈
      Work.SSGRoute.coboundaries p k Ω K M H := ⟨m, fun g _ => rfl⟩
  exact sub_mem hf (Work.SSGRoute.coboundaries_le_lcCocycles p k Ω K M H hcob)

/-- `toClass` is insensitive to subtracting a coboundary. -/
lemma toClass_eq_of_sub_mem_coboundaries
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M H)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M H)
    (hsub : f - g ∈ Work.SSGRoute.coboundaries p k Ω K M H) :
    Work.SSGRoute.toClass p k Ω K M H f = Work.SSGRoute.toClass p k Ω K M H g := by
  rw [Work.SSGRoute.toClass, dif_pos hf, Work.SSGRoute.toClass, dif_pos hg,
    Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).mpr (by
    rw [Submodule.mem_comap]
    simpa using hsub)

/-- A locally constant `1`-cocycle on `D = decomp k A` which vanishes on `I` takes the value
`g σ` in `M^I = H⁰(I,M)`. -/
lemma mem_H0loc_of_kills_I
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A) (hσ : σ ∈ SSGRoute.decomp k A)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (g : (Ω ≃ₐ[k] Ω) → M)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A))
    (hkill : ∀ n ∈ I, g n = 0) :
    g σ ∈ Work.SSGRoute.H0loc p k Ω K M I := by
  intro n hn
  have hA : g (n * σ) = SSGRoute.res k K n • g σ := by
    rw [hg.1 n (hI hn) σ hσ, hkill n hn, zero_add]
  have hB : g (n * σ) = g σ := by
    rw [show n * σ = σ * (σ⁻¹ * n * σ) from by group,
      hg.1 σ hσ (σ⁻¹ * n * σ) (hI (hnorm2 n hn)),
      hkill (σ⁻¹ * n * σ) (hnorm2 n hn), smul_zero, add_zero]
  exact hA.symm.trans hB

/-! ## The two ingredients of the kernel computation -/

/-- **The kernel of `res1` computed at the generator.**  If `g` is a locally constant `1`-cocycle on
`D = decomp k A` which vanishes on `I` and whose value at `σ` is the coboundary of an element
`μ ∈ M^I`, then `g` is itself a coboundary on `D`. -/
lemma coboundary_of_kills_I_gen_mem_range_aux
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A) (hσ : σ ∈ SSGRoute.decomp k A)
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (g : (Ω ≃ₐ[k] Ω) → M)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A))
    (hkill : ∀ n ∈ I, g n = 0)
    (hgen : ∃ μ : M, (∀ n ∈ I, SSGRoute.res k K n • μ = μ) ∧
      SSGRoute.res k K σ • μ - μ = g σ) :
    g ∈ Work.SSGRoute.coboundaries p k Ω K M (SSGRoute.decomp k A) := by
  classical
  obtain ⟨μ, hμI, hμσ⟩ := hgen
  set h : (Ω ≃ₐ[k] Ω) → M := fun γ => g γ - (SSGRoute.res k K γ • μ - μ) with hh
  have hhmem : h ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    lcCocycles_sub_coboundary p k Ω K M (SSGRoute.decomp k A) μ hg
  have hkillh : ∀ n ∈ I, h n = 0 := by
    intro n hn
    rw [show h n = g n - (SSGRoute.res k K n • μ - μ) from rfl, hkill n hn, hμI n hn]
    simp
  have hσh : h σ = 0 := by
    rw [show h σ = g σ - (SSGRoute.res k K σ • μ - μ) from rfl, hμσ]
    simp
  have hC : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
    HS.CC_le_DD A σ hσ
  have hCzero : ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ), h γ = 0 :=
    Work.SSGRoute.PT.lcCocycleOn_zpowers_eq_zero_of_gen_eq_zero p k Ω K M σ h
      (fun x hx y hy => hhmem.1 x (hC hx) y (hC hy))
      (by
        obtain ⟨U, hUo, hU⟩ := hhmem.2
        exact ⟨U, hUo, fun x hx u hu huC => hU x (hC hx) u hu (hC huC)⟩)
      hσh
  have hDzero : ∀ d ∈ SSGRoute.decomp k A, h d = 0 := by
    intro d hd
    obtain ⟨i, hi, γ, hγ, hprod⟩ := HS.exists_factor A I σ hI hnorm hC hsup hd
    rw [← hprod, hhmem.1 i (hI hi) γ (hC hγ), hkillh i hi, hCzero γ hγ, smul_zero, add_zero]
  refine ⟨μ, fun d hd => ?_⟩
  have hz := hDzero d hd
  rw [show h d = g d - (SSGRoute.res k K d • μ - μ) from rfl] at hz
  exact sub_eq_zero.mp hz

end

/-! ## The main theorem -/

theorem finite_H1loc_decomp_loc
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A) (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (hfin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) := by
  classical
  haveI hFinI : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I) := hfin M
  haveI hFinIt : Finite (Work.SSGRoute.H1loc p k Ω K M I) := Module.finite_of_finite (ZMod p)
  -- representatives killed on `I` for the elements of `ker (res1)`
  have key : ∀ x : ↥(LinearMap.ker (res1 p k Ω K M I A hI)),
      ∃ f : (Ω ≃ₐ[k] Ω) → M,
        f ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A) ∧
        Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) f = x.1 ∧
        ∀ n ∈ I, f n = 0 :=
    fun x => exists_kills_I_representative p k Ω K A I hI M x.1 x.2
  choose F hFmem hFeq hFkill using key
  -- the finite target `M^I ⧸ (σ - 1)M^I`
  haveI hFinN : Finite ↥(Work.SSGRoute.H0loc p k Ω K M I) :=
    Finite.of_injective
      (Subtype.val : ↥(Work.SSGRoute.H0loc p k Ω K M I) → M) Subtype.val_injective
  haveI hFinQ : Finite (↥(Work.SSGRoute.H0loc p k Ω K M I) ⧸
      LinearMap.range (conj0 p k Ω K M I σ hnorm2 - LinearMap.id)) :=
    Finite.of_surjective
      (Submodule.mkQ (LinearMap.range (conj0 p k Ω K M I σ hnorm2 - LinearMap.id)))
      (Submodule.mkQ_surjective _)
  -- `ker (res1)` injects into it
  have hFinKer : Finite ↥(LinearMap.ker (res1 p k Ω K M I A hI)) := by
    refine Finite.of_injective
      (fun x : ↥(LinearMap.ker (res1 p k Ω K M I A hI)) =>
        (Submodule.Quotient.mk (p := LinearMap.range
            (conj0 p k Ω K M I σ hnorm2 - LinearMap.id))
          ⟨F x σ, mem_H0loc_of_kills_I p k Ω K M A I σ hI hσ hnorm2 (F x) (hFmem x)
            (hFkill x)⟩ :
          ↥(Work.SSGRoute.H0loc p k Ω K M I) ⧸
            LinearMap.range (conj0 p k Ω K M I σ hnorm2 - LinearMap.id))) ?_
    intro x y hxy
    have hsub : (⟨F x σ, mem_H0loc_of_kills_I p k Ω K M A I σ hI hσ hnorm2 (F x) (hFmem x)
            (hFkill x)⟩ : ↥(Work.SSGRoute.H0loc p k Ω K M I)) -
          ⟨F y σ, mem_H0loc_of_kills_I p k Ω K M A I σ hI hσ hnorm2 (F y) (hFmem y)
            (hFkill y)⟩ ∈
          LinearMap.range (conj0 p k Ω K M I σ hnorm2 - LinearMap.id) :=
      (Submodule.Quotient.eq _).mp hxy
    obtain ⟨μ, hμ⟩ := LinearMap.mem_range.mp hsub
    have hμM : SSGRoute.res k K σ • (μ : M) - (μ : M) = (F x - F y) σ := by
      have h1 := congrArg (fun z : ↥(Work.SSGRoute.H0loc p k Ω K M I) => (z : M)) hμ
      rw [LinearMap.sub_apply, LinearMap.id_apply, Submodule.coe_sub] at h1
      rw [conj0_coe] at h1
      rw [Pi.sub_apply]
      simpa using h1
    have hh : F x - F y ∈ Work.SSGRoute.coboundaries p k Ω K M (SSGRoute.decomp k A) :=
      coboundary_of_kills_I_gen_mem_range_aux p k Ω K A I σ hI hσ hnorm hsup M (F x - F y)
        (sub_mem (hFmem x) (hFmem y))
        (fun n hn => by rw [Pi.sub_apply, hFkill x n hn, hFkill y n hn, sub_self])
        ⟨(μ : M), μ.2, hμM⟩
    have hclass : Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) (F x) =
        Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) (F y) :=
      toClass_eq_of_sub_mem_coboundaries p k Ω K M (SSGRoute.decomp k A) (hFmem x) (hFmem y) hh
    refine Subtype.ext ?_
    rw [← hFeq x, ← hFeq y]
    exact hclass
  -- finally `H¹_loc(D,M)` is finite: it is an extension of the finite `ker (res1)` by a submodule
  -- of the finite `H¹_loc(I,M)`
  have hExt : Finite (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) := by
    haveI : Finite ↥(LinearMap.range (res1 p k Ω K M I A hI)) :=
      Finite.of_injective
        (Subtype.val : ↥(LinearMap.range (res1 p k Ω K M I A hI)) →
          Work.SSGRoute.H1loc p k Ω K M I) Subtype.val_injective
    let s : Work.SSGRoute.H1loc p k Ω K M I →
        Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A) :=
      fun y => if h : ∃ x, res1 p k Ω K M I A hI x = y then Classical.choose h else 0
    have hs : ∀ y (h : ∃ x, res1 p k Ω K M I A hI x = y),
        res1 p k Ω K M I A hI (s y) = y := by
      intro y h
      show res1 p k Ω K M I A hI
        (if h' : ∃ x, res1 p k Ω K M I A hI x = y then Classical.choose h' else 0) = y
      rw [dif_pos h]
      exact Classical.choose_spec h
    let ι : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A) →
        ↥(LinearMap.ker (res1 p k Ω K M I A hI)) × Work.SSGRoute.H1loc p k Ω K M I :=
      fun x => (⟨x - s (res1 p k Ω K M I A hI x), by
          rw [LinearMap.mem_ker, map_sub, hs (res1 p k Ω K M I A hI x) ⟨x, rfl⟩, sub_self]⟩,
        res1 p k Ω K M I A hI x)
    refine Finite.of_injective ι ?_
    intro x y hxy
    have h1 : res1 p k Ω K M I A hI x = res1 p k Ω K M I A hI y := congrArg Prod.snd hxy
    have h2 : (⟨x - s (res1 p k Ω K M I A hI x), _⟩ :
        ↥(LinearMap.ker (res1 p k Ω K M I A hI))) =
        ⟨y - s (res1 p k Ω K M I A hI y), _⟩ := congrArg Prod.fst hxy
    have h3 : x - s (res1 p k Ω K M I A hI x) = y - s (res1 p k Ω K M I A hI y) := by
      simpa using congrArg (fun z : ↥(LinearMap.ker (res1 p k Ω K M I A hI)) =>
        (z : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A))) h2
    rw [h1] at h3
    have h4 := congrArg (fun z => z + s (res1 p k Ω K M I A hI y)) h3
    simpa [sub_add_cancel] using h4
  haveI := hExt
  exact Module.Finite.of_finite

end Work.SSGRoute.HSTwoRow
