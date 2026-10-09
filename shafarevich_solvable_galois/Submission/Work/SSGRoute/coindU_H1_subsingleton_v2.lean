import Mathlib
import Submission.Work.SSGRoute.coindU_aux
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(Ω/k), Maps(Gal(K/k), Ωˣ))` is trivial (self-contained version)

Let `k` be a field, `Ω` an algebraic closure of `k` and `K/k` a finite Galois subextension.  The
coinduced module `CoindU k Ω K = Maps(Gal(K/k), Ωˣ)` carries the action
`(σ • φ)(x) = σ (φ ((σ|_K)⁻¹ x))`.  We prove that `H¹` of `Gal(Ω/k)` with these coefficients is
trivial.

This is Shapiro's lemma together with Hilbert 90 for the subgroup `Gal(Ω/K) ≤ Gal(Ω/k)`:
restricting a `1`-cocycle `F : Gal(Ω/k) → Maps(Gal(K/k), Ωˣ)` to the fixing subgroup of `K` and
evaluating at `1 ∈ Gal(K/k)` gives a locally constant crossed homomorphism
`Gal(Ω/K) → Ωˣ`, whose triviality (`Work.SSGRoute.exists_div_fixingSubgroup`) produces an element
`b : Ωˣ`.  Choosing a section `Gal(K/k) → Gal(Ω/k)` of the restriction map, the element
`a(x) = x̃ • b - F(x̃)(x)` (with `x̃` any lift of `x`) then satisfies `F σ = σ • a - a` for all `σ`.

The main statement is `Work.SSGRoute.coindU_H1_subsingleton_v2`.
-/

open scoped Classical Topology
open Filter

namespace Work.SSGRoute

/-- **Shapiro's lemma, in explicit form.**  A locally constant `1`-cocycle on `Gal(Ω/k)` with
values in `Maps(Gal(K/k), Ωˣ)` is a coboundary. -/
theorem coindU_coboundary_v2 {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (F : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.CoindU k Ω K)
    (hcross : ∀ σ τ : Ω ≃ₐ[k] Ω, F (σ * τ) = σ • F τ + F σ)
    (hloc : Work.AbsoluteKummer.IsLocallyConstant F) :
    ∃ a : Work.SSGRoute.CoindU k Ω K, ∀ σ, F σ = σ • a - a := by
  have hresker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have hreskermem : ∀ σ : ↥(K.fixingSubgroup), SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = 1 := by
    intro σ
    have h : (σ : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
      rw [hresker]; exact σ.2
    exact h
  have hsurj : Function.Surjective (SSGRoute.res k K) := AlgEquiv.restrictNormalHom_surjective Ω
  let lift : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω) := fun y => Classical.choose (hsurj y)
  have hlift : ∀ y, SSGRoute.res k K (lift y) = y := fun y => Classical.choose_spec (hsurj y)
  let f : ↥(K.fixingSubgroup) → Additive Ωˣ := fun τ => F (τ : Ω ≃ₐ[k] Ω) 1
  have hfcross : ∀ σ τ : ↥(K.fixingSubgroup), f (σ * τ) = σ • f τ + f σ := by
    intro σ τ
    have h1 : (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) = 1 := hreskermem σ
    have h := congrFun (hcross (σ : Ω ≃ₐ[k] Ω) (τ : Ω ≃ₐ[k] Ω)) (1 : K ≃ₐ[k] K)
    have h2 : ((σ : Ω ≃ₐ[k] Ω) • F (τ : Ω ≃ₐ[k] Ω) + F (σ : Ω ≃ₐ[k] Ω)) (1 : K ≃ₐ[k] K)
        = ((σ : Ω ≃ₐ[k] Ω) • F (τ : Ω ≃ₐ[k] Ω)) (1 : K ≃ₐ[k] K)
          + (F (σ : Ω ≃ₐ[k] Ω)) (1 : K ≃ₐ[k] K) := rfl
    rw [h2] at h
    rw [show ((σ : Ω ≃ₐ[k] Ω) • F (τ : Ω ≃ₐ[k] Ω)) (1 : K ≃ₐ[k] K)
        = (σ : Ω ≃ₐ[k] Ω) • ((F (τ : Ω ≃ₐ[k] Ω))
            ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω))⁻¹ * 1)) from rfl,
      h1, inv_one, one_mul] at h
    exact h
  have hfloc : Work.AbsoluteKummer.IsLocallyConstant f :=
    (Work.AbsoluteKummer.IsLocallyConstant.map
      (fun φ : Work.SSGRoute.CoindU k Ω K => φ (1 : K ≃ₐ[k] K)) hloc).comp continuous_subtype_val
  obtain ⟨b, hb⟩ := exists_div_fixingSubgroup (K := K) f hfcross hfloc
  let a : Work.SSGRoute.CoindU k Ω K := fun y => (lift y) • b - F (lift y) y
  have ha : ∀ y, a y = (lift y) • b - F (lift y) y := fun y => rfl
  refine ⟨a, fun σ => ?_⟩
  funext y
  set τ := lift y with hτ
  have hresτ : SSGRoute.res k K τ = y := hlift y
  set x' := (SSGRoute.res k K σ)⁻¹ * y with hx'
  set ρ := lift x' with hρ
  have hresρ : SSGRoute.res k K ρ = x' := hlift x'
  let hh : ↥(K.fixingSubgroup) := ⟨ρ⁻¹ * (σ⁻¹ * τ), by
    rw [← hresker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hresρ, hresτ, hx']
    group⟩
  have hhval : (hh : Ω ≃ₐ[k] Ω) = ρ⁻¹ * (σ⁻¹ * τ) := rfl
  have hdecomp : σ⁻¹ * τ = ρ * (hh : Ω ≃ₐ[k] Ω) := by rw [hhval]; group
  have hfour : (SSGRoute.res k K ρ)⁻¹ * x' = 1 := by rw [hresρ]; group
  have hkey1 : F (ρ * (hh : Ω ≃ₐ[k] Ω)) x' = ρ • f hh + F ρ x' := by
    rw [hcross]
    rw [show (ρ • F (hh : Ω ≃ₐ[k] Ω) + F ρ) x'
        = (ρ • F (hh : Ω ≃ₐ[k] Ω)) x' + F ρ x' from rfl]
    rw [show (ρ • F (hh : Ω ≃ₐ[k] Ω)) x'
        = ρ • (F (hh : Ω ≃ₐ[k] Ω) ((SSGRoute.res k K ρ)⁻¹ * x')) from rfl]
    rw [hfour]
  have hkey2 : ρ • f hh = (σ⁻¹ * τ) • b - ρ • b := by
    rw [hb hh]
    rw [show (hh : ↥(K.fixingSubgroup)) • b = (hh : Ω ≃ₐ[k] Ω) • b from rfl]
    rw [smul_sub, ← mul_smul, ← hdecomp]
  have key : F ρ x' = F (σ⁻¹ * τ) x' + ρ • b - (σ⁻¹ * τ) • b := by
    have h := hkey1
    rw [← hdecomp, hkey2] at h
    rw [h]
    abel
  have hax' : a x' = (σ⁻¹ * τ) • b - F (σ⁻¹ * τ) x' := by
    rw [ha, show (lift x') = ρ from rfl, key]
    abel
  have hay : a y = τ • b - F τ y := ha y
  have hsmul : (σ • a) y = τ • b - σ • (F (σ⁻¹ * τ) x') := by
    rw [show (σ • a) y = σ • a ((SSGRoute.res k K σ)⁻¹ * y) from rfl]
    rw [show (SSGRoute.res k K σ)⁻¹ * y = x' from rfl]
    rw [hax', smul_sub, ← mul_smul]
    rw [show σ * (σ⁻¹ * τ) = τ by group]
  have hcross' : F τ y = σ • (F (σ⁻¹ * τ) x') + F σ y := by
    have h := congrFun (hcross σ (σ⁻¹ * τ)) y
    rw [show (σ • F (σ⁻¹ * τ) + F σ) y = (σ • F (σ⁻¹ * τ)) y + F σ y from rfl] at h
    rw [show (σ • F (σ⁻¹ * τ)) y
        = σ • (F (σ⁻¹ * τ) ((SSGRoute.res k K σ)⁻¹ * y)) from rfl] at h
    rw [show (SSGRoute.res k K σ)⁻¹ * y = x' from rfl] at h
    rw [show σ * (σ⁻¹ * τ) = τ by group] at h
    exact h
  have hgoal : F σ y = (σ • a) y - a y := by
    rw [hsmul, hay, hcross']
    abel
  rw [hgoal]
  rfl

/-- **`H¹(Gal(Ω/k), Maps(Gal(K/k), Ωˣ)) = 0`.** -/
theorem coindU_H1_subsingleton_v2 {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.CoindU k Ω K)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (CoindU k Ω K)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (CoindU k Ω K)).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (CoindU k Ω K) F from hF.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff]
  rw [Work.AbsoluteKummer.mem_B1_iff]
  obtain ⟨hcross, hloc⟩ :=
    (Work.AbsoluteKummer.mem_Z1_iff (F : (Ω ≃ₐ[k] Ω) → CoindU k Ω K)).mp F.2
  obtain ⟨a, ha⟩ := coindU_coboundary_v2 (K := K) F hcross hloc
  exact ⟨a, by funext σ; rw [Work.GroupCohomology.d0_apply]; exact (ha σ).symm⟩

end Work.SSGRoute
