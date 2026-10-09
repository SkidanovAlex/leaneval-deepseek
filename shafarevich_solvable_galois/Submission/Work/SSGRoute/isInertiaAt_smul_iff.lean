import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-!
# Conjugacy of the inertia condition at a finite place

`SSGRoute.PTExt.IsInertiaAt q σ` says that `σ ∈ Gal(L/k)` acts trivially on the residue field of
the prime `q` of `𝓞 L`, i.e. that `q.valuation L (σ x - x) < 1` for every integral `x`.

The main result of this file is the standard conjugacy formula for the inertia subgroup: for
`σ, τ : Gal(L/k)` and a prime `q` of `𝓞 L`, with `σ • q` the image prime,
`τ` lies in the inertia group of `σ • q` iff `σ⁻¹ τ σ` lies in the inertia group of `q`.
-/

section General

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]

open NK.GlobalCFT

/-- The inertia condition rewritten as a membership condition for the prime ideal: `σ` acts
trivially mod `q` iff `σ • x - x ∈ q.asIdeal` for every `x ∈ 𝓞 L`. -/
private lemma isInertiaAtConj_iff_forall_mem
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) :
    SSGRoute.PTExt.IsInertiaAt q σ ↔
      ∀ x : NumberField.RingOfIntegers L, σ • x - x ∈ q.asIdeal := by
  unfold SSGRoute.PTExt.IsInertiaAt
  refine forall_congr' fun x => ?_
  have key : ((σ • x - x : NumberField.RingOfIntegers L) : L) = σ (x : L) - (x : L) := by
    have h : algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x) -
          algebraMap (NumberField.RingOfIntegers L) L x := map_sub _ _ _
    rw [show ((σ • x - x : NumberField.RingOfIntegers L) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) from rfl, h]
    congr 1
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (v := q) _

/-- The Galois action on `𝓞 L` is the action on the ideal: `τ • (σ • y) - σ • y` is the image
under `σ` of `(σ⁻¹ τ σ) • y - y`. -/
private lemma isInertiaAtConj_sub_eq (σ τ : L ≃ₐ[k] L)
    (y : NumberField.RingOfIntegers L) :
    τ • (σ • y) - σ • y =
      NK.GlobalCFT.Place.ringOfIntegersEquiv σ ((σ⁻¹ * τ * σ) • y - y) := by
  rw [show NK.GlobalCFT.Place.ringOfIntegersEquiv σ ((σ⁻¹ * τ * σ) • y - y)
      = σ • ((σ⁻¹ * τ * σ) • y - y) from rfl, smul_sub]
  rw [← mul_smul τ σ y]
  have hgroup : τ * σ = σ * (σ⁻¹ * τ * σ) := by group
  rw [hgroup, mul_smul]

/-- **Conjugacy of the inertia condition.**  For `σ, τ ∈ Gal(L/k)` and a nonzero prime `q` of
`𝓞 L`, the element `τ` lies in the inertia group of the image prime `σ • q` if and only if
`σ⁻¹ τ σ` lies in the inertia group of `q`. -/
private theorem isInertiaAtConj_smul_iff_general
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ τ : L ≃ₐ[k] L) :
    SSGRoute.PTExt.IsInertiaAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) τ ↔
      SSGRoute.PTExt.IsInertiaAt q (σ⁻¹ * τ * σ) := by
  rw [isInertiaAtConj_iff_forall_mem, isInertiaAtConj_iff_forall_mem]
  constructor
  · intro h y
    have h1 : τ • (σ • y) - σ • y ∈
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal := h (σ • y)
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, isInertiaAtConj_sub_eq σ τ y] at h1
    rwa [Ideal.apply_mem_of_equiv_iff] at h1
  · intro h x
    have hx : σ • (σ⁻¹ • x) = x := by rw [← mul_smul, mul_inv_cancel, one_smul]
    have h1 : (σ⁻¹ * τ * σ) • (σ⁻¹ • x) - σ⁻¹ • x ∈ q.asIdeal := h (σ⁻¹ • x)
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, ← hx,
      isInertiaAtConj_sub_eq σ τ (σ⁻¹ • x)]
    exact Ideal.mem_map_of_mem _ h1

end General

theorem isInertiaAt_smul_iff {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω] (L : IntermediateField K Ω) [NumberField L]
    [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ τ : L ≃ₐ[k] L) :
    SSGRoute.PTExt.IsInertiaAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) τ ↔
      SSGRoute.PTExt.IsInertiaAt q (σ⁻¹ * τ * σ) :=
  isInertiaAtConj_smul_iff_general (k := k) (L := ↥L) q σ τ

end Work.SSGRoute
