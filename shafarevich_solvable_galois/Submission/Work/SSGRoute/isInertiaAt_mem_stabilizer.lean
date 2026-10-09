import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open NumberField
open scoped Pointwise

/-- **The inertia subgroup at a finite place fixes the place.**

For a number field `k`, an intermediate field `L` of a finite Galois extension `K ⊆ Ω` such that
`L/k` is finite Galois, a nonzero prime `q` of `𝓞 L` and `σ ∈ Gal(L/k)` acting trivially modulo `q`
(`SSGRoute.PTExt.IsInertiaAt q σ`), the place `Place.ofFinite q` is fixed by `σ`.

Indeed `σ • Place.ofFinite q = Place.ofFinite (Place.smulHeightOneSpectrum σ q)` and
`Place.smulHeightOneSpectrum σ q` is `Ideal.map (Place.ringOfIntegersEquiv σ) q.asIdeal`; the
inertia condition is exactly `σ ∈ Ideal.inertia (L ≃ₐ[k] L) q.asIdeal`, and Mathlib's
`Ideal.inertia_le_stabilizer` shows that the ideal-action inertia subgroup is contained in the
stabiliser of the ideal, which is the same condition on the prime. -/
theorem isInertiaAt_mem_stabilizer {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω] (L : IntermediateField K Ω) [NumberField L]
    [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) (hσ : SSGRoute.PTExt.IsInertiaAt q σ) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) := by
  -- Membership in the stabiliser of the finite place is equality of the underlying prime ideals.
  have key : σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ↔
      Ideal.map (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv σ)) q.asIdeal = q.asIdeal := by
    rw [MulAction.mem_stabilizer_iff, NK.GlobalCFT.Place.smul_ofFinite,
      NK.GlobalCFT.Place.ofFinite_inj, IsDedekindDomain.HeightOneSpectrum.ext_iff,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  rw [key]
  -- The inertia condition is membership in the ideal-theoretic inertia subgroup.
  have hmem : σ ∈ Ideal.inertia (L ≃ₐ[k] L) q.asIdeal := by
    show ∀ x : NumberField.RingOfIntegers L, σ • x - x ∈ q.asIdeal
    intro x
    have hcoe : ((σ • x - x : NumberField.RingOfIntegers L) : L) =
        σ (x : L) - (x : L) := by
      have h : algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) =
          algebraMap (NumberField.RingOfIntegers L) L (σ • x) -
            algebraMap (NumberField.RingOfIntegers L) L x := map_sub _ _ _
      rw [show ((σ • x - x : NumberField.RingOfIntegers L) : L) =
          algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) from rfl, h]
      congr 1
    have h1 : q.valuation L (σ (x : L) - (x : L)) < 1 := hσ x
    rw [← hcoe] at h1
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (v := q) _).mp h1
  -- `Ideal.inertia` is contained in the stabiliser of the ideal; rewrite the pointwise action.
  have hstab : σ • q.asIdeal = q.asIdeal :=
    MulAction.mem_stabilizer_iff.mp (Ideal.inertia_le_stabilizer q.asIdeal hmem)
  rw [Ideal.pointwise_smul_def] at hstab
  exact hstab

end Work.SSGRoute
