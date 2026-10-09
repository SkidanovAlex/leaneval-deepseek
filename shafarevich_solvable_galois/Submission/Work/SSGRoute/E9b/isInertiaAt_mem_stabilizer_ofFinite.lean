import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9b

open scoped Pointwise

/-- **Inertia at a finite place fixes that place** (bare-types form).  Let `k` be a number field and `L` a number field with a `k`-algebra structure, `q` a nonzero prime of `𝓞 L` and `σ : L ≃ₐ[k] L` an automorphism acting trivially on the residue field of `q` (`SSGRoute.PTExt.IsInertiaAt q σ`, i.e. `q.valuation L (σ x - x) < 1` for all `x : 𝓞 L`).  Then `σ` fixes the finite place `NK.GlobalCFT.Place.ofFinite q` of `L`.  This is the bare-type companion of the existing `Work.SSGRoute.isInertiaAt_mem_stabilizer` (stated for an intermediate field `L ≤ Ω` of a Galois extension); the proof should go through `Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia`, Mathlib's `Ideal.inertia_le_stabilizer`, and `NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal` / `Place.ofFinite_inj`. -/
lemma isInertiaAt_mem_stabilizer_ofFinite {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) (hσ : SSGRoute.PTExt.IsInertiaAt q σ) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) := by
  -- The place `Place.ofFinite q` is fixed by `σ` exactly when `σ` preserves the ideal `q.asIdeal`.
  have key : σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) ↔
      Ideal.map (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv σ)) q.asIdeal = q.asIdeal := by
    rw [MulAction.mem_stabilizer_iff, NK.GlobalCFT.Place.smul_ofFinite,
      NK.GlobalCFT.Place.ofFinite_inj, IsDedekindDomain.HeightOneSpectrum.ext_iff,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  rw [key]
  -- `IsInertiaAt q σ` is membership in the ideal-theoretic inertia subgroup of `q`.
  have hmem : σ ∈ Ideal.inertia (L ≃ₐ[k] L) q.asIdeal :=
    (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := L) q σ).mp hσ
  -- Inertia is contained in the stabiliser of the ideal, and the pointwise action on ideals of
  -- `𝓞 L` is `Ideal.map` along the induced ring automorphism.
  have hstab : σ • q.asIdeal = q.asIdeal :=
    MulAction.mem_stabilizer_iff.mp (Ideal.inertia_le_stabilizer q.asIdeal hmem)
  rw [Ideal.pointwise_smul_def] at hstab
  exact hstab

end Work.SSGRoute.E9b
