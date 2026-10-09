import Mathlib
import Submission.Work.SSGRoute.ExtChain.localField_place_glue_with_theta
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `carrier_hact` — the carrier-side group-compatibility at a finite place

The E1a `Ext`-chain comparison needs, at each finite place `A` of `Ω`, the compatibility between
the glued `k_v`-automorphism `Φ σ` of the local closure (`σ ∈ decomp k A`) and the restriction
`res k K σ` of `σ` to `K`, at the level of the local completion `K' = θ'.fieldRange ⊆ Ω_v`.

Concretely, writing `eG : D_w ≃* Aut_{k_v}(K')` for the algebra isomorphism supplied by the place
glue (`NK.Mine.localGaloisEquiv` at the finite place `q`), the statement is that the composite

`D_w --eG.symm∘(.|K')--> Aut_{k_v}(K')`  equals  `res k K`,

i.e. that the place dictionary at `q` and the global dictionary `Φ` at `A` agree on `K`.
The proof is a `ψ`-conjugation computation: `eG` is (by `hpt`) the `ψ`-transport of
`localAut`, and on the image of `K` both sides agree by `h4`.
-/

namespace Work.SSGRoute.ExtChain

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option maxHeartbeats 3200000

theorem carrier_hact (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal)
    (θ' : q.adicCompletion K →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) θ'.fieldRange]
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) θ'.fieldRange]
    (ψ : ↥θ'.fieldRange ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K))
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (θ'.fieldRange ≃ₐ[Work.SSGRoute.localFieldAt k A hA] θ'.fieldRange))
    (Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA))
    (hpt : ∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (y : ↥θ'.fieldRange),
      (eG σ) y = ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) σ (ψ y)))
    (h4 : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
      (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
        ψ.symm (algebraMap K (q.adicCompletion K)
          ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)))
    (hgen : IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (fun x : K => ψ.symm (algebraMap K (q.adicCompletion K) x))) = ⊤) :
    ∀ σ : ↥(SSGRoute.decomp k A),
      eG.symm (AlgEquiv.restrictNormalHom ↥θ'.fieldRange (Φ σ))
        = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) := by
  have halg : Function.Injective (algebraMap K (q.adicCompletion K)) := by
    intro a b hab
    have h0 : algebraMap K (q.adicCompletion K) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h3 : a - b = 0 := by
      by_contra hne
      have h5 : algebraMap K (q.adicCompletion K) ((a - b)⁻¹ * (a - b)) = 1 := by
        rw [inv_mul_cancel₀ hne, map_one]
      rw [map_mul, h0, mul_zero] at h5
      exact one_ne_zero h5.symm
    exact sub_eq_zero.mp h3
  intro σ
  set τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    eG.symm (AlgEquiv.restrictNormalHom ↥θ'.fieldRange (Φ σ)) with hτ
  have hτe : eG τ = AlgEquiv.restrictNormalHom ↥θ'.fieldRange (Φ σ) :=
    eG.apply_symm_apply _
  apply AlgEquiv.ext
  intro x
  apply halg
  apply ψ.symm.injective
  refine Subtype.ext ?_
  have h1 : (ψ.symm (algebraMap K (q.adicCompletion K) ((τ : K ≃ₐ[k] K) x)) :
        Work.SSGRoute.localClosureAt k A hA) =
      ((eG τ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) :
        Work.SSGRoute.localClosureAt k A hA) := by
    have hp := hpt τ (ψ.symm (algebraMap K (q.adicCompletion K) x))
    rw [ψ.apply_symm_apply] at hp
    rw [NK.HassePrinciple.localAut_algebraMap] at hp
    exact congrArg (fun z : ↥θ'.fieldRange =>
      (z : Work.SSGRoute.localClosureAt k A hA)) hp.symm
  have h2 : ((eG τ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) :
        Work.SSGRoute.localClosureAt k A hA) =
      (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) := by
    rw [hτe]
    exact AlgEquiv.restrictNormalHom_apply θ'.fieldRange (Φ σ) _
  rw [h1, h2]
  exact h4 σ x

end Work.SSGRoute.ExtChain
