import Mathlib
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.NodeS37.inertSquareOfRhoFixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.P2Close

theorem rhoValuationTransport {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A) :
    ∀ z : ↥K, (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 (ρ z) < 1 ↔
        IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 z < 1) := by
  classical
  -- A chosen lift of `ρ` to `Ω`; it restricts to `ρ` on `↥K`.
  set g : Ω ≃ₐ[k] Ω := Work.SSGRoute.ZDataMup.galLift K ρ with hg_def
  -- The `𝔭`-adic valuation of `↥K`.
  set v := IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 with hv_def
  -- `g` restricts to `ρ` on `↥K`.
  have hg_apply : ∀ x : ↥K, g (x : Ω) = (ρ x : Ω) := by
    intro x
    have h := AlgEquiv.restrictNormalHom_apply (F := k) K g x
    have hspec : (AlgEquiv.restrictNormalHom ↥K) g = ρ := by
      rw [hg_def]; exact Work.SSGRoute.ZDataMup.galLift_spec K ρ
    rw [hspec] at h
    exact h.symm
  -- The restriction of `A` to `↥K` is the valuation subring at `𝔭`.
  have hVB : v.valuationSubring = A.comap (algebraMap ↥K Ω) := by
    rw [hv_def,
      ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := ↥K) 𝔭, h𝔭]
  -- `ρ` preserves this valuation subring, because `g` fixes `A`.
  have hsmul : ρ • A.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
    rw [← Work.SSGRoute.NodeS37.comap_smul_eq_smul_comap (K := K) A g ρ hg_apply, hfixA]
  have hV : ρ • v.valuationSubring = v.valuationSubring := by
    rw [hVB]; exact hsmul
  -- The pulled back valuation `v ∘ ρ` has the same valuation subring as `v`, hence is
  -- equivalent to it, hence has the same elements of value `< 1`.
  have key : ∀ x : ↥K, v (ρ x) ≤ 1 ↔ v x ≤ 1 := by
    intro x
    have hmem : ρ x ∈ v.valuationSubring ↔ x ∈ v.valuationSubring := by
      have h := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
        (g := ρ) (S := v.valuationSubring) (x := ρ x))
      rw [hV] at h
      simpa [AlgEquiv.smul_def] using h
    rwa [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff] at hmem
  have hequiv : (v.comap (ρ.toRingEquiv : ↥K →+* ↥K)).IsEquiv v :=
    Valuation.isEquiv_of_val_le_one (fun x => by
      rw [Valuation.comap_apply]; exact key x)
  have hlt : ∀ {x : ↥K}, (v.comap (ρ.toRingEquiv : ↥K →+* ↥K)) x < 1 ↔ v x < 1 :=
    (Valuation.isEquiv_iff_val_lt_one).mp hequiv
  intro z
  simpa [Valuation.comap_apply] using hlt (x := z)

end Work.SSGRoute.P2Close
