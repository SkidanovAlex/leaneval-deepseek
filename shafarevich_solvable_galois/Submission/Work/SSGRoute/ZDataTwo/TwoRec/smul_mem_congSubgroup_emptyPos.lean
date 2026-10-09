import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

/-- The canonical local isomorphism of `q`-adic completions induced by `σ` preserves the
valuation, also in the direction `(smulHeightOneSpectrum σ q).adicCompletion → q.adicCompletion`. -/
private lemma adicCongrEquiv_symm_valued {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (y : (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).adicCompletion K) :
    Valued.v ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q).symm y) = Valued.v y := by
  have h := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued σ q
    ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem smul_mem_congSubgroup_emptyPos {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (𝔪 : NK.NUV2.RouteB.Modulus K)
    (hpos : 𝔪.pos = ∅)
    (hexp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) :
    ∀ x : NK.GlobalCFT.Idele K, x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 →
      ρ • x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  intro x hx
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff] at hx ⊢
  obtain ⟨hxfin, _⟩ := hx
  -- `ρ` is an involution, so `ρ⁻¹ = ρ`; this identifies the place `ρ⁻¹ • q` occurring in the
  -- definition of the Galois action on idèles with `Place.smulHeightOneSpectrum ρ q`.
  have hinv : ρ⁻¹ = ρ := by
    have h2 : ρ * ρ = 1 := by simpa [pow_two] using hρ2
    exact inv_eq_of_mul_eq_one_left h2
  refine ⟨fun q => ?_, fun w hw hmem => ?_⟩
  · rw [NK.GlobalCFT.Idele.smul_apply, hinv]
    set q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
      NK.GlobalCFT.Place.smulHeightOneSpectrum ρ q with hq'
    -- the exponent of the modulus at the transported place agrees with the exponent at `q`
    have hexpq' : 𝔪.exps q' = 𝔪.exps q := by
      rw [hq', ← NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum ρ q]
      exact hexp q
    obtain ⟨hval', hcong'⟩ := hxfin q'
    refine ⟨?_, ?_⟩
    · -- local-unit condition
      rw [Units.coe_map]
      change Valued.v ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ q).symm
        ((x (ρ • NK.GlobalCFT.Place.ofFinite q) :
            (NK.GlobalCFT.Place.localField K (ρ • NK.GlobalCFT.Place.ofFinite q))ˣ) :
          NK.GlobalCFT.Place.localField K (ρ • NK.GlobalCFT.Place.ofFinite q))) = 1
      rw [adicCongrEquiv_symm_valued ρ q]
      exact hval'
    · -- congruence condition
      rw [NK.NUV2.RouteB.IsCongAt, Units.coe_map]
      change Valued.v ((NK.GlobalCFT.Place.localRingEquiv ρ (NK.GlobalCFT.Place.ofFinite q)).symm
        ↑(x (ρ • NK.GlobalCFT.Place.ofFinite q)) - 1) ≤ WithZero.exp (-↑(𝔪.exps q))
      rw [← map_one (NK.GlobalCFT.Place.localRingEquiv ρ (NK.GlobalCFT.Place.ofFinite q)).symm,
        ← map_sub]
      change Valued.v ((NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ q).symm
        (↑(x (ρ • NK.GlobalCFT.Place.ofFinite q)) - 1)) ≤ WithZero.exp (-↑(𝔪.exps q))
      rw [adicCongrEquiv_symm_valued ρ q]
      rw [← hexpq']
      exact hcong'
  · -- the positivity condition is vacuous
    rw [hpos] at hmem
    exact absurd hmem (by simp)

end Work.SSGRoute.ZDataTwo.TwoRec
