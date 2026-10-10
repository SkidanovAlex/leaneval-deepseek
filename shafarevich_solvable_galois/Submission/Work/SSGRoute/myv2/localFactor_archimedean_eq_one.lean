import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.N2v2.kummerChar_archimedean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.myv2

/-- **The archimedean local factors of a finite abelian level are trivial.**  At an archimedean
place `v` of `↥K` the local field has no ring homomorphism to `ℝ`
(`Work.SSG8Escape.localField_not_real_of_no_involutions`), hence is `ℂ`, hence its unit group is
divisible; a homomorphism from a divisible group to the finite group `Gal(E/↥K)` is trivial.  This is
the `harch` hypothesis of `N2v2.heart_chi1_part` / `heart_chi2_part`.

Route: `v` is archimedean, hence of the form `ofInfinite w`; `localField_not_real_of_no_involutions`
gives `w.IsComplex` (`NumberField.InfinitePlace.not_isReal_iff_isComplex` plus
`ringEquivRealOfIsReal`), so `localField ↥K v ≃+* ℂ`
(`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`) and its unit group is
`RootableBy ℕ` (`N2v2.rootableBy_units_of_ringEquiv_complex`), while `↥E ≃ₐ[↥K] ↥E` is finite
(`AlgEquiv.fintype`), so `N2v2.MonoidHom.eq_one_of_rootableBy_finite θv u` gives the result. -/
theorem localFactor_archimedean_eq_one (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    (θ : (v : NK.GlobalCFT.Place ↥K) →
      (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E)) :
    ∀ (v : NK.GlobalCFT.Place ↥K), (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      v ≠ NK.GlobalCFT.Place.ofFinite 𝔮) →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K v)ˣ, θ v u = 1 := by
  intro v hv u
  -- `v` is archimedean, i.e. not a finite place
  have hvinf : ¬ v.IsFinite := by
    intro h
    obtain ⟨q, hq⟩ := NK.GlobalCFT.Place.isFinite_iff.mp h
    exact hv q hq
  -- so the local field admits no ring homomorphism to `ℝ`
  have hnotreal := Work.SSG8Escape.localField_not_real_of_no_involutions
    p K ζ hζ hKimag v hvinf
  cases v with
  | inr q =>
    -- impossible: `ofFinite q` is a finite place
    exact absurd (NK.GlobalCFT.Place.isFinite_ofFinite q) hvinf
  | inl w =>
    -- the local field is `ℂ`, so its unit group is rootable by `ℕ`
    have hC : NumberField.InfinitePlace.IsComplex w := by
      rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
      intro hR
      exact hnotreal
        ⟨(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hR).toRingHom, trivial⟩
    haveI : RootableBy
        (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofInfinite w))ˣ ℕ :=
      Work.SSGRoute.N2v2.rootableBy_units_of_ringEquiv_complex
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC)
    -- and `Gal(E/↥K)` is finite, so `θ w` is trivial
    exact Work.SSGRoute.N2v2.MonoidHom.eq_one_of_rootableBy_finite
      (θ (NK.GlobalCFT.Place.ofInfinite w)) u

end Work.SSGRoute.myv2
