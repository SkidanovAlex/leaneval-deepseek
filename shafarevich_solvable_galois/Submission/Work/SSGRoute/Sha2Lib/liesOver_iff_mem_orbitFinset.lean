import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.HSRow.SplitPlaceSetup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The primes of `𝓞 K` above a prime of `𝓞 k` are exactly the `Gal(K/k)`-orbit

For a finite Galois extension `K / k` of number fields and a prime `q` of `𝓞 K`, the primes `𝔮`
of `𝓞 K` lying over the contraction `q ∩ 𝓞 k` are exactly the conjugates `τ • q`,
`τ : Gal(K/k)` — i.e. the elements of `Work.SSGRoute.HSRow.orbitFinset q`.

The two ingredients are the transitivity of the Galois action on the places of `K` above a
fixed place of `k` (`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`) and the
fact that a Galois conjugate lies over the same prime
(`NK.GlobalCFT.Galois.globalCFT_finitePlace_smul_liesOver`).
-/

open scoped NumberField

namespace Work.SSGRoute.Sha2Lib

theorem liesOver_iff_mem_orbitFinset (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔮.asIdeal.LiesOver (q.asIdeal.under (NumberField.RingOfIntegers k)) ↔
        𝔮 ∈ Work.SSGRoute.HSRow.orbitFinset (k := k) (K := K) q := by
  classical
  intro 𝔮
  -- the prime of `𝓞 k` below `q`, viewed as a height one spectrum
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hQasIdeal : Q.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) := rfl
  constructor
  · -- `𝔮` lies over `Q`, so some `σ : Gal(K/k)` carries `q` to `𝔮`
    intro h
    have hq : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite Q) :=
      NK.GlobalCFT.Place.liesOver_ofFinite (Ideal.LiesOver.mk rfl)
    have h𝔮 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite 𝔮)
        (NK.GlobalCFT.Place.ofFinite Q) :=
      NK.GlobalCFT.Place.liesOver_ofFinite (Ideal.LiesOver.mk (hQasIdeal.trans h.over))
    obtain ⟨σ, hσ⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := k) (L := K) hq h𝔮
    have hσ' : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = 𝔮 := by
      rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj] at hσ
      exact hσ
    rw [Work.SSGRoute.HSRow.orbitFinset]
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, hσ'⟩
  · -- a conjugate `τ • q` lies over the same prime of `𝓞 k` as `q`
    intro h
    rw [Work.SSGRoute.HSRow.orbitFinset, Finset.mem_image] at h
    obtain ⟨τ, -, hτ⟩ := h
    rw [← hτ]
    refine (NK.GlobalCFT.Galois.globalCFT_finitePlace_smul_liesOver (K := k) (L := K) τ q
      Q).mpr ?_
    exact Ideal.LiesOver.mk hQasIdeal

end Work.SSGRoute.Sha2Lib
