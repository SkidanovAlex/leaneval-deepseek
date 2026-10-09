import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.productFormula_ramifiedSupport
import Submission.Work.SSGRoute.ZDataMup.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos_clean
import Submission.Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/-! ## Bookkeeping for the group of idèles -/

/-- **The component of a `ℤ`-power of an idèle.** -/
theorem Idele_zpow_apply (x : NK.GlobalCFT.Idele K) (n : ℤ) (v : NK.GlobalCFT.Place K) :
    (x ^ n) v = (x v) ^ n :=
  map_zpow (NK.GlobalCFT.Idele.eval v) x n

/-- **The component at a finite place of a finite product of prime idèles.**  Only the prime idèle
of the place itself contributes, and there it contributes a power of the local uniformizer. -/
theorem prod_ideleOfPrime_zpow_apply_ofFinite (f : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (P : HeightOneSpectrum (𝓞 K)) :
    (∏ Q ∈ f.support, (NK.HeckeL.ideleOfPrime K Q) ^ (f Q))
        (NK.GlobalCFT.Place.ofFinite P)
      = (NK.GlobalCFT.IdeleClassGroup.unifUnit K P) ^ (f P) := by
  classical
  rw [Idele_prod_apply]
  refine (Finset.prod_eq_single (s := f.support) P ?_ ?_).trans ?_
  · intro Q _ hQP
    rw [Idele_zpow_apply,
      NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_setup (q := P) (Q := Q) hQP.symm,
      one_zpow]
  · intro hP
    rw [Finsupp.notMem_support_iff.mp hP, zpow_zero, NK.GlobalCFT.Idele.one_apply]
  · rw [Idele_zpow_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_self]

/-- **The component at an infinite place of a finite product of prime idèles is trivial.** -/
theorem prod_ideleOfPrime_zpow_apply_ofInfinite (f : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (w : NumberField.InfinitePlace K) :
    (∏ Q ∈ f.support, (NK.HeckeL.ideleOfPrime K Q) ^ (f Q))
        (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
  classical
  rw [Idele_prod_apply]
  refine Finset.prod_eq_one fun Q _ => ?_
  rw [Idele_zpow_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite, one_zpow]

/-! ## The normalized valuation of the standard local elements -/

/-- The normalized valuation of the local uniformizer is `1`. -/
theorem finVal_unifUnit (Q : HeightOneSpectrum (𝓞 K)) :
    NK.CFTLib.finVal K Q (NK.GlobalCFT.IdeleClassGroup.unifUnit K Q) = 1 := by
  rw [NK.CFTLib.finVal, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit, WithZero.log_exp]
  norm_num

/-- The normalized valuation is additive for the inverse. -/
theorem finVal_inv (Q : HeightOneSpectrum (𝓞 K)) (z : (Q.adicCompletion K)ˣ) :
    NK.CFTLib.finVal K Q z⁻¹ = - NK.CFTLib.finVal K Q z := by
  have h := NK.CFTLib.finVal_mul K Q z z⁻¹
  rw [mul_inv_cancel, NK.CFTLib.finVal_one] at h
  omega

/-- The normalized valuation is `ℤ`-linear in the exponent. -/
theorem finVal_zpow (Q : HeightOneSpectrum (𝓞 K)) (z : (Q.adicCompletion K)ˣ) (n : ℤ) :
    NK.CFTLib.finVal K Q (z ^ n) = n * NK.CFTLib.finVal K Q z := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk, zpow_natCast, NK.CFTLib.finVal_pow]
  · rw [hk, zpow_neg, zpow_natCast, finVal_inv, NK.CFTLib.finVal_pow]
    ring

/-! ## The main statement -/

/-- **The "unit part" of the principal idèle of a congruent element is an idèle norm.**

Let `m` be an admissible modulus (`IsAdmissible K L m`), `b : Kˣ` congruent to `1` modulo `(m)` at
the ramified primes dividing `(m)` (`hcong`) and totally positive (`hpos`).  Write
`(b) = ∏_Q Q ^ v_Q(b)` and `z := (∏_Q ideleOfPrime K Q ^ v_Q(b))⁻¹ · principalIdele K b`.  Then

* at a prime `Q ∤ (m)`, the component `z_Q` is a unit at an unramified place (`hram`), hence a local
  norm (`localUnits_le_localNormSubgroup_of_unramified`);
* at a ramified prime `Q | (m)`, `hcong` gives `b_Q ≡ 1 mod Q ^ v_Q(m)`, so `z_Q = b_Q` is a local
  norm by admissibility (`IsAdmissible`, via `localNormSubgroup_ofFinite`);
* at an infinite place, `z_w = b_w` is positive, hence a local norm
  (`localImageAt_ofInfinite_mem_localNormSubgroup_of_pos_clean`).

So every component of `z` is a local norm and `z` is an idèle norm
(`mem_normImage_iff_localNorm` / `mem_normImage_iff_forall_mem_localNormSubgroup`). -/
theorem unitIdele_mem_normImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (m : ℕ) (hAdm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) (hram : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal → Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1) (b : Kˣ) (hcong : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (m : NumberField.RingOfIntegers K) ∈ Q.asIdeal → Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) ≠ 1 → Valued.v (algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K) - 1) ≤ Valued.v ((m : ℕ) : Q.adicCompletion K)) (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal), 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion ((b : Kˣ) : K))) : (∏ Q ∈ (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((b : Kˣ) : K))).support, (NK.HeckeL.ideleOfPrime K Q) ^ (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((b : Kˣ) : K)) Q))⁻¹ * NK.GlobalCFT.Idele.principalIdele K b ∈ NK.GlobalCFT.Idele.normImage K L := by
  classical
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : Kˣ) : K) with hA
  set c : NK.GlobalCFT.Idele K :=
    ∏ Q ∈ (NK.CFTLib.Arl.exps A).support,
      (NK.HeckeL.ideleOfPrime K Q) ^ (NK.CFTLib.Arl.exps A Q) with hc
  rw [mem_normImage_iff_forall_mem_localNormSubgroup]
  intro v
  cases v with
  | inl w =>
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hc,
        prod_ideleOfPrime_zpow_apply_ofInfinite, inv_one, one_mul,
        principalIdele_apply_eq_localImageAt]
      exact localImageAt_ofInfinite_mem_localNormSubgroup_of_pos_clean (K := K) (L := L) b w hpos
  | inr P =>
      have hzP : (c⁻¹ * NK.GlobalCFT.Idele.principalIdele K b)
            (NK.GlobalCFT.Place.ofFinite P)
          = (NK.GlobalCFT.IdeleClassGroup.unifUnit K P ^ (NK.CFTLib.Arl.exps A P))⁻¹
            * NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b := by
        rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hc,
          prod_ideleOfPrime_zpow_apply_ofFinite, principalIdele_apply_eq_localImageAt]
      rw [hzP]
      -- every finite component of `z` is a local unit
      have hzPmem : (NK.GlobalCFT.IdeleClassGroup.unifUnit K P ^ (NK.CFTLib.Arl.exps A P))⁻¹
            * NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b
          ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite P) := by
        refine (NK.CFTLib.finVal_eq_zero_iff_mem_localUnits K P
          ((NK.GlobalCFT.IdeleClassGroup.unifUnit K P ^ (NK.CFTLib.Arl.exps A P))⁻¹
            * NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b)).mp ?_
        rw [NK.CFTLib.finVal_mul, finVal_inv, finVal_zpow, finVal_unifUnit,
          finVal_localImageAt_eq_count, ← hA, ← NK.CFTLib.Arl.exps_apply]
        ring
      by_cases hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) P
      · exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L)
          P hunr hzPmem
      · -- a ramified prime: the congruence at `(m)` makes `b` a unit, and admissibility makes it
        -- a local norm
        have hne : Ideal.ramificationIdxIn P.asIdeal (𝓞 L) ≠ 1 := fun h1 =>
          hunr (isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) P h1)
        have hmem : (m : 𝓞 K) ∈ P.asIdeal := by
          by_contra h
          exact hne (hram P h)
        have hbUnit : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b
            ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite P) :=
          isAdm_mem_localUnits_of_congr P m hmem _ (hcong P hmem hne)
        have hexp0 : NK.CFTLib.Arl.exps A P = 0 := by
          rw [NK.CFTLib.Arl.exps_apply]
          simpa [hA] using (count_eq_zero_iff_localUnit (K := K) P b).mpr hbUnit
        obtain ⟨𝔮, h𝔮⟩ :=
          Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) P
        have hbN : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b
            ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
              (NK.GlobalCFT.Place.ofFinite P) := by
          rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite (K := K) (L := L) P]
          exact Subgroup.mem_iSup_of_mem ⟨𝔮, h𝔮⟩
            (hAdm P hmem 𝔮 h𝔮
              (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite P) b)
              (hcong P hmem hne))
        rw [hexp0, zpow_zero, inv_one, one_mul]
        exact hbN

end

end Work.SSGRoute.ZDataMup
