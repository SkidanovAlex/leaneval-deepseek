import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.Gap.langCyclicRelIndex
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The product of the norms of the primes of `𝓞 K` that ramify in `L`. -/
noncomputable def ramNormProd : ℕ :=
  ∏ Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L), Ideal.absNorm Q.asIdeal

/-- The exponent of the optimal modulus: strictly larger than every local level. -/
noncomputable def ramExp : ℕ :=
  (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
    (NK.CFTLib.ArtinReciprocityIdeal.levelQ (K := K) (L := L)) + 1

/-- **The optimal natural-number modulus supported on the ramified primes.** -/
noncomputable def mRam : ℕ := ramNormProd (K := K) (L := L) ^ ramExp (K := K) (L := L)

theorem ramNormProd_ne_zero : ramNormProd (K := K) (L := L) ≠ 0 := by
  rw [ramNormProd, Finset.prod_ne_zero_iff]
  intro Q _
  rw [Ideal.absNorm_ne_zero_iff]
  infer_instance

theorem mRam_pos : 0 < mRam (K := K) (L := L) :=
  Nat.pos_of_ne_zero (pow_ne_zero _ ramNormProd_ne_zero)

theorem ramExp_pos : 0 < ramExp (K := K) (L := L) := by
  rw [ramExp]
  exact Nat.succ_pos _

theorem le_ramExp (Q : HeightOneSpectrum (𝓞 K))
    (hQ : Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)) :
    NK.CFTLib.ArtinReciprocityIdeal.levelQ (K := K) (L := L) Q ≤ ramExp (K := K) (L := L) := by
  rw [ramExp]
  exact Finset.le_sup hQ |>.trans (Nat.le_succ _)

theorem dvd_mRam (Q : HeightOneSpectrum (𝓞 K))
    (hQ : Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)) :
    (Ideal.absNorm Q.asIdeal) ^ (NK.CFTLib.ArtinReciprocityIdeal.levelQ (K := K) (L := L) Q) ∣
      mRam (K := K) (L := L) := by
  rw [mRam]
  exact (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ hQ) _).trans
    (pow_dvd_pow _ (le_ramExp (K := K) (L := L) Q hQ))

/-- The `levelQ Q`-th power of `absNorm Q` lies in `Q`. -/
theorem absNorm_pow_mem_pow (Q : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    (((Ideal.absNorm Q.asIdeal) ^ k : ℕ) : 𝓞 K) ∈ Q.asIdeal ^ k := by
  rw [Nat.cast_pow]
  exact Ideal.pow_mem_pow (Ideal.absNorm_mem Q.asIdeal) k

theorem absNorm_pow_mem (Q : HeightOneSpectrum (𝓞 K)) (k : ℕ) (hk : 0 < k) :
    (((Ideal.absNorm Q.asIdeal) ^ k : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hmem : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 K) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  rw [Nat.cast_pow]
  exact Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hk) (Ideal.pow_mem_pow hmem k)

theorem mRam_isAdmissible :
    NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L (mRam (K := K) (L := L)) := by
  refine NK.CFTLib.ArtinReciprocityIdeal.isAdmissible_of_mem_pow (K := K) (L := L)
    (mRam (K := K) (L := L)) ?_
  intro Q hQ
  obtain ⟨c, hc⟩ := dvd_mRam (K := K) (L := L) Q hQ
  rw [hc, Nat.cast_mul]
  rw [← Ideal.mul_top (Q.asIdeal ^ NK.CFTLib.ArtinReciprocityIdeal.levelQ (K := K) (L := L) Q)]
  exact Ideal.mul_mem_mul (absNorm_pow_mem_pow (K := K) Q _) Submodule.mem_top

theorem mRam_strongSupport :
    ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      ((mRam (K := K) (L := L) : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  intro p hp
  obtain ⟨P, hP, he⟩ : ∃ P : NK.Chebotarev.PrimeIdeal L,
      P.asIdeal.LiesOver p.asIdeal ∧ P.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := by
    by_contra h
    exact hp fun P hP => by
      by_contra hne
      exact h ⟨P, hP, hne⟩
  have hpram : p ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L) :=
    NK.CFTLib.ExistsCongruence.mem_ramPrimes_of_ramificationIdx_ne_one (K := K) (L := L) hP he
  obtain ⟨c, hc⟩ := dvd_mRam (K := K) (L := L) p hpram
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right (c : 𝓞 K) p.asIdeal
    (absNorm_pow_mem (K := K) p (NK.CFTLib.ArtinReciprocityIdeal.levelQ (K := K) (L := L) p)
      (NK.CFTLib.ArtinReciprocityIdeal.levelQ_pos (K := K) (L := L) p))

/-- **Every prime dividing `(mRam)` has its rational prime below a ramified prime**: there is a
ramified prime `Q` of `K` whose norm lies in `𝔮`. -/
theorem mRam_support_bound (𝔮 : HeightOneSpectrum (𝓞 K))
    (h𝔮 : ((mRam (K := K) (L := L) : ℕ) : 𝓞 K) ∈ 𝔮.asIdeal) :
    ∃ Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L),
      ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 K) ∈ 𝔮.asIdeal := by
  have h1 : (∏ Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L),
      ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 K)) ∈ 𝔮.asIdeal :=
    𝔮.isPrime.mem_of_pow_mem _ (by
      rw [mRam, ramNormProd] at h𝔮
      simpa using h𝔮)
  exact 𝔮.isPrime.prod_mem_iff.mp h1

/-! ## Status of the reciprocity condition at `mRam`

`mRam_hprinc : artinKillsPrincipal K L mRam` is **not** obtained by applying
`artinSymbol_span_eq_one_of_kernelLe_of_relIndex` to the pair
(`kernelLe_of_auxField K L mRam …`, `langCyclicRelIndex K L`): that theorem returns an *abstract*
witness `∃ m, …` (its proof uses `Exists.elim`, so the witness is not definitionally `mRam`), which
is enough for `NK.CFTLib.ArtinReciprocityIdeal.cyclic_conductor_ramifiedSupport`
(a modulus *exists* with strong support and `hprinc`) but not for the sharp support bound recorded
here.  To get `hprinc` **at `mRam`** one reruns the index argument of
`artinSymbol_span_eq_one_of_kernelLe_of_relIndex` with `m := mRam` fixed; the two inputs are
available at `mRam`:
* `kernelLe_of_auxField K L mRam (mRam_pos …) (auxField_exists K L mRam (mRam_pos …)) (mRam_strongSupport …)`;
* `langCyclicRelIndex K L mRam (mRam_pos …) (mRam_strongSupport …) (mRam_isAdmissible …)`.
-/

end

end Work.SSGRoute.ZDataMup
