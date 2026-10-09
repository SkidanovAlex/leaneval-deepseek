import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.localGlobalArtinMap_killing_principalIdele
import Submission.Work.SSGRoute.ZDataMup.localFactor_productFormula_abelian
import Submission.NK.CFTLib.HR.Basic
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Auxiliary lemmas for the conductor drop at an admissible modulus

These lemmas are the pieces of the local–global computation described in the docstring of the main
theorem; they do not depend on the target statement. -/

/-- `Ideal.ramificationIdxIn p (𝓞 L) = 1` is `NK.HeckeL.IsUnramifiedIn p`. -/
theorem isUnramifiedIn_of_ramificationIdxIn_eq_one (p : HeightOneSpectrum (𝓞 K))
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal q.asIdeal
    (Gal(L/K))]
  exact h

/-- The converse reading: a prime which is not unramified has ramification index `≠ 1`. -/
theorem ramificationIdxIn_ne_one_of_not_isUnramifiedIn (p : HeightOneSpectrum (𝓞 K))
    (h : ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p) :
    Ideal.ramificationIdxIn p.asIdeal (𝓞 L) ≠ 1 :=
  fun h1 => h (isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) p h1)

/-- The `q`-adic exponent of the principal idèle of `b` is the multiplicity of `q` in `(b)`. -/
theorem exps_spanSingleton_eq_exp (b : Kˣ) (Q : HeightOneSpectrum (𝓞 K)) :
    NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q
      = Idele.exp Q (Idele.principalIdele K b) := by
  rw [NK.CFTLib.Arl.exps_apply, ← Idele.idealOf_principalIdele, Idele.count_idealOf]

/-- The image of `b` in the completion at a finite place, as the coercion of `localImageAt`. -/
theorem localImageAt_ofFinite_coe (Q : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :
    ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K)
      = algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K) := rfl

/-- **Admissibility is local-normality of the congruence units.**  If `M` is admissible, then at
every prime `𝔭 | (M)` every unit of `K_𝔭` which is `≡ 1 mod M` lies in the local norm subgroup. -/
theorem mem_localNormSubgroup_of_isAdmissible
    {M : ℕ} (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M)
    (Q : HeightOneSpectrum (𝓞 K)) (hQ : (M : 𝓞 K) ∈ Q.asIdeal)
    (x : (Q.adicCompletion K)ˣ)
    (hx : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((x : Q.adicCompletion K) - 1)
        ≤ Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((M : ℕ) : Q.adicCompletion K))) :
    x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
  exact Subgroup.mem_iSup_of_mem ⟨q, hq⟩ (hadm Q hQ q hq x hx)

/-- A prime occurring in the principal ideal `(b)` (i.e. `v_𝔭(b) ≠ 0`) is unramified: at a ramified
prime dividing `(M)` the congruence hypothesis forces `b` to be a local unit. -/
theorem isUnramifiedIn_of_exps_ne_zero (b : Kˣ) {M : ℕ}
    (hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hcong : ∀ 𝔮 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v (((M : ℕ) : 𝔮.adicCompletion K)))
    (Q : HeightOneSpectrum (𝓞 K))
    (hQ : NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q ≠ 0) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
  by_contra hnot
  have he : Ideal.ramificationIdxIn Q.asIdeal (𝓞 L) ≠ 1 :=
    ramificationIdxIn_ne_one_of_not_isUnramifiedIn (K := K) (L := L) Q hnot
  have hMQ : (M : 𝓞 K) ∈ Q.asIdeal := by
    by_contra h
    exact he (hram Q h)
  have hval1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt (by simpa only [localImageAt_ofFinite_coe] using hcong Q hMQ he)
      (NK.CFTLib.Arl.val_natCast_lt_one (K := K) Q M hMQ)
  have hval2 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : Q.adicCompletion K))
      (y := (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b :
        (Q.adicCompletion K)ˣ) - 1)
      (by rw [map_one]; exact hval1)
    rw [map_one, show (1 : Q.adicCompletion K)
      + ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b :
          (Q.adicCompletion K)ˣ) - 1)
      = (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b :
          (Q.adicCompletion K)ˣ) from by ring] at h
    exact h
  have hexp : Idele.exp Q (Idele.principalIdele K b) = 0 := by
    have h2 : WithZero.exp (-(Idele.exp Q (Idele.principalIdele K b))) = 1 := by
      rw [← Idele.exp_val Q (Idele.principalIdele K b),
        principalIdele_apply_eq_localImageAt]
      exact hval2
    rw [← WithZero.exp_zero] at h2
    exact neg_eq_zero.mp (WithZero.exp_injective h2)
  exact hQ (exps_spanSingleton_eq_exp (K := K) b Q ▸ hexp)

/-- At a prime outside the support of `(b)`, the local factor of the principal idèle `b` is `1`:
the component is a local unit, hence a local norm at an unramified prime, while at a ramified prime
dividing `(M)` the congruence hypothesis and admissibility apply. -/
theorem onePlace_localImageAt_eq_one_of_exps_eq_zero (b : Kˣ) {M : ℕ}
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M)
    (hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hcong : ∀ 𝔮 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v (((M : ℕ) : 𝔮.adicCompletion K)))
    (Φ : Idele K →* Gal(L/K))
    (hloc : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (Q : HeightOneSpectrum (𝓞 K))
    (hQ : NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q = 0) :
    Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)) = 1 := by
  have hexp : Idele.exp Q (Idele.principalIdele K b) = 0 := by
    rw [← exps_spanSingleton_eq_exp (K := K) b Q]; exact hQ
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) = 1 := by
    rw [← principalIdele_apply_eq_localImageAt,
      Idele.exp_val Q (Idele.principalIdele K b), hexp, neg_zero, WithZero.exp_zero]
  have hunit : NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b
      ∈ Place.localUnits K (Place.ofFinite Q) :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mpr hval
  by_cases hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q
  · refine (hloc (Place.ofFinite Q)
      (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)).mpr ?_
    exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L)
      Q hunr hunit
  · have he : Ideal.ramificationIdxIn Q.asIdeal (𝓞 L) ≠ 1 :=
      ramificationIdxIn_ne_one_of_not_isUnramifiedIn (K := K) (L := L) Q hunr
    have hMQ : (M : 𝓞 K) ∈ Q.asIdeal := by
      by_contra h
      exact he (hram Q h)
    refine (hloc (Place.ofFinite Q)
      (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)).mpr ?_
    exact mem_localNormSubgroup_of_isAdmissible (K := K) (L := L) hadm Q hMQ _
      (by simpa only [localImageAt_ofFinite_coe] using hcong Q hMQ he)

/-- **The local factor at a finite prime.**  At every finite prime, the value of the local–global
Artin map on the `𝔭`-component of the principal idèle `b` is the Frobenius at `𝔭` raised to the
multiplicity of `𝔭` in the principal ideal `(b)`. -/
theorem phi_onePlace_ofFinite_eq_frob_zpow (b : Kˣ) {M : ℕ}
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M)
    (hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hcong : ∀ 𝔮 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v (((M : ℕ) : 𝔮.adicCompletion K)))
    (Φ : Idele K →* Gal(L/K))
    (hloc : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hfrob : ∀ Q : HeightOneSpectrum (𝓞 K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (Q : HeightOneSpectrum (𝓞 K)) :
    Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b))
      = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^
          (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q) := by
  classical
  by_cases hQ : NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q = 0
  · rw [onePlace_localImageAt_eq_one_of_exps_eq_zero (K := K) (L := L) b hadm hram hcong Φ hloc
      Q hQ, hQ, zpow_zero]
  · have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q :=
      isUnramifiedIn_of_exps_ne_zero (K := K) (L := L) b hram hcong Q hQ
    obtain ⟨n, u, hu, hzu⟩ :=
      NK.CFTLib.HR.exists_zpow_unifUnit_mul_mem_localUnits (K := K) Q
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)
    -- `onePlace` is multiplicative, hence commutes with integer powers
    let op : (Place.localField K (Place.ofFinite Q))ˣ →* Idele K :=
      { toFun := NK.HassePrinciple.onePlace (Place.ofFinite Q)
        map_one' := NK.CFTLib.IdeleHasse.onePlace_one _
        map_mul' := NK.CFTLib.IdeleHasse.onePlace_mul _ }
    have hzpow : ∀ (a : (Place.localField K (Place.ofFinite Q))ˣ) (k : ℤ),
        NK.HassePrinciple.onePlace (Place.ofFinite Q) (a ^ k)
          = (NK.HassePrinciple.onePlace (Place.ofFinite Q) a) ^ k :=
      fun a k => op.map_zpow a k
    have hΦu : Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) u) = 1 :=
      (hloc (Place.ofFinite Q) u).mpr
        (NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified
          (K := K) (L := L) Q hunr hu)
    have h1 : NK.HassePrinciple.onePlace (Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)
        = (NK.HeckeL.ideleOfPrime K Q) ^ n
          * NK.HassePrinciple.onePlace (Place.ofFinite Q) u := by
      calc NK.HassePrinciple.onePlace (Place.ofFinite Q)
            (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b)
          = NK.HassePrinciple.onePlace (Place.ofFinite Q)
              (IdeleClassGroup.unifUnit K Q ^ n * u) := by rw [hzu]
        _ = NK.HassePrinciple.onePlace (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q ^ n)
              * NK.HassePrinciple.onePlace (Place.ofFinite Q) u :=
              NK.CFTLib.IdeleHasse.onePlace_mul _ _ _
        _ = (NK.HassePrinciple.onePlace (Place.ofFinite Q) (IdeleClassGroup.unifUnit K Q)) ^ n
              * NK.HassePrinciple.onePlace (Place.ofFinite Q) u :=
              congrArg (fun z => z * NK.HassePrinciple.onePlace (Place.ofFinite Q) u) (hzpow _ _)
        _ = (NK.HeckeL.ideleOfPrime K Q) ^ n
              * NK.HassePrinciple.onePlace (Place.ofFinite Q) u := by
              rw [NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime]
    have hmain : Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b))
        = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ n := by
      rw [h1]
      calc Φ ((NK.HeckeL.ideleOfPrime K Q) ^ n
            * NK.HassePrinciple.onePlace (Place.ofFinite Q) u)
          = Φ ((NK.HeckeL.ideleOfPrime K Q) ^ n)
            * Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) u) := map_mul Φ _ _
        _ = (Φ (NK.HeckeL.ideleOfPrime K Q)) ^ n
            * Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) u) :=
              congrArg (fun z => z * Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) u))
                (MonoidHom.map_zpow Φ (NK.HeckeL.ideleOfPrime K Q) n)
        _ = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ n
            * Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q) u) := by rw [hfrob Q hunr]
        _ = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ n := by rw [hΦu, mul_one]
    have hn : n = Idele.exp Q (Idele.principalIdele K b) := by
      have hv1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
            Q.adicCompletion K) = WithZero.exp (-n) := by
        rw [hzu, Units.val_mul, map_mul, IdeleClassGroup.valued_unifUnit_zpow,
          (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp hu, mul_one]
      have hv2 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b : (Q.adicCompletion K)ˣ) :
            Q.adicCompletion K)
          = WithZero.exp (-(Idele.exp Q (Idele.principalIdele K b))) := by
        rw [← principalIdele_apply_eq_localImageAt,
          Idele.exp_val Q (Idele.principalIdele K b)]
      exact neg_inj.mp (WithZero.exp_injective (hv1.symm.trans hv2))
    rw [exps_spanSingleton_eq_exp (K := K) b Q, ← hn]
    exact hmain

/-- **The local factor at an infinite place** is trivial when `b` is positive at every real
place. -/
theorem phi_onePlace_ofInfinite_eq_one (b : Kˣ)
    (hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K)))
    (Φ : Idele K →* Gal(L/K))
    (hloc : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (w : InfinitePlace K) :
    Φ (NK.HassePrinciple.onePlace (Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (Place.ofInfinite w) b)) = 1 := by
  refine (hloc (Place.ofInfinite w)
    (NK.CFTLib.IdeleHasse.localImageAt (Place.ofInfinite w) b)).mpr ?_
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
  refine Subgroup.mem_iSup_of_mem
    ⟨NK.CFTLib.ExistsCongruence.aboveInf (K := K) (L := L) w,
      NK.CFTLib.ExistsCongruence.aboveInf_liesOver (K := K) (L := L) w⟩ ?_
  exact NK.CFTLib.ExistsCongruence.posAtReal_mem_range_localNormInfinite
    (K := K) (L := L) (v := w)
    (w := NK.CFTLib.ExistsCongruence.aboveInf (K := K) (L := L) w)
    (hw := NK.CFTLib.ExistsCongruence.aboveInf_liesOver (K := K) (L := L) w)
    (u := NK.CFTLib.IdeleHasse.localImageAt (Place.ofInfinite w) b) (fun hw => hpos w hw)

/-! ## Products of local factors -/

/-- The `cprod` of a function over the image of a finite set of primes. -/
theorem cprod_image {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {ι κ : Type} [DecidableEq ι] {s : Finset κ} {g : κ → ι} (hg : Set.InjOn g ↑s) (f : ι → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (s.image g) f
      = NK.CFTLib.IdeleHasse.cprod hcomm s (fun x => f (g x)) := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  rw [Finset.prod_image hg]

/-- The `cprod` over the support of the exponent vector of a fractional ideal is the Artin
symbol of that ideal. -/
theorem cprod_support_eq_artinSym (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (A : FractionalIdeal (𝓞 K)⁰ K) :
    NK.CFTLib.IdeleHasse.cprod hcomm (NK.CFTLib.Arl.exps A).support
        (fun Q => (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.Arl.exps A Q))
      = NK.CFTLib.Arl.artinSym hcomm A := by
  letI : CommMonoid Gal(L/K) := NK.CFTLib.Arl.galCommMonoid hcomm
  unfold NK.CFTLib.IdeleHasse.cprod NK.CFTLib.Arl.artinSym
  rw [Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) (subset_refl _)
    (fun Q e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ e)
    (fun i _ => zpow_zero _)]
  exact Finset.prod_congr rfl (fun i _ => rfl)

/-- **The product of the local factors of the principal idèle `b` is the Artin symbol of `(b)`.**
This is the bookkeeping which turns the `cprod` of the local–global Artin map into the ideal
theoretic Artin symbol. -/
theorem cprod_localFactor_eq_artinSym [DecidableEq (Place K)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Φ : Idele K →* Gal(L/K)) (b : Kˣ)
    (hfac : ∀ Q : HeightOneSpectrum (𝓞 K),
      Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
          (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b))
        = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^
            (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q)) :
    NK.CFTLib.IdeleHasse.cprod hcomm
        ((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support.image
          Place.ofFinite)
        (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v b)))
      = NK.CFTLib.Arl.artinSym hcomm
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) := by
  classical
  have hinj : Set.InjOn Place.ofFinite
      ((↑((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support) :
        Set (HeightOneSpectrum (𝓞 K)))) := by
    intro a _ c _ h
    exact Place.ofFinite_inj.mp h
  have h1 : NK.CFTLib.IdeleHasse.cprod hcomm
        ((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support.image
          Place.ofFinite)
        (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v b)))
      = NK.CFTLib.IdeleHasse.cprod hcomm
        ((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support)
        (fun Q => Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
          (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b))) :=
    cprod_image hcomm hinj _
  rw [h1, NK.CFTLib.IdeleHasse.cprod_congr hcomm (fun Q => hfac Q)]
  exact cprod_support_eq_artinSym (K := K) (L := L) hcomm _

end

/-- For a **cyclic** extension `L/K`: if the modulus `M` is admissible (every unit `≡ 1 mod M` at
`𝔭 | (M)` is a local norm) and every prime `𝔭 ∤ (M)` is unramified, then the Artin symbol of the
principal ideal `(b)` is trivial as soon as `b` is `≡ 1 mod M` at the **ramified** primes dividing
`(M)` and totally positive.

Proof route: use the glued local–global Artin map `Φ` of
`Work.SSGRoute.ZDataMup.localGlobalArtinMap_killing_principalIdele`, which is Frobenius-normalised
at *every* unramified prime (`Φ (ideleOfPrime Q) = frobAtPrime Q`), kills principal idèles and
idèlic norms and satisfies `Φ (onePlace v a) = 1 ↔ a` a local norm.  Grouping the product formula
`∏_v Φ (onePlace v b_v) = Φ (principalIdele b) = 1` (`cprod_localFactor_eq_one`) one finds that
every factor outside the support of `(b)` is `1` (unramified primes: local units are norms;
ramified primes: `b_v ≡ 1 mod M` and `hadm`), and the remaining factors are exactly the Frobenius
elements of the primes dividing `(b)`, i.e. `artinSym (b)`. -/

theorem artinSym_eq_one_of_isAdmissible_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  classical
  obtain ⟨Φ, -, hnorm, hprin, hloc, hfrob⟩ :=
    localGlobalArtinMap_killing_principalIdele (K := K) (L := L)
      (inferInstance : IsCyclic (L ≃ₐ[K] L))
  -- the local faithfulness of `Φ`, in terms of the local norm subgroup
  have hloc' : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v :=
    fun v a => (hloc v a).trans
      (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a)
  -- the value of the local factor at every finite place
  have hfac : ∀ Q : HeightOneSpectrum (𝓞 K),
      Φ (NK.HassePrinciple.onePlace (Place.ofFinite Q)
          (NK.CFTLib.IdeleHasse.localImageAt (Place.ofFinite Q) b))
        = (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^
            (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q) :=
    fun Q => phi_onePlace_ofFinite_eq_frob_zpow (K := K) (L := L) b hadm hram hcong Φ hloc' hfrob Q
  -- every place outside the support of `(b)` contributes `1`
  have hhs : ∀ v : Place K,
      v ∉ ((NK.CFTLib.Arl.exps
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support.image Place.ofFinite) →
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v b)) = 1 := by
    intro v hv
    match v with
    | Sum.inl w => exact phi_onePlace_ofInfinite_eq_one (K := K) (L := L) b hpos Φ hloc' w
    | Sum.inr Q =>
        rw [hfac Q]
        have hQ : NK.CFTLib.Arl.exps
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K)) Q = 0 := by
          by_contra h
          exact hv (Finset.mem_image.mpr ⟨Q, Finsupp.mem_support_iff.mpr h, rfl⟩)
        rw [hQ, zpow_zero]
  -- the product formula
  have hmain := cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ hprin hnorm b
    ((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((b : Kˣ) : K))).support.image
      Place.ofFinite) hhs
  -- identify the product with the Artin symbol
  rw [cprod_localFactor_eq_artinSym (K := K) (L := L) hcomm Φ b hfac] at hmain
  exact hmain

end Work.SSGRoute.ZDataMup
