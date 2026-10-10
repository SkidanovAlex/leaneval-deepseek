import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_unramified
import Submission.NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs
import Submission.NK.NUV2.ARL.cyclotomic_isComplex
import Submission.NK.NUV2.ARL.norm_neg_of_one_negative_real_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert reciprocity for an arbitrary cyclotomic level at a real place

`NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_real` (still a target) treats the
cyclotomic level `L = K(ζ_q)` with `q` **prime**.  This file removes the primality hypothesis:
for **any** `m > 2` with `L = K(ζ_m)` and a **real** place `w` of `K`, a global element `b ∈ Kˣ`
which is a local norm at every place `v ≠ w` is a local norm at `w` as well.

## Strategy

The local norm group at `w` is the group of positive reals
(`NK.NUV2.ARL.mem_localNormSubgroup_ofInfinite_iff_pos`, generalised here to an arbitrary
modulus `m > 2`), so the assertion is `b_w > 0`.  Assume the contrary: `b_w < 0`.  Then

* `z := P(b)·(onePlace w b_w)⁻¹` is an idèle norm (componentwise: `b` is a local norm away from
  `w` by hypothesis, and the component at `w` is `1`), so it is killed by any idèlic Artin map;
* hence `art (P(b)) = art (onePlace w b_w)`, i.e. `art (onePlace w b_w) = 1` (`art` kills `Kˣ`);
* likewise `x := P(b)·(onePlace w (-1))` is an idèle norm (the component at `w` is `-b_w > 0`),
  so `art (onePlace w (-1)) = 1`.

The contradiction is a *sign computation*: choosing `c ∈ 𝓞 K` with `c ≡ 1 mod m`, `c < 0` at `w` and
`c > 0` at every other real place (`NK.CFTLib.Arl.exists_integral_sign_adjust`), the idèle
`onePlace w (-1)·P(c)` lies in the congruence subgroup `U` of modulus `m`
(`NK.NUV2.ARL.ideleArtin_eq_artinSym_of_mem`, reproved here in a clash-free form), so

`art (onePlace w (-1)) = artinSym ((c))`.

Finally, the cyclotomic character of `artinSym ((c))` is the absolute norm
`|N_{K/ℚ}(c)|` (`NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs`, generalised here from a prime
modulus to an arbitrary modulus `m`): since `c ≡ 1 mod m` we have `N_{K/ℚ}(c) ≡ 1 mod m` while
`N_{K/ℚ}(c) < 0` (exactly one negative real embedding,
`NK.NUV2.ARL.norm_lt_zero_of_neg_at_one_real_place`), so `|N_{K/ℚ}(c)| ≡ -1 mod m` and
`artinSym ((c)) ≠ 1` as soon as `m > 2`.  Contradiction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.HR

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The archimedean local norm group of `K(ζ_m)/K` at a real place, `m > 2` -/

/-- **Every infinite place of `K(ζ_m)` is complex, for `m > 2`** (generalising
`NK.NUV2.ARL.isComplex_infinitePlace_of_isCyclotomic` from a prime modulus to an arbitrary
modulus): a real place would give a ring homomorphism `ψ : L →+* ℝ`, and `ψ(ζ_m)` would be a real
`m`-th root of unity, i.e. `±1`; but `ζ_m ≠ ±1` for `m > 2`. -/
theorem isComplex_infinitePlace_of_isCyclotomic_neZero {m : ℕ} [NeZero m] (hm : 2 < m)
    [IsCyclotomicExtension {m} K L] (v : InfinitePlace L) : v.IsComplex := by
  rcases v.isReal_or_isComplex with hw | hw
  · exfalso
    have hφR : ComplexEmbedding.IsReal v.embedding := (InfinitePlace.isReal_iff).mp hw
    set ψ : L →+* ℝ := hφR.embedding with hψ
    have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta m K L) m :=
      IsCyclotomicExtension.zeta_spec m K L
    have h1 : ψ (IsCyclotomicExtension.zeta m K L) ^ m = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have habs : |ψ (IsCyclotomicExtension.zeta m K L)| = 1 := by
      refine (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by omega : m ≠ 0)).mp ?_
      rw [← abs_pow, h1, abs_one]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · have hz : IsCyclotomicExtension.zeta m K L = 1 := ψ.injective (by rw [h, map_one])
      exact hζ.ne_one (by omega) hz
    · have hz : IsCyclotomicExtension.zeta m K L = -1 :=
        ψ.injective (by rw [h, map_neg, map_one])
      have h2 : (IsCyclotomicExtension.zeta m K L) ^ 2 = 1 := by rw [hz]; ring
      have hdvd : m ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp h2
      exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  · exact hw

/-- **The local norm group at a real place of a cyclotomic level is the set of positive elements**
(arbitrary modulus `m > 2`).  This is
`NK.NUV2.ARL.mem_localNormSubgroup_ofInfinite_iff_pos` with the primality hypothesis removed. -/
theorem mem_localNormSubgroup_ofInfinite_iff_pos_neZero [IsGalois K L] {m : ℕ} [NeZero m]
    (hm : 2 < m) [IsCyclotomicExtension {m} K L] (w : InfinitePlace K) (hw : w.IsReal)
    (x : (w.Completion)ˣ) :
    x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) ↔ NK.CFTLib.Arl.PosAtReal w x := by
  classical
  obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (K := L) w
  have hlies : W.LiesOver w := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq W w).mpr hW
  have hcompl : W.IsComplex := isComplex_infinitePlace_of_isCyclotomic_neZero (K := K) hm W
  have hsup : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofInfinite w) =
      (@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ W w hlies).range := by
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
    refine le_antisymm (iSup_le fun (w' : {w' : InfinitePlace L // w'.LiesOver w}) => ?_)
      (le_iSup_of_le ⟨W, hlies⟩ le_rfl)
    haveI : w'.1.LiesOver w := w'.2
    rw [NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := w'.1)
        hw (isComplex_infinitePlace_of_isCyclotomic_neZero (K := K) hm w'.1),
      NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := W) hw hcompl]
  rw [hsup, NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := W)
    hw hcompl]
  constructor
  · intro hx hw'
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map] at hx
    have h : hw' = hw := Subsingleton.elim _ _
    rw [h]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (x : w.Completion)
    exact hx
  · intro hx
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (x : w.Completion)
    exact hx hw


/-! ## The idèlic Artin map of a cyclotomic level, with its congruence subgroup exposed -/

/-- The `Crux` input of the idèlic Artin map from the ideal-theoretic reciprocity law (local copy of
`NK.NUV2.ARL.killsPrincipal_of_artinKillsPrincipal`: the module
`Submission.NK.NUV2.ARL.artinSym_principal_of_primeIdele` cannot be imported here because it
clashes with `NK.CFTLib.IdeleHasse.localGlobalArtinSetup`). -/
theorem crux_of_artinKillsPrincipal [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U) :
    NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U :=
  fun b hb =>
    NK.CFTLib.Arl.artinSym_spanSingleton_eq_one hcomm m hm hram hprinc b
      ((hU.2 b).mp hb).1 ((hU.2 b).mp hb).2

/-- **Independence of the adjustment** (local copy of
`NK.NUV2.ARL.artinSym_idealOf_congr_aux`).  If `x * (b)` and `x * (b')` both lie in `U`, then the
Artin symbols of the fractional ideals of `x * (b)` and `x * (b')` agree. -/
theorem artinSym_idealOf_congr_aux [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (U : Subgroup (Idele K))
    (hstep : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U)
    {x : Idele K} {b b' : Kˣ}
    (hb : x * Idele.principalIdele K b ∈ U)
    (hb' : x * Idele.principalIdele K b' ∈ U) :
    NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b))
      = NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b')) := by
  have hmem : Idele.principalIdele K (b * b'⁻¹) ∈ U := by
    have h1 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹ ∈ U :=
      U.mul_mem hb (U.inv_mem hb')
    have h2 : (x * Idele.principalIdele K b) * (x * Idele.principalIdele K b')⁻¹
        = Idele.principalIdele K (b * b'⁻¹) := by
      rw [map_mul, map_inv, mul_inv_rev]
      rw [mul_comm (Idele.principalIdele K b')⁻¹ x⁻¹]
      rw [← mul_assoc, mul_assoc x (Idele.principalIdele K b) x⁻¹,
        mul_comm (Idele.principalIdele K b) x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    rwa [h2] at h1
  have hid : Idele.idealOf (x * Idele.principalIdele K b)
      = Idele.idealOf (x * Idele.principalIdele K b')
        * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b * b'⁻¹ : Kˣ) : K) := by
    have hbval : (b : K) = (b' : K) * ((b * b'⁻¹ : Kˣ) : K) := by
      rw [← Units.val_mul]
      congr 1
      rw [← mul_assoc, mul_comm b' b, mul_assoc, mul_inv_cancel, mul_one]
    rw [Idele.idealOf_mul, Idele.idealOf_mul, Idele.idealOf_principalIdele,
      Idele.idealOf_principalIdele, hbval, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ac_rfl
  rw [hid, NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm (Idele.idealOf_ne_zero _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)),
    hstep _ hmem, mul_one]

/-- **The value of the idèlic Artin map at any valid adjustment** (local copy of
`NK.NUV2.ARL.ideleArtin_eq_artinSym_of_mem`). -/
theorem ideleArtin_eq_artinSym_of_mem [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) {U : Subgroup (Idele K)}
    (hUc : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U)
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
    (x : Idele K) {b : Kˣ} (hb : x * Idele.principalIdele K b ∈ U) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj x
      = NK.CFTLib.Arl.artinSym hcomm (Idele.idealOf (x * Idele.principalIdele K b)) := by
  show NK.CFTLib.Arl.artinSym hcomm
      (Idele.idealOf (x * Idele.principalIdele K (NK.CFTLib.Arl.adjust U hadj x))) = _
  exact artinSym_idealOf_congr_aux hcomm U hUc
    (NK.CFTLib.Arl.adjust_spec U hadj x) hb

/-- **The idèlic Artin map of a cyclotomic level `L = K(ζ_m)` for an arbitrary modulus `m`**, with
its congruence subgroup `U`, the proof that `U` is the congruence subgroup of modulus `m`, and the
adjustment function exposed; at the modulus `m` the Frobenius normalisation is available at every
prime `𝔭` with `(m : 𝓞 K) ∉ 𝔭`. -/
theorem exists_artin_of_cyclotomic_neZero_with_adjust [IsGalois K L] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    ∃ (U : Subgroup (Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
      (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U)
      (art : Idele K →* Gal(L/K)),
      (∀ x : Idele K, art x = NK.CFTLib.Arl.ideleArtin hcomm U hadj x) ∧
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := m) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L m :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L m a ha hpos s e σ hs hfac hfrob
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hmpos
  obtain ⟨art, hagree, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hmpos hram hprinc
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hmpos hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hmpos z
    exact ⟨d, hUeq ▸ hd⟩
  exact ⟨U, hU, hadj, art, fun x => hagree x, hprin, hnorm, hfrob, hsurj⟩

/-- The fractional ideal of a one-place idèle at an **infinite** place is trivial. -/
theorem idealOf_onePlace_ofInfinite (w : InfinitePlace K) (y : (w.Completion)ˣ) :
    Idele.idealOf (NK.HassePrinciple.onePlace (Place.ofInfinite w) y) = 1 := by
  rw [Idele.idealOf_eq_one_iff, Idele.mem_integralIdeles]
  intro v hv
  rw [Place.isFinite_iff] at hv
  obtain ⟨q, rfl⟩ := hv
  rw [NK.HassePrinciple.onePlace_apply_ne (by
    simpa using Place.ofInfinite_ne_ofFinite w q)]
  exact Subgroup.one_mem _

/-! ## The cyclotomic character of the Artin symbol of a principal ideal (arbitrary modulus) -/

/-- **A Frobenius at an unramified prime raises `ζ_m` to the `N𝔭`-th power** (arbitrary modulus
`m`): the general-modulus form of `NK.NUV2.ARL.autToPow_frobAtPrime_eq_absNorm_zmod`. -/
lemma autToPow_frobAtPrime_eq_absNorm_zmod_neZero [IsGalois K L] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hs : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec m K L)
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : (ZMod m)ˣ) : ZMod m)
      = (Ideal.absNorm 𝔭.asIdeal : ZMod m) := by
  classical
  have hfrob : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
    rw [NK.Chebotarev.frobAtPrime,
      dif_pos (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) 𝔭)]
    exact (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) 𝔭).choose_spec
  have hpow := NK.CFTLib.ARL.isFrobAtPrime_zeta (K := K) (L := L) m 𝔭
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) hs hfrob
  have h := NK.CFTLib.ARL.autToPow_eq_of_pow_eq (K := K)
    (IsCyclotomicExtension.zeta_spec m K L) (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
    (Nat.card (𝓞 K ⧸ 𝔭.asIdeal)) hpow
  rw [h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **The cyclotomic character of the Artin symbol of a principal ideal `(c)`** is the absolute norm
`|N_{K/ℚ}(c)|`, for an arbitrary modulus `m` (the general-modulus form of
`NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs`; the only change is that the computation is
carried out in the group of units `(ZMod m)ˣ`, where negative exponents make sense, and cast to
`ZMod m` at the end using the non-negativity of the exponent vector of an integral ideal). -/
theorem autToPow_artinSym_spanSingleton_natAbs_neZero [IsGalois K L] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (c : 𝓞 K) (hc : c ≠ 0)
    (hcop : ∀ p : NK.Chebotarev.PrimeIdeal K, p.asIdeal ∣ Ideal.span {c} →
      (m : 𝓞 K) ∉ p.asIdeal) :
    ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec m K L)
        (NK.CFTLib.Arl.artinSym hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K))) : (ZMod m)ˣ) : ZMod m)
      = ((Algebra.norm ℤ c).natAbs : ZMod m) := by
  classical
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K) with hA
  set Z : HeightOneSpectrum (𝓞 K) →₀ ℤ := NK.CFTLib.Arl.exps A with hZ
  have hR : (c : K) ≠ 0 := fun h => hc (RingOfIntegers.coe_injective (by
    simpa [RingOfIntegers.coe_eq_algebraMap] using h))
  have hAcoe : A = (Ideal.span {c} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hA, FractionalIdeal.coeIdeal_span_singleton, RingOfIntegers.coe_eq_algebraMap]
  have hAne : A ≠ 0 := by rw [hA, FractionalIdeal.spanSingleton_ne_zero_iff]; exact hR
  have hI : Ideal.span {c} ≠ 0 := fun h => hc (Ideal.span_singleton_eq_bot.mp h)
  have hZc : ∀ v, Z v = FractionalIdeal.count K v A := by
    intro v; rw [hZ, NK.CFTLib.Arl.exps_apply]
  have hZnn : ∀ v, 0 ≤ Z v := by
    intro v
    rw [hZc v, hAcoe]
    exact FractionalIdeal.count_coe_nonneg K v (Ideal.span {c})
  have hfin : A = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hAne]
    apply finprod_congr
    intro v
    rw [hZc]
  have hfins : ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v)
      = ∏ v ∈ Z.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v) := by
    rw [finprod_eq_finsetProd_of_mulSupport_subset (s := Z.support)]
    intro v hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hZ0
    rw [Function.mem_mulSupport] at hv
    exact hv (by rw [hZ0]; exact zpow_zero _)
  have hcoe : ∏ v ∈ Z.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v)
      = ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (nonZeroDivisors (𝓞 K)) K
          (∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat),
        map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
          (fun v => v.asIdeal ^ (Z v).toNat) Z.support]
    apply Finset.prod_congr rfl
    intro v _
    rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    conv_lhs => rw [← Int.toNat_of_nonneg (hZnn v)]
    rw [zpow_natCast]
  have hA' : A = ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by rw [hfin, hfins, hcoe]
  have hideal : Ideal.span {c} = ∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat := by
    refine FractionalIdeal.coeIdeal_injective (K := K) ?_
    show (Ideal.span {c} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [← hAcoe, hA']
  have habs : ∏ v ∈ Z.support, (Ideal.absNorm v.asIdeal) ^ (Z v).toNat
      = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton c, hideal, map_prod]
    apply Finset.prod_congr rfl
    intro v hv
    rw [map_pow]
  have hdiv : ∀ 𝔭 ∈ Z.support, 𝔭.asIdeal ∣ Ideal.span {c} := by
    intro 𝔭 h𝔭
    have hZne : Z 𝔭 ≠ 0 := Finsupp.mem_support_iff.mp h𝔭
    have hcnt : FractionalIdeal.count K 𝔭 A ≠ 0 := by rw [← hZc 𝔭]; exact hZne
    rw [hAcoe] at hcnt
    have hcnt' : (Associates.mk 𝔭.asIdeal).count
        (Associates.mk (Ideal.span {c})).factors ≠ 0 := by
      have h2 := FractionalIdeal.count_coe K 𝔭 hI
      rw [h2] at hcnt
      exact_mod_cast hcnt
    exact (Associates.count_ne_zero_iff_dvd (a := Ideal.span {c}) hI 𝔭.irreducible).mp hcnt'
  have hprime : ∀ 𝔭 ∈ Z.support, (m : 𝓞 K) ∉ 𝔭.asIdeal := fun 𝔭 h𝔭 => hcop 𝔭 (hdiv 𝔭 h𝔭)
  let galC : CommMonoid Gal(L/K) := NK.CFTLib.Arl.galCommMonoid hcomm
  let ψ : Gal(L/K) →* ZMod m := (Units.coeHom (ZMod m)).comp
    (IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec m K L))
  have hcharψ : ∀ 𝔭 ∈ Z.support,
      ψ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) = (Ideal.absNorm 𝔭.asIdeal : ZMod m) := by
    intro 𝔭 h𝔭
    exact autToPow_frobAtPrime_eq_absNorm_zmod_neZero (K := K) (L := L) m 𝔭 (hprime 𝔭 h𝔭)
  have hstep : ψ (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A)
      = ∏ 𝔭 ∈ Z.support, ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m) ^ (Z 𝔭).toNat := by
    rw [NK.CFTLib.Arl.artinSym]
    rw [Finsupp.prod_of_support_subset (f := Z) (s := Z.support) (le_refl _)
      (g := fun 𝔭 e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro 𝔭 h𝔭
    have h1 : (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ (Z 𝔭)
        = (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ ((Z 𝔭).toNat) := by
      conv_lhs => rw [← Int.toNat_of_nonneg (hZnn 𝔭)]
      rw [zpow_natCast]
    rw [h1, map_pow, hcharψ 𝔭 h𝔭]
  have hfinal : (∏ 𝔭 ∈ Z.support, ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m) ^ (Z 𝔭).toNat)
      = ((Algebra.norm ℤ c).natAbs : ZMod m) := by
    calc ∏ 𝔭 ∈ Z.support, ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m) ^ (Z 𝔭).toNat
        = ∏ 𝔭 ∈ Z.support,
            (((Ideal.absNorm 𝔭.asIdeal) ^ (Z 𝔭).toNat : ℕ) : ZMod m) := by
          apply Finset.prod_congr rfl
          intro 𝔭 _
          rw [Nat.cast_pow]
      _ = ((∏ 𝔭 ∈ Z.support, (Ideal.absNorm 𝔭.asIdeal) ^ (Z 𝔭).toNat : ℕ) : ZMod m) := by
          rw [Nat.cast_prod]
      _ = ((Algebra.norm ℤ c).natAbs : ZMod m) := by rw [habs]
  change ψ (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A)
    = ((Algebra.norm ℤ c).natAbs : ZMod m)
  rw [hstep, hfinal]

/-! ## The main theorem -/

/-- **Hilbert reciprocity for a cyclotomic level at a real place.**  For `L = K(ζ_m)` with `m > 2`
and a **real** place `w` of `K`, a global element `b ∈ Kˣ` which is a local norm at every place
`v ≠ w` is a local norm at `w`.  (At such a place the local norm group is the group of positive
reals, so the statement is `b > 0` at `w`.) -/
theorem isCyclotomic_onePlace_real
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (hm : 2 < m) [IsCyclotomicExtension {m} K L]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) (b : Kˣ)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ NK.GlobalCFT.Place.ofInfinite w →
      NK.CFTLib.localImageHom v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.localImageHom (NK.GlobalCFT.Place.ofInfinite w) b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hmpos : 0 < m := by omega
  -- the archimedean local norm group at `w` is the group of positive reals
  refine (mem_localNormSubgroup_ofInfinite_iff_pos_neZero (K := K) (L := L) hm w hw _).mpr ?_
  -- suppose `b` is negative at `w`
  by_contra hcon
  set xw : (w.Completion)ˣ := NK.CFTLib.localImageHom (NK.GlobalCFT.Place.ofInfinite w) b
    with hxwdef
  have hneg : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      ((xw : (w.Completion)ˣ) : w.Completion) < 0 := by
    have hnn : ¬ (0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((xw : (w.Completion)ˣ) : w.Completion)) := fun hpos =>
      hcon (fun hw' => by
        rw [show hw' = hw from Subsingleton.elim _ _]
        exact hpos)
    have hne0 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((xw : (w.Completion)ˣ) : w.Completion) ≠ 0 := by
      intro h0
      exact Units.ne_zero xw ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective
        (by rw [h0, map_zero]))
    exact lt_of_le_of_ne (not_lt.mp hnn) hne0
  -- the idèle `-1` at the place `w`
  set nw : (w.Completion)ˣ := NK.CFTLib.localImageHom (NK.GlobalCFT.Place.ofInfinite w) (-1 : Kˣ)
    with hnwdef
  have hnwval : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      ((nw : (w.Completion)ˣ) : w.Completion) = -1 := by
    rw [hnwdef, NK.CFTLib.localImageHom_apply, Units.coe_map]
    simp
  -- ### the idèlic Artin map of the level `m`
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    hcomm_of_isCyclotomic_neZero (K := K) (L := L) m
  obtain ⟨U, hU, hadj, art, hagree, hprin, hnorm, hfrob, -⟩ :=
    exists_artin_of_cyclotomic_neZero_with_adjust (K := K) (L := L) m hcomm
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := m) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L m :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L m a ha hpos s e σ hs hfac hfrob
  have hUc : NK.CFTLib.Arl.Crux (K := K) (L := L) hcomm U :=
    crux_of_artinKillsPrincipal hcomm m hmpos hram hprinc U hU
  -- ### Step 1: `art (onePlace w b_w) = 1`
  have hz1mem : Idele.principalIdele K b *
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw)⁻¹
      ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro v
    by_cases hv : v = NK.GlobalCFT.Place.ofInfinite w
    · subst hv
      refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      have hxweq : (Idele.principalIdele K b) (NK.GlobalCFT.Place.ofInfinite w) = xw := by
        rw [hxwdef, NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply]
        rfl
      rw [Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_self, hxweq,
        mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      rw [Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_ne hv, inv_one,
        mul_one, Idele.principalIdele_apply]
      exact h v hv
  have hart_xw : art (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw) = 1 := by
    have hz1art : art (Idele.principalIdele K b *
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw)⁻¹) = 1 := by
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hz1mem
      have hzy : Idele.principalIdele K b *
          (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw)⁻¹
          = Idele.normIdeleHom K L y := by
        ext v
        rw [Idele.normIdeleHom_apply]
        exact congrArg Units.val (hy v)
      rw [hzy]
      exact hnorm y
    have h2 : art (Idele.principalIdele K b *
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw)⁻¹)
        = (art (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) xw))⁻¹ := by
      rw [map_mul, map_inv, hprin b, one_mul]
    rw [hz1art] at h2
    exact inv_eq_one.mp h2.symm
  -- ### Step 2: `art (onePlace w (-1)) = 1`, using `b_w < 0`
  have hxwnw : xw * nw ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofInfinite w) := by
    refine (mem_localNormSubgroup_ofInfinite_iff_pos_neZero (K := K) (L := L) hm w hw
      (xw * nw)).mpr ?_
    intro hw'
    rw [show hw' = hw from Subsingleton.elim _ _]
    rw [Units.val_mul, map_mul, hnwval]
    linarith [hneg]
  have hz2mem : Idele.principalIdele K b *
      NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw
      ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro v
    by_cases hv : v = NK.GlobalCFT.Place.ofInfinite w
    · subst hv
      refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      have hxweq : (Idele.principalIdele K b) (NK.GlobalCFT.Place.ofInfinite w) = xw := by
        rw [hxwdef, NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply]
        rfl
      rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_self, hxweq]
      exact hxwnw
    · refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_ne hv, mul_one,
        Idele.principalIdele_apply]
      exact h v hv
  have hart_nw : art (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw) = 1 := by
    have hz2art : art (Idele.principalIdele K b *
        NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw) = 1 := by
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hz2mem
      have hzy : Idele.principalIdele K b *
          NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw
          = Idele.normIdeleHom K L y := by
        ext v
        rw [Idele.normIdeleHom_apply]
        exact congrArg Units.val (hy v)
      rw [hzy]
      exact hnorm y
    have h2 : art (Idele.principalIdele K b *
        NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw)
        = art (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw) := by
      rw [map_mul, hprin b, one_mul]
    rw [h2] at hz2art
    exact hz2art
  -- ### Step 3: the sign adjustment `c`
  let r : InfinitePlace K → ℝ := fun w' => if h : w'.IsReal then (if w' = w then -1 else 1) else 1
  have hr : ∀ w' : InfinitePlace K, w'.IsReal → r w' ≠ 0 := by
    intro w' hw'
    have h : r w' = -1 ∨ r w' = 1 := by
      simp only [r]
      rw [dif_pos hw']
      split_ifs with h1
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases h with h | h <;> rw [h] <;> norm_num
  obtain ⟨u, hu⟩ := NK.CFTLib.Arl.exists_integral_sign_adjust K m hmpos r hr
  have hcu_neg : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (algebraMap K w.Completion ((1 : K) + m * ((u : 𝓞 K) : K))) < 0 := by
    have h := hu w hw
    have hrw : r w = -1 := by
      simp only [r]
      rw [dif_pos hw]
      simp
    rw [hrw] at h
    linarith
  have hcu_pos : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w →
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw')
        (algebraMap K w'.Completion ((1 : K) + m * ((u : 𝓞 K) : K))) := by
    intro w' hw' hne'
    have h := hu w' hw'
    have hrw' : r w' = 1 := by
      simp only [r]
      rw [dif_pos hw']
      simp [hne']
    rw [hrw'] at h
    simpa using h
  have hne : (1 : K) + m * ((u : 𝓞 K) : K) ≠ 0 := by
    intro h0
    have h := hcu_neg
    rw [h0] at h
    simp at h
  set cU : Kˣ := Units.mk0 ((1 : K) + m * ((u : 𝓞 K) : K)) hne with hcUdef
  set c : 𝓞 K := 1 + m * u with hcdef
  have hcK : ((c : 𝓞 K) : K) = (1 : K) + m * ((u : 𝓞 K) : K) := by
    rw [hcdef]
    push_cast
    ring
  have hc_ne : c ≠ 0 := by
    intro h0
    have h1 : ((c : 𝓞 K) : K) = 0 := by rw [h0]; simp
    exact hne (by rw [← hcK]; exact h1)
  have hcU_coe : (cU : K) = ((c : 𝓞 K) : K) := by
    rw [hcUdef, hcK, Units.val_mk0]
  -- ### Step 3a: `onePlace w (-1) * P(c) ∈ U`
  have hmemU : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
      Idele.principalIdele K cU ∈ U := by
    refine (hU.1 (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
      Idele.principalIdele K cU)).mpr ⟨?_, ?_⟩
    · intro 𝔭 h𝔭
      have h1 : (((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
            Idele.principalIdele K cU) (Place.ofFinite 𝔭) : (𝔭.adicCompletion K)ˣ) :
            𝔭.adicCompletion K)
          = algebraMap K (𝔭.adicCompletion K) ((1 : K) + m * ((u : 𝓞 K) : K)) := by
        rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_ne (Ne.symm
            (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w 𝔭)), one_mul,
          Idele.principalIdele_apply, hcUdef, Units.coe_map, Units.val_mk0]
        rfl
      rw [h1]
      have hdec : algebraMap K (𝔭.adicCompletion K) ((1 : K) + m * ((u : 𝓞 K) : K)) - 1
          = ((m : ℕ) : 𝔭.adicCompletion K)
            * algebraMap K (𝔭.adicCompletion K) ((u : 𝓞 K) : K) := by
        rw [map_add, map_mul, map_one, map_natCast]
        ring
      rw [hdec, map_mul]
      calc Valued.v (((m : ℕ) : 𝔭.adicCompletion K))
            * Valued.v (algebraMap K (𝔭.adicCompletion K) ((u : 𝓞 K) : K))
          ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) * 1 :=
            mul_le_mul_of_nonneg_left (NK.CFTLib.Arl.val_algebraMap_units_le_one 𝔭 u) zero_le
        _ = Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := mul_one _
    · intro w'
      by_cases hwr : w'.IsReal
      · intro hw'
        rw [show (InfinitePlace.Completion.ringEquivRealOfIsReal hw') =
            (InfinitePlace.Completion.ringEquivRealOfIsReal hwr) from
          congrArg _ (Subsingleton.elim hw' hwr)]
        by_cases hw'w : w' = w
        · subst w'
          have hcomp : ((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
                Idele.principalIdele K cU) (NK.GlobalCFT.Place.ofInfinite w) :
                (w.Completion)ˣ)
              = nw * Units.map (algebraMap K w.Completion : K →* w.Completion)
                  (Units.mk0 ((1 : K) + m * ((u : 𝓞 K) : K)) hne) := by
            rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_self, Idele.principalIdele_apply,
              hcUdef]
          have hprodt : (((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
                Idele.principalIdele K cU) (NK.GlobalCFT.Place.ofInfinite w) :
                (w.Completion)ˣ) : w.Completion)
              = (nw : w.Completion) *
                  (algebraMap K w.Completion ((1 : K) + m * ((u : 𝓞 K) : K))) := by
            rw [hcomp, Units.val_mul, Units.coe_map, Units.val_mk0]
            rfl
          rw [hprodt, map_mul, hnwval,
            show (InfinitePlace.Completion.ringEquivRealOfIsReal hwr)
                = (InfinitePlace.Completion.ringEquivRealOfIsReal hw) from
              congrArg _ (Subsingleton.elim hwr hw)]
          linarith [hcu_neg]
        · have hcomp : ((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
                Idele.principalIdele K cU) (NK.GlobalCFT.Place.ofInfinite w') :
                (w'.Completion)ˣ)
              = Units.map (algebraMap K w'.Completion : K →* w'.Completion)
                  (Units.mk0 ((1 : K) + m * ((u : 𝓞 K) : K)) hne) := by
            rw [Idele.mul_apply, NK.HassePrinciple.onePlace_apply_ne (by
              intro hcontra
              exact hw'w (NK.GlobalCFT.Place.ofInfinite_inj.mp hcontra)), one_mul,
              Idele.principalIdele_apply, hcUdef]
          have hprodt : (((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
                Idele.principalIdele K cU) (NK.GlobalCFT.Place.ofInfinite w') :
                (w'.Completion)ˣ) : w'.Completion)
              = algebraMap K w'.Completion ((1 : K) + m * ((u : 𝓞 K) : K)) := by
            rw [hcomp, Units.coe_map, Units.val_mk0]
            rfl
          rw [hprodt]
          exact hcu_pos w' hwr hw'w
      · exact fun hw' => absurd hw' hwr
  -- ### Step 3b: the idèle `idealOf` of that element is `(c)`
  have hid : Idele.idealOf (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw *
      Idele.principalIdele K cU)
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K) := by
    rw [Idele.idealOf_mul, idealOf_onePlace_ofInfinite, one_mul, Idele.idealOf_principalIdele,
      hcU_coe]
  have hart_eq : art (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) nw)
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K)) := by
    rw [hagree, ideleArtin_eq_artinSym_of_mem hcomm hUc hadj _ hmemU, hid]
  -- ### Step 3c: the Artin symbol of `(c)` is non-trivial
  have hcop : ∀ p : NK.Chebotarev.PrimeIdeal K, p.asIdeal ∣ Ideal.span {c} →
      (m : 𝓞 K) ∉ p.asIdeal := by
    intro p hp hmem
    have hle : Ideal.span {c} ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
    have hc_in : c ∈ p.asIdeal := hle (Ideal.mem_span_singleton_self c)
    have hm_in : (m : 𝓞 K) ∈ p.asIdeal := hmem
    have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
      have h2 : c - m * u ∈ p.asIdeal :=
        p.asIdeal.sub_mem hc_in (p.asIdeal.mul_mem_right u hm_in)
      have h3 : c - m * u = 1 := by rw [hcdef]; ring
      rwa [h3] at h2
    exact p.isPrime.ne_top (p.asIdeal.eq_top_iff_one.mpr h1)
  have hchar := autToPow_artinSym_spanSingleton_natAbs_neZero (K := K) (L := L) m hcomm c hc_ne hcop
  have hnormcong : ((Algebra.norm ℤ c : ℤ) : ZMod m) = 1 := by
    have hc1 : c - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      have h3 : c - 1 = (m : 𝓞 K) * u := by rw [hcdef]; ring
      rw [h3]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self _)
    have hdvd : (m : ℤ) ∣ Algebra.norm ℤ c - 1 :=
      Ideal.mem_span_singleton.mp (NK.CFTLib.ARL.norm_sub_one_mem_span m c hc1)
    have hmodeq : Algebra.norm ℤ c ≡ 1 [ZMOD (m : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← neg_sub]
      exact dvd_neg.mpr hdvd
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    exact hmodeq
  have hnormneg : Algebra.norm ℤ c < 0 := by
    have hneK' : ((c : 𝓞 K) : K) ≠ 0 := by rw [hcK]; exact hne
    have hnegK : (InfinitePlace.embedding_of_isReal hw) ((c : 𝓞 K) : K) < 0 := by
      rw [show (InfinitePlace.embedding_of_isReal hw) ((c : 𝓞 K) : K)
          = (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion ((c : 𝓞 K) : K)) from by
        simp [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
          InfinitePlace.embedding_of_isReal]]
      rw [hcK]
      exact hcu_neg
    have hposK : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), w' ≠ w →
        0 < (InfinitePlace.embedding_of_isReal hw') ((c : 𝓞 K) : K) := by
      intro w' hw' hne'
      rw [show (InfinitePlace.embedding_of_isReal hw') ((c : 𝓞 K) : K)
          = (InfinitePlace.Completion.ringEquivRealOfIsReal hw')
              (algebraMap K w'.Completion ((c : 𝓞 K) : K)) from by
        simp [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
          InfinitePlace.embedding_of_isReal]]
      rw [hcK]
      exact hcu_pos w' hw' hne'
    have h1 : Algebra.norm ℚ ((c : 𝓞 K) : K) < 0 :=
      NK.NUV2.ARL.norm_lt_zero_of_neg_at_one_real_place (K := K) ((c : 𝓞 K) : K) hneK' w hw
        hnegK hposK
    rw [← Algebra.coe_norm_int c] at h1
    exact_mod_cast h1
  have hNabs : (((Algebra.norm ℤ c).natAbs : ℕ) : ZMod m) = -1 := by
    have h1 : ((Algebra.norm ℤ c).natAbs : ℤ) = -(Algebra.norm ℤ c) := by
      have h := Int.eq_neg_natAbs_of_nonpos (le_of_lt hnormneg)
      linarith
    calc (((Algebra.norm ℤ c).natAbs : ℕ) : ZMod m)
        = ((((Algebra.norm ℤ c).natAbs : ℤ)) : ZMod m) := by simp
      _ = ((-(Algebra.norm ℤ c) : ℤ) : ZMod m) := by rw [h1]
      _ = -((Algebra.norm ℤ c : ℤ) : ZMod m) := by simp
      _ = -1 := by rw [hnormcong]
  have hσne : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K)) ≠ 1 := by
    intro h1
    have h2 : ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec m K L)
        (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((c : 𝓞 K) : K))) :
          (ZMod m)ˣ) : ZMod m) = 1 := by
      rw [h1, map_one]
      rfl
    rw [hchar, hNabs] at h2
    have h3 : ((2 : ℤ) : ZMod m) = 0 := by
      have hthis := congrArg (fun x : ZMod m => x + 1) h2
      rw [neg_add_cancel] at hthis
      have h2' : (1 : ZMod m) + 1 = (2 : ZMod m) := by ring
      rw [h2'] at hthis
      rw [show ((2 : ℤ) : ZMod m) = (2 : ZMod m) from by simp]
      exact hthis.symm
    have hdvd : (m : ℤ) ∣ 2 := by
      have hmod : (2 : ℤ) ≡ 0 [ZMOD (m : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff 2 0 m).mp (by rw [h3]; simp)
      exact Int.modEq_zero_iff_dvd.mp hmod
    have hdvd2 : m ∣ 2 := by exact_mod_cast hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd2) (by omega)
  -- ### Step 4: contradiction
  exact hσne (hart_eq ▸ hart_nw)

/-- **The prime-modulus case**, deduced from the arbitrary-modulus theorem: this is the statement
of `NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_real`. -/
theorem localImage_mem_localNormSubgroup_of_isCyclotomic_of_real_prime
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : ℕ) [Fact q.Prime] (hq : 2 < q) [IsCyclotomicExtension {q} K L]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) (b : Kˣ)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ NK.GlobalCFT.Place.ofInfinite w →
      NK.CFTLib.localImageHom v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.localImageHom (NK.GlobalCFT.Place.ofInfinite w) b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) :=
  isCyclotomic_onePlace_real (K := K) (L := L) q hq w hw b h

end NK.CFTLib.HR
