import Mathlib
import Submission.Work.SSGRoute.CycLevel.routeA_defs
import Submission.Work.SSGRoute.CycLevel.kummerCyc_data
import Submission.Work.SSGRoute.CycLevel.cycM_fullLocal
import Submission.Work.SSGRoute.CycLevel.LevelData
import Submission.Work.SSGRoute.glue_involution_place
import Submission.NK.Chebotarev.Basic
import Submission.NK.ChebotarevGeneral.Defs
import Submission.Work.SSGRoute.isPrimitiveRoot_quotient_mk
import Submission.Work.SSGRoute.exists_level_residueDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.CycLevel

open scoped NumberField

/-- **The prime `ℓ` of route A.**

Let `q` be an odd prime, `e > 0` and `m > 0` an integer which is not a `q`-th power.  Given the
Kummer field `N = ℚ(ζ_{q^e}, m^{1/q})` with a primitive `q ^ e`-th root of unity `ζ`, an element
`α` with `α ^ q = m`, and an automorphism `σ` of `N` over `ℚ` fixing `ζ` and sending `α` to
`ζ ^ (q ^ (e - 1)) * α`, and given any integer `D`, there is a rational prime `ℓ` such that

* `q ^ e ∣ ℓ - 1`,
* `ℓ ∤ D` and `ℓ ∤ m`, and
* `m` is not a `q`-th power in `(ZMod ℓ)ˣ`.

Proof: Čebotarev's existence theorem for `N/ℚ` (`NK.ChebotarevGeneral.ChebotarevInfinite`) applied
to `σ` produces infinitely many primes; choose `ℓ` larger than the finitely many bad primes.  The
Frobenius congruence at such a prime upgrades to an equality on the root of unity `ζ`
(`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, using `ℓ ≠ q`), giving `ζ ^ (ℓ - 1) = 1` and hence
`q ^ e ∣ ℓ - 1` (`IsPrimitiveRoot.pow_eq_one_iff_dvd`).  Finally, if `m` were a `q`-th power
`a ^ q` modulo `ℓ`, reducing `σ α = ζ ^ (q ^ (e-1)) * α` at a prime `P ∣ (ℓ)` of `𝓞 N` would give
`ζ̄_q = (ᾱ) ^ (ℓ - 1) = (ᾱ ^ q) ^ ((ℓ-1)/q) = a ^ (ℓ - 1) = 1` (Fermat in `𝔽_ℓ`), contradicting
the fact that `ζ̄_q` is a primitive `q`-th root of unity in the residue field
(`Work.SSGRoute.isPrimitiveRoot_quotient_mk`, using `ℓ ≠ q`). -/
theorem exists_prime_notPower_mod (q e m : ℕ) (hq : q.Prime) (hq2 : 2 < q) (he : 0 < e)
    (hm : 0 < m) (hmq : ¬ ∃ m' : ℕ, 0 < m' ∧ m = m' ^ q) (D : ℤ) (hD : D ≠ 0)
    (N : Type) [Field N] [NumberField N] [Algebra ℚ N] [FiniteDimensional ℚ N] [IsGalois ℚ N]
    (ζ α : N) (σ : N ≃ₐ[ℚ] N) (hζ : IsPrimitiveRoot ζ (q ^ e))
    (hα : α ^ q = algebraMap ℚ N (m : ℚ)) (hσζ : σ ζ = ζ)
    (hσα : σ α = ζ ^ (q ^ (e - 1)) * α) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ q ^ e ∣ ℓ - 1 ∧ ¬ (ℓ : ℤ) ∣ D ∧ ¬ (ℓ : ℤ) ∣ (m : ℤ) ∧
      (¬ ∃ x : (ZMod ℓ)ˣ, (x : ZMod ℓ) ^ q = (m : ZMod ℓ)) := by
  classical
  -- ## Step 1: a large rational prime whose Frobenius in `N/ℚ` is `σ`
  have hinf : (NK.ChebotarevGeneral.frobSet (K := ℚ) (N := N) σ).Infinite :=
    Work.SSGRoute.chebotarevInfinite_type0 (K := ℚ) (N := N) σ
  have hinj : Function.Injective
      (fun p : NK.Chebotarev.PrimeIdeal ℚ => Rat.HeightOneSpectrum.natGenerator p) := by
    intro p p' h
    have h' : Rat.HeightOneSpectrum.primesEquiv p = Rat.HeightOneSpectrum.primesEquiv p' := by
      apply Subtype.ext
      show (Rat.HeightOneSpectrum.primesEquiv p : ℕ) = (Rat.HeightOneSpectrum.primesEquiv p' : ℕ)
      rw [show (Rat.HeightOneSpectrum.primesEquiv p : ℕ)
            = Rat.HeightOneSpectrum.natGenerator p from rfl,
        show (Rat.HeightOneSpectrum.primesEquiv p' : ℕ)
            = Rat.HeightOneSpectrum.natGenerator p' from rfl]
      exact h
    exact Rat.HeightOneSpectrum.primesEquiv.injective h'
  have hinf' : (Rat.HeightOneSpectrum.natGenerator ''
      NK.ChebotarevGeneral.frobSet (K := ℚ) (N := N) σ).Infinite :=
    hinf.image (fun _ _ _ _ h => hinj h)
  set B : ℕ := max (max (q + 1) (m + 1)) (D.natAbs + 1) with hB
  obtain ⟨ℓ, hℓmem, hℓgt⟩ := hinf'.exists_gt B
  obtain ⟨p, hp_mem, hp_gen⟩ := hℓmem
  have hℓprime : ℓ.Prime := hp_gen ▸ Rat.HeightOneSpectrum.prime_natGenerator p
  have hqℓ : q < ℓ := by
    have : q + 1 ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  have hmℓ : m < ℓ := by
    have : m + 1 ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hDℓ : D.natAbs < ℓ := by
    have : D.natAbs + 1 ≤ B := le_max_right _ _
    omega
  have hDabs : D.natAbs ≠ 0 := fun h => hD (Int.natAbs_eq_zero.mp h)
  have hℓnotm : ¬ (ℓ : ℤ) ∣ (m : ℤ) := by
    intro hdiv
    have h1 : ℓ ∣ m := by exact_mod_cast hdiv
    have h2 : ℓ ≤ m := Nat.le_of_dvd hm h1
    omega
  have hℓnotD : ¬ (ℓ : ℤ) ∣ D := by
    intro hdiv
    have h1 : (ℓ : ℤ).natAbs ∣ D.natAbs := Int.natAbs_dvd_natAbs.mpr hdiv
    rw [Int.natAbs_natCast] at h1
    have h2 : ℓ ≤ D.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hDabs) h1
    omega
  -- ## Step 2: unpack the Frobenius
  obtain ⟨P, hP, hfrobP⟩ := (NK.ChebotarevGeneral.mem_frobSet).mp hp_mem
  have hcardp : Nat.card (NumberField.RingOfIntegers ℚ ⧸ p.asIdeal) = ℓ := by
    rw [Work.SSGRoute.natCard_quotient_rat_primeIdeal p]; exact hp_gen
  -- `ℓ ∈ P`
  have hℓP : ((ℓ : ℕ) : 𝓞 N) ∈ P.asIdeal := by
    have h1 : (ℓ : 𝓞 ℚ) ∈ p.asIdeal :=
      (Work.SSGRoute.rat_primeIdeal_mem_iff p ℓ).mpr (by rw [hp_gen])
    have h2 : (ℓ : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by rwa [← hP.over]
    rw [Ideal.mem_under] at h2
    simpa using h2
  -- integral models of `ζ` and `α`
  obtain ⟨ζO, hζO⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 N) (R := ℤ) (B := N)).mp
    (hζ.isIntegral (pow_pos hq.pos e))
  have hζO' : IsPrimitiveRoot ζO (q ^ e) := by
    refine ⟨?_, ?_⟩
    · apply NumberField.RingOfIntegers.coe_injective
      rw [map_pow, map_one, hζO, hζ.pow_eq_one]
    · intro l hl
      refine (hζ.pow_eq_one_iff_dvd l).mp ?_
      rw [← hζO, ← map_pow, hl, map_one]
  have hζOpow : ζO ^ (q ^ e) = 1 := hζO'.pow_eq_one
  have hαint : IsIntegral ℤ α := by
    refine ⟨Polynomial.X ^ q - Polynomial.C (m : ℤ),
      Polynomial.monic_X_pow_sub_C _ (by omega : q ≠ 0), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, hα]
    rw [IsScalarTower.algebraMap_apply ℤ ℚ N]
    simp
  obtain ⟨αO, hαO⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 N) (R := ℤ) (B := N)).mp hαint
  have hqe_mem : ((q ^ e : ℕ) : 𝓞 N) ∉ P.asIdeal := by
    intro hmem
    have h1 : ((q ^ e : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by
      have h2 : ((q ^ e : ℕ) : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by
        rw [Ideal.mem_under]
        simpa using hmem
      rwa [← hP.over] at h2
    have h3 : Rat.HeightOneSpectrum.natGenerator p ∣ q ^ e :=
      (Work.SSGRoute.rat_primeIdeal_mem_iff p (q ^ e)).mp h1
    rw [hp_gen] at h3
    have h4 : ℓ ∣ q := hℓprime.dvd_of_dvd_pow h3
    rcases hq.eq_one_or_self_of_dvd ℓ h4 with h5 | h5
    · exact hℓprime.ne_one h5
    · omega
  -- ## Step 3: `q ^ e ∣ ℓ - 1`
  have hcongr : galRestrict (𝓞 ℚ) ℚ N (𝓞 N) σ ζO = ζO ^ ℓ := by
    have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
      (φ := (galRestrict (𝓞 ℚ) ℚ N (𝓞 N) σ).toAlgHom) (Q := P.asIdeal) hfrobP
      (ζ := ζO) (m := q ^ e) hζOpow hqe_mem
    rwa [← hP.over, hcardp] at h
  have hσζℓ : σ ζ = ζ ^ ℓ := by
    have h := congrArg (algebraMap (𝓞 N) N) hcongr
    rwa [map_pow, algebraMap_galRestrict_apply, hζO] at h
  have hdvd : q ^ e ∣ ℓ - 1 := by
    have h1 : ζ ^ (ℓ - 1) = 1 := by
      have h2 : ζ ^ ℓ = ζ ^ 1 := by rw [← hσζℓ, hσζ, pow_one]
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero e hq.ne_zero)
      have h3 : ζ ^ (ℓ - 1) = ζ ^ ℓ / ζ := by
        rw [eq_div_iff hζ0, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
      rw [h3, h2, pow_one, div_self hζ0]
    exact (hζ.pow_eq_one_iff_dvd (ℓ - 1)).mp h1
  refine ⟨ℓ, hℓprime, hdvd, hℓnotD, hℓnotm, ?_⟩
  -- ## Step 4: `m` is not a `q`-th power modulo `ℓ`
  haveI : NeZero ℓ := ⟨hℓprime.ne_zero⟩
  rintro ⟨x, hx⟩
  set n : ℕ := (x : ZMod ℓ).val with hn
  have hxval : ((n : ℕ) : ZMod ℓ) = (x : ZMod ℓ) := by
    rw [hn]; exact ZMod.natCast_zmod_val (x : ZMod ℓ)
  have hmZ : ((m : ℕ) : ZMod ℓ) ≠ 0 := by
    intro h0
    have h1 : ℓ ∣ m := (ZMod.natCast_eq_zero_iff m ℓ).mp h0
    exact hℓnotm (by exact_mod_cast h1)
  have hxq : ((n : ℕ) : ZMod ℓ) ^ q = ((m : ℕ) : ZMod ℓ) := by
    rw [hxval]; exact hx
  have hn0 : ((n : ℕ) : ZMod ℓ) ≠ 0 := by
    intro h0
    have h1 : ((n : ℕ) : ZMod ℓ) ^ q = 0 := by rw [h0]; exact zero_pow (by omega : q ≠ 0)
    rw [hxq] at h1
    exact hmZ h1
  have hdivq : (ℓ : ℤ) ∣ (m : ℤ) - (n : ℤ) ^ q := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub ((n : ℤ) ^ q) (m : ℤ) ℓ).mp ?_
    push_cast
    exact hxq
  have hfermat : (ℓ : ℤ) ∣ (n : ℤ) ^ (ℓ - 1) - 1 := by
    haveI : Fact ℓ.Prime := ⟨hℓprime⟩
    have h2 : ((n : ℕ) : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one hn0
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub (1 : ℤ) (((n : ℕ) ^ (ℓ - 1) : ℕ) : ℤ) ℓ).mp ?_
    push_cast
    rw [h2]
  -- ## Step 5: the residue field at `P`
  let κ := 𝓞 N ⧸ P.asIdeal
  haveI : Field κ := Ideal.Quotient.field P.asIdeal
  have hℓκ : ((ℓ : ℕ) : κ) = 0 := by
    rw [show ((ℓ : ℕ) : κ) = Ideal.Quotient.mk P.asIdeal (ℓ : 𝓞 N) from (map_natCast _ _).symm,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hℓP
  set ᾱ : κ := Ideal.Quotient.mk P.asIdeal αO with hᾱ
  set ζqO : 𝓞 N := ζO ^ (q ^ (e - 1)) with hζqO
  have hmκ : ((m : ℕ) : κ) ≠ 0 := by
    intro h0
    have h1 : (m : 𝓞 N) ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem,
        show Ideal.Quotient.mk P.asIdeal (m : 𝓞 N) = ((m : ℕ) : κ) from map_natCast _ m]
      exact h0
    have h2 : ((m : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by
      have h3 : ((m : ℕ) : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by
        rw [Ideal.mem_under]; simpa using h1
      rwa [← hP.over] at h3
    exact hℓnotm (by
      have h4 : Rat.HeightOneSpectrum.natGenerator p ∣ m :=
        (Work.SSGRoute.rat_primeIdeal_mem_iff p m).mp h2
      rw [hp_gen] at h4
      exact_mod_cast h4)
  have hαOq : αO ^ q = (m : 𝓞 N) := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, hαO, hα]
    simp
  have hᾱq : ᾱ ^ q = ((m : ℕ) : κ) := by
    rw [hᾱ, ← map_pow, hαOq]
    exact map_natCast _ m
  have hᾱne : ᾱ ≠ 0 := by
    intro h0
    have h1 : ᾱ ^ q = 0 := by rw [h0]; exact zero_pow (by omega : q ≠ 0)
    rw [hᾱq] at h1
    exact hmκ h1
  have hmk_frob : (Ideal.Quotient.mk P.asIdeal) (galRestrict (𝓞 ℚ) ℚ N (𝓞 N) σ αO)
      = ᾱ ^ ℓ := by
    have h := hfrobP.mk_apply hP αO
    rw [hcardp] at h
    rw [h]
  have hgal_α : galRestrict (𝓞 ℚ) ℚ N (𝓞 N) σ αO = ζqO * αO := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_mul, algebraMap_galRestrict_apply, hαO, hζqO, map_pow, hζO, hσα]
  have hkey : (Ideal.Quotient.mk P.asIdeal) ζqO = ᾱ ^ (ℓ - 1) := by
    have h := hmk_frob
    rw [hgal_α, map_mul] at h
    have h1 : ᾱ ^ ℓ = ᾱ ^ (ℓ - 1) * ᾱ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
    rw [h1] at h
    exact mul_right_cancel₀ hᾱne h
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h]; exact Nat.cast_zero) hn0
    · exact h
  have hmod : (((n : ℕ) ^ q : ℕ) : ZMod ℓ) = ((m : ℕ) : ZMod ℓ) := by
    rw [Nat.cast_pow]; exact hxq
  have hmodq : ((n : ℕ) ^ q) ≡ m [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
  have hm_eq : ((m : ℕ) : κ) = ((n : ℕ) : κ) ^ q := by
    rcases le_total m (n ^ q) with hle | hle
    · have hdvd : ℓ ∣ n ^ q - m := hmodq.symm.dvd'
      obtain ⟨u, hu⟩ := hdvd
      have hc : (((n ^ q - m : ℕ)) : κ) = 0 := by
        rw [hu, Nat.cast_mul, hℓκ, zero_mul]
      have hsplit : (((n : ℕ) ^ q : ℕ) : κ) = (((n ^ q - m : ℕ)) : κ) + ((m : ℕ) : κ) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hle]
      calc ((m : ℕ) : κ) = (((n ^ q - m : ℕ)) : κ) + ((m : ℕ) : κ) := by rw [hc, zero_add]
        _ = (((n : ℕ) ^ q : ℕ) : κ) := hsplit.symm
        _ = ((n : ℕ) : κ) ^ q := by rw [Nat.cast_pow]
    · have hdvd : ℓ ∣ m - n ^ q := hmodq.dvd'
      obtain ⟨u, hu⟩ := hdvd
      have hc : (((m - n ^ q : ℕ)) : κ) = 0 := by
        rw [hu, Nat.cast_mul, hℓκ, zero_mul]
      have hsplit : (((m : ℕ)) : κ) = (((m - n ^ q : ℕ)) : κ) + (((n : ℕ) ^ q : ℕ) : κ) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hle]
      calc ((m : ℕ) : κ) = (((m - n ^ q : ℕ)) : κ) + (((n : ℕ) ^ q : ℕ) : κ) := hsplit
        _ = (((n : ℕ) ^ q : ℕ) : κ) := by rw [hc, zero_add]
        _ = ((n : ℕ) : κ) ^ q := by rw [Nat.cast_pow]
  have hnpow_pos : 1 ≤ (n : ℕ) ^ (ℓ - 1) := Nat.one_le_pow _ _ hnpos
  have hferm : ((n : ℕ) : ZMod ℓ) ^ (ℓ - 1) = 1 := by
    haveI : Fact ℓ.Prime := ⟨hℓprime⟩
    exact ZMod.pow_card_sub_one_eq_one hn0
  have hfmod : (((n : ℕ) ^ (ℓ - 1) : ℕ) : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by
    rw [Nat.cast_pow, Nat.cast_one]; exact hferm
  have hfq : ((n : ℕ) ^ (ℓ - 1)) ≡ 1 [MOD ℓ] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hfmod
  have hfermatκ : ((n : ℕ) : κ) ^ (ℓ - 1) = 1 := by
    have hdvd : ℓ ∣ n ^ (ℓ - 1) - 1 := hfq.symm.dvd'
    obtain ⟨u, hu⟩ := hdvd
    have hc : (((n ^ (ℓ - 1) - 1 : ℕ)) : κ) = 0 := by
      rw [hu, Nat.cast_mul, hℓκ, zero_mul]
    have hsplit : (((n : ℕ) ^ (ℓ - 1) : ℕ) : κ)
        = (((n ^ (ℓ - 1) - 1 : ℕ)) : κ) + ((1 : ℕ) : κ) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hnpow_pos]
    calc ((n : ℕ) : κ) ^ (ℓ - 1) = (((n : ℕ) ^ (ℓ - 1) : ℕ) : κ) := by rw [Nat.cast_pow]
      _ = (((n ^ (ℓ - 1) - 1 : ℕ)) : κ) + ((1 : ℕ) : κ) := hsplit
      _ = 1 := by rw [hc, zero_add, Nat.cast_one]
  have hᾱℓ : ᾱ ^ (ℓ - 1) = 1 := by
    have hqdvd : q ∣ ℓ - 1 := dvd_trans (dvd_pow_self q (by omega : e ≠ 0)) hdvd
    obtain ⟨s, hs⟩ := hqdvd
    have h1 : ᾱ ^ (ℓ - 1) = (ᾱ ^ q) ^ s := by rw [hs, pow_mul]
    have h2 : ᾱ ^ q = ((n : ℕ) : κ) ^ q := by rw [hᾱq, hm_eq]
    rw [h1, h2, ← pow_mul, ← hs, hfermatκ]
  have hprim : IsPrimitiveRoot ((Ideal.Quotient.mk P.asIdeal) ζqO) q := by
    refine Work.SSGRoute.isPrimitiveRoot_quotient_mk (p := ℓ) P.asIdeal (hm := hq.pos) ?_ ?_ ?_
    · intro nn hnn
      have h2 : ((nn : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by
        have h3 : ((nn : ℕ) : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by
          rw [Ideal.mem_under]; simpa using hnn
        rwa [← hP.over] at h3
      have h4 : Rat.HeightOneSpectrum.natGenerator p ∣ nn :=
        (Work.SSGRoute.rat_primeIdeal_mem_iff p nn).mp h2
      rwa [hp_gen] at h4
    · intro h
      rcases hq.eq_one_or_self_of_dvd ℓ h with h1 | h1
      · exact hℓprime.ne_one h1
      · omega
    · have h1 : IsPrimitiveRoot (ζO ^ (q ^ (e - 1)))
          (q ^ e / Nat.gcd (q ^ e) (q ^ (e - 1))) :=
        Work.SSGRoute.pow_div_gcd (by positivity) hζO'
      have hgcd : q ^ e / Nat.gcd (q ^ e) (q ^ (e - 1)) = q := by
        rw [Nat.gcd_eq_right (pow_dvd_pow q (by omega : e - 1 ≤ e))]
        rw [show q ^ e = q ^ (e - 1) * q from by rw [← pow_succ]; congr 1; omega]
        exact Nat.mul_div_cancel_left q (pow_pos hq.pos (e - 1))
      rwa [hgcd] at h1
  have hneq : (Ideal.Quotient.mk P.asIdeal) ζqO ≠ 1 := by
    intro h1
    have h2 : q ∣ 1 := hprim.dvd_of_pow_eq_one 1 (by rw [pow_one, h1])
    exact hq.not_dvd_one h2
  exact hneq (by rw [hkey, hᾱℓ])


/-- **The residue characteristic is not `ℓ` if `ℓ` does not divide the residue cardinality.** -/
theorem cast_notMem_of_not_dvd_natCard (k : Type) [Field k] [NumberField k]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hm : ¬ ℓ ∣ Nat.card (NumberField.RingOfIntegers k ⧸ v.asIdeal)) :
    (ℓ : NumberField.RingOfIntegers k) ∉ v.asIdeal := by
  intro hmem
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Field (NumberField.RingOfIntegers k ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (NumberField.RingOfIntegers k ⧸ v.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum v
  haveI : Fintype (NumberField.RingOfIntegers k ⧸ v.asIdeal) := Fintype.ofFinite _
  have hm' : ¬ ℓ ∣ Fintype.card (NumberField.RingOfIntegers k ⧸ v.asIdeal) := by
    rwa [← Nat.card_eq_fintype_card]
  have hℓκ : ((ℓ : ℕ) : NumberField.RingOfIntegers k ⧸ v.asIdeal) = 0 := by
    rw [show ((ℓ : ℕ) : NumberField.RingOfIntegers k ⧸ v.asIdeal)
        = Ideal.Quotient.mk v.asIdeal (ℓ : NumberField.RingOfIntegers k) from
      (map_natCast _ ℓ).symm, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  haveI : CharP (NumberField.RingOfIntegers k ⧸ v.asIdeal) ℓ :=
    (CharP.charP_iff_prime_eq_zero hℓ).mpr hℓκ
  letI : Module (ZMod ℓ) (NumberField.RingOfIntegers k ⧸ v.asIdeal) :=
    { (ZMod.castHom dvd_rfl (NumberField.RingOfIntegers k ⧸ v.asIdeal) : ZMod ℓ →+* _).toModule with }
  obtain ⟨n, hn⟩ := VectorSpace.card_fintype (ZMod ℓ) (NumberField.RingOfIntegers k ⧸ v.asIdeal)
  have hn' : Fintype.card (NumberField.RingOfIntegers k ⧸ v.asIdeal) = ℓ ^ n := by
    simpa [ZMod.card] using hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn'
    have := Fintype.one_lt_card (α := NumberField.RingOfIntegers k ⧸ v.asIdeal)
    omega
  exact hm' (by rw [hn']; exact dvd_pow_self ℓ hn0)




/-- Auxiliary: **the level construction of route A.**

Given a prime `ℓ` with `ℓ ∤ disc k`, `(ℓ) ∉ v₀`, `q ^ e ∣ ℓ - 1`, `N v₀ ∉ ((ZMod ℓ)ˣ) ^ q` and the
fact that every place of `cycM q e ℓ ζ` above `v₀` has full local degree, the level
`cycM q e ℓ ζ` gives a `LevelData k q e v₀`. -/
theorem cycM_assembly (k : Type) [Field k] [NumberField k] (q e ℓ : ℕ) (hq : q.Prime)
    (hℓ : ℓ.Prime) (he : 0 < e) (hdisc : ¬ (ℓ : ℤ) ∣ NumberField.discr k)
    (hdvd : q ^ e ∣ ℓ - 1) (ζ : AlgebraicClosure k) (hζ : IsPrimitiveRoot ζ ℓ)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hres : (ℓ : NumberField.RingOfIntegers k) ∉ v₀.asIdeal)
    (hnotpow : ¬ ∃ x : (ZMod ℓ)ˣ, (x : ZMod ℓ) ^ q
      = ((Nat.card (NumberField.RingOfIntegers k ⧸ v₀.asIdeal) : ℕ) : ZMod ℓ))
    [NumberField ↥(cycM q e ℓ ζ)]
    (hfull : ∀ w : NK.GlobalCFT.Place ↥(cycM q e ℓ ζ),
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v₀) →
        Nat.card (MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ)) w) =
          Nat.card (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))) :
    Nonempty (LevelData k q e v₀) := by
  obtain ⟨D⟩ := cycM_structure_aux k q e ℓ hq hℓ he hdisc hdvd ζ hζ
  exact ⟨{ M := cycM q e ℓ ζ
           fd := D.fd
           nf := D.nf
           gal := D.gal
           cyc := D.cyc
           qpow := ⟨e, D.card⟩
           dvd := ⟨1, by rw [D.card, mul_one]⟩
           fullLocal := hfull }⟩

/-- **Route A: the cyclotomic per-place level, when the residue cardinality is not a `q`-th power.**

For a number field `k`, a finite place `v₀`, an odd prime `q` and `e > 0`: if the residue field
cardinality `N v₀ = #(𝓞 k ⧸ v₀.asIdeal)` is **not** a `q`-th power of an integer, then there is a
`LevelData k q e v₀`.

Construction: by Chebotarev's existence-form result over `ℚ`
(`Work.SSGRoute.chebotarevInfinite_type0`, applied to the finite Galois extension
`ℚ(ζ_{q^e}, m^{1/q})/ℚ` with `m = N v₀`) there is a rational prime `ℓ` with `q^e ∣ ℓ - 1`,
`ℓ ∤ disc k`, `ℓ ∤ N v₀` and `N v₀ ∉ (ZMod ℓ)ˣ ^ q`.  Then `k ∩ ℚ(ζ_ℓ) = ℚ`
(`NK.CFTLib.RouteB.finrank_eq_one_of_isCyclotomic_of_unramified`), so
`Gal(k(ζ_ℓ)/k) ≅ (ZMod ℓ)ˣ`, and the level is the subfield `M ⊆ k(ζ_ℓ)` with
`Gal(M/k) = (ZMod ℓ)ˣ ⧸ ((ZMod ℓ)ˣ)^q^e ≅ ZMod (q^e)`; the Frobenius of the (unramified) place
`v₀` generates this quotient, so `v₀` has full local degree. -/
theorem routeA_level (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q e : ℕ) (hq : q.Prime) (hq2 : 2 < q) (he : 0 < e)
    (hN : ¬ ∃ m : ℕ, 0 < m ∧ Nat.card (NumberField.RingOfIntegers k ⧸ v₀.asIdeal) = m ^ q) :
    Nonempty (LevelData k q e v₀) := by
  classical
  set m : ℕ := Nat.card (NumberField.RingOfIntegers k ⧸ v₀.asIdeal) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.card_pos
  have hmq : ¬ ∃ m' : ℕ, 0 < m' ∧ m = m' ^ q := by
    rw [hm]; exact hN
  -- the Kummer field `ℚ(ζ_{q^e}, m ^ (1/q))` with the automorphism moving `m ^ (1/q)`
  obtain ⟨N, hFN, hNF, hAlgN, hFDiN, hGalN, ζ, α, σ, hζ, hα, hσζ, hσα⟩ :=
    kummerCyc_data q e m hq hq2 he hmpos hmq
  letI : Field N := hFN
  letI : NumberField N := hNF
  letI : Algebra ℚ N := hAlgN
  letI : FiniteDimensional ℚ N := hFDiN
  letI : IsGalois ℚ N := hGalN
  -- the prime `ℓ`
  obtain ⟨ℓ, hℓprime, hℓdvd, hℓnotD, hℓnotmZ, hℓnotpow⟩ :=
    exists_prime_notPower_mod q e m hq hq2 he hmpos hmq (NumberField.discr k)
      (NumberField.discr_ne_zero k) N ζ α σ hζ hα hσζ hσα
  have hℓnotm : ¬ ℓ ∣ m := fun h => hℓnotmZ (by exact_mod_cast h)
  -- `ℓ` is not the residue characteristic of `v₀`
  have hres : (ℓ : NumberField.RingOfIntegers k) ∉ v₀.asIdeal :=
    cast_notMem_of_not_dvd_natCard k v₀ ℓ hℓprime (by rw [← hm]; exact hℓnotm)
  -- a primitive `ℓ`-th root of unity in `AlgebraicClosure k`
  haveI : IsSepClosure k (AlgebraicClosure k) :=
    IsSepClosure.of_isAlgClosure_of_perfectField k (AlgebraicClosure k)
  haveI : IsSepClosed (AlgebraicClosure k) := (inferInstance : IsSepClosure k _).sep_closed
  haveI : NeZero ((ℓ : ℕ) : AlgebraicClosure k) := ⟨by
    rw [Nat.cast_ne_zero]; exact hℓprime.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := AlgebraicClosure k) (n := ℓ)
  haveI : NumberField ↥(cycM q e ℓ ζ₀) :=
    (cycM_structure_aux k q e ℓ hq hℓprime he hℓnotD hℓdvd ζ₀ hζ₀).some.nf
  refine cycM_assembly k q e ℓ hq hℓprime he hℓnotD hℓdvd ζ₀ hζ₀ v₀ hres ?_ ?_
  · rw [← hm]; exact hℓnotpow
  · -- the local-degree statement at `v₀`
    exact cycM_fullLocal k q e ℓ hq hℓprime he hℓnotD hℓdvd ζ₀ hζ₀ v₀ hres
      (by rw [← hm]; exact hℓnotpow)

end Work.SSGRoute.CycLevel
