import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.vdwOrderCriterion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Van der Waerden's prime-existence lemma

`NK.CFTLib.ArtinReciprocityIdeal.vdwPrimeExists_self`: for `a > 1`, a prime `ℓ`, `e ≥ 1`, a bound
`B` and a finite set `S` of primes there is a prime `p > max B a`, `p ∉ S`, with
`ℓ^e ∣ orderOf ((a : ZMod p))`.  This is the arithmetic bottleneck of the auxiliary-field
construction of Artin's lemma (`NOTES_vdwPrimeExists.md`); the `Q`-construction below is that of
the notes, with `b := a^M`, `M := ∏_{q ∈ F'}(q-1)` for the finite set `F'` of primes that must be
avoided.

Ingredients: `geomSum_mul_nat` (the geometric-sum identity in `ℕ`), `notSqDvdGeomSum` (LTE: for odd
`ℓ` and `b ≡ 1 (mod ℓ)` the sum is exactly divisible by `ℓ`), `notFourDvdGeomSumTwo` (the `ℓ = 2`
case, by a parity argument), `not_dvd_geomSum_of_small` (small primes do not divide the sum, by
Fermat), `existsPrimeDvdNotMem` (a prime divisor of the sum different from `ℓ` exists), and
`orderOf_eq_prime_pow_of_dvd_geomSum` (`vdwOrderCriterion.lean`: such a prime forces the order to be
exactly `ℓ^(e+1)`).
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

open Finset


/-- The geometric-sum identity in `ℕ`. -/
theorem geomSum_mul_nat (x ℓ : ℕ) : (∑ i ∈ Finset.range ℓ, x ^ i) * (x - 1) = x ^ ℓ - 1 := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    cases ℓ with
    | zero => simp
    | succ n => simp
  · induction ℓ with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, add_mul, ih, Nat.mul_sub_left_distrib, mul_one, pow_succ]
        have h2 : 1 ≤ x ^ n := one_le_pow₀ hx
        have hle : x ^ n * 1 ≤ x ^ n * x := Nat.mul_le_mul_left _ hx
        omega

/-- **LTE corollary.** For odd `ℓ` and `b ≡ 1 (mod ℓ)`, `ℓ² ∤ ∑_{i<ℓ} b^{i ℓ^e}`. -/
theorem notSqDvdGeomSum {b ℓ e : ℕ} (hb : 1 < b) (hℓ : ℓ.Prime) (hodd : Odd ℓ) (he : 0 < e)
    (hcong : ℓ ∣ b - 1) :
    ¬ ℓ ^ 2 ∣ ∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hb1 : ¬ ℓ ∣ b := by
    intro h
    have h1 : ℓ ∣ b - (b - 1) := Nat.dvd_sub h hcong
    have h2 : b - (b - 1) = 1 := by omega
    rw [h2] at h1
    exact hℓ.not_dvd_one h1
  set Q : ℕ := ∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e) with hQ
  have hmul : Q * (b ^ (ℓ ^ e) - 1) = b ^ (ℓ ^ (e + 1)) - 1 := by
    rw [hQ, show (∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e))
        = ∑ i ∈ Finset.range ℓ, (b ^ (ℓ ^ e)) ^ i from by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_mul']]
    rw [geomSum_mul_nat, ← pow_mul, ← pow_succ]
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨0, Finset.mem_range.mpr hℓ.pos, by simp⟩
  have hsub : 0 < b ^ (ℓ ^ e) - 1 := by
    have : 1 < b ^ (ℓ ^ e) := Nat.one_lt_pow (pow_ne_zero e hℓ.ne_zero) hb
    omega
  have hLTE : ∀ k : ℕ, padicValNat ℓ (b ^ (ℓ ^ k) - 1) = padicValNat ℓ (b - 1) + k := by
    intro k
    rw [show b ^ (ℓ ^ k) - 1 = b ^ (ℓ ^ k) - 1 ^ (ℓ ^ k) by simp,
      padicValNat.pow_sub_pow hodd hb hcong hb1 (pow_ne_zero k hℓ.ne_zero),
      padicValNat.prime_pow]
  have hval : padicValNat ℓ Q + padicValNat ℓ (b ^ (ℓ ^ e) - 1)
      = padicValNat ℓ (b ^ (ℓ ^ (e + 1)) - 1) := by
    have h := padicValNat.mul (p := ℓ) (a := Q) (b := b ^ (ℓ ^ e) - 1)
      (hQpos.ne') (hsub.ne')
    rw [hmul] at h
    exact h.symm
  rw [hLTE e, hLTE (e + 1)] at hval
  have hpe : padicValNat ℓ Q = 1 := by omega
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hkne : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have h2 : padicValNat ℓ Q = 2 + padicValNat ℓ k := by
    have hℓ2nz : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ.ne_zero
    rw [hk, padicValNat.mul (p := ℓ) (a := ℓ ^ 2) (b := k) hℓ2nz hkne,
      padicValNat.prime_pow]
  omega

/-- The `ℓ = 2` companion: `4 ∤ ∑_{i<2} b^{i 2^e}` for `b ≥ 2`, `e ≥ 1`. -/
theorem notFourDvdGeomSumTwo {b e : ℕ} (hb : 1 < b) (he : 0 < e) :
    ¬ 4 ∣ ∑ i ∈ Finset.range 2, b ^ (i * 2 ^ e) := by
  have hpos : 0 < 2 ^ e := by positivity
  have hsplit : 2 ^ e = 2 * 2 ^ (e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [zero_mul, pow_zero, one_mul]
  rcases Nat.even_or_odd b with ⟨c, hc⟩ | hodd
  · have hb2 : b = 2 * c := by omega
    have hd : 2 ∣ b ^ 2 ^ e := by
      rw [hb2]
      exact dvd_trans (dvd_mul_right 2 c) (dvd_pow_self _ hpos.ne')
    intro h4
    have h1 : b ^ 2 ^ e % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h2 : (1 + b ^ 2 ^ e) % 2 = 1 := by omega
    have h3 := Nat.mod_eq_zero_of_dvd h4
    omega
  · obtain ⟨c, hc⟩ := hodd
    have hb2 : b = 2 * c + 1 := by omega
    have hbmod : b ^ 2 % 4 = 1 := by
      have h1 : b % 4 = 1 ∨ b % 4 = 3 := by omega
      rcases h1 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
    have hX : b ^ 2 ^ e % 4 = 1 := by
      rw [show b ^ 2 ^ e = (b ^ 2) ^ (2 ^ (e - 1)) by rw [← pow_mul, hsplit]]
      rw [Nat.pow_mod, hbmod]
      norm_num
    intro h4
    have h3 := Nat.mod_eq_zero_of_dvd h4
    omega



/-- A prime divisor of `Q` different from `k` and outside `F`, given that the elements of `F`
dividing `Q` must equal `k`. -/
theorem existsPrimeDvdNotMem {Q k : ℕ} (hk : k.Prime) (hQ : k < Q) (hsq : ¬ k ^ 2 ∣ Q)
    {F : Finset ℕ} (hdiv : ∀ q ∈ F, q ∣ Q → q = k) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Q ∧ p ≠ k ∧ p ∉ F := by
  have hk2 : 2 ≤ k := hk.two_le
  have hQ1 : Q ≠ 1 := by omega
  have hex : ∃ p, p.Prime ∧ p ∣ Q ∧ p ≠ k := by
    by_cases hkQ : k ∣ Q
    · have hdiv1 : 1 < Q / k := by
        have h := Nat.mul_div_cancel' hkQ
        have h2 : k * 1 < k * (Q / k) := by rw [h, mul_one]; exact hQ
        exact Nat.lt_of_mul_lt_mul_left h2
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : Q / k ≠ 1)
      have hpQ : p ∣ Q := dvd_trans hpd (Nat.div_dvd_of_dvd hkQ)
      refine ⟨p, hp, hpQ, ?_⟩
      intro hpk
      have hkk : k * k ∣ Q := by
        rw [← Nat.mul_div_cancel' hkQ]
        exact mul_dvd_mul_left k (hpk ▸ hpd)
      exact hsq (by simpa [pow_two] using hkk)
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hQ1
      exact ⟨p, hp, hpd, fun hpk => hkQ (hpk ▸ hpd)⟩
  obtain ⟨p, hp, hpQ, hpk⟩ := hex
  exact ⟨p, hp, hpQ, hpk, fun hpF => hpk (hdiv p hpF hpQ)⟩

/-- For a prime `q ≠ ℓ` with `q - 1 ∣ M`, the geometric sum `∑_{i<ℓ} (a^M)^{i ℓ^e}` is not
divisible by `q`: if `q ∣ a` then all terms except the first vanish mod `q`, otherwise all terms
equal `1` mod `q` (Fermat, since `q - 1 ∣ M`), and `q ≠ ℓ`. -/
theorem not_dvd_geomSum_of_small {a M q ℓ e : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hM : q - 1 ∣ M)
    (ha : 1 < a) (hMpos : 0 < M) (hqℓ : q ≠ ℓ) :
    ¬ q ∣ ∑ i ∈ Finset.range ℓ, (a ^ M) ^ (i * ℓ ^ e) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hℓe : ℓ ^ e ≠ 0 := pow_ne_zero e hℓ.ne_zero
  have hℓpos : 0 < ℓ := hℓ.pos
  by_cases hqa : q ∣ a
  · have hbq : ((a ^ M : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_pow, (ZMod.natCast_eq_zero_iff a q).mpr hqa]
      exact zero_pow hMpos.ne'
    intro hdvd
    have h1 : ((∑ i ∈ Finset.range ℓ, (a ^ M) ^ (i * ℓ ^ e) : ℕ) : ZMod q) = 1 := by
      rw [Nat.cast_sum]
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hℓpos)]
      · simp
      · intro i hi hi0
        rw [Nat.cast_pow, hbq]
        exact zero_pow (mul_ne_zero hi0 hℓe)
    rw [(ZMod.natCast_eq_zero_iff _ q).mpr hdvd] at h1
    exact one_ne_zero h1.symm
  · have hane : (a : ZMod q) ≠ 0 := fun h => hqa ((ZMod.natCast_eq_zero_iff a q).mp h)
    have hb : ((a ^ M : ℕ) : ZMod q) = 1 := by
      rw [Nat.cast_pow]
      obtain ⟨k, hk⟩ := hM
      rw [hk, pow_mul, ZMod.pow_card_sub_one_eq_one hane, one_pow]
    intro hdvd
    have h1 : ((∑ i ∈ Finset.range ℓ, (a ^ M) ^ (i * ℓ ^ e) : ℕ) : ZMod q) = (ℓ : ZMod q) := by
      push_cast
      have hb' : ((a : ZMod q)) ^ M = 1 := by
        rw [← Nat.cast_pow]
        exact hb
      have h2 : ∀ i ∈ Finset.range ℓ, ((a : ZMod q) ^ M) ^ (i * ℓ ^ e) = 1 := by
        intro i hi
        rw [hb', one_pow]
      rw [Finset.sum_congr rfl h2]
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [(ZMod.natCast_eq_zero_iff _ q).mpr hdvd] at h1
    have hqdl : q ∣ ℓ := (ZMod.natCast_eq_zero_iff ℓ q).mp h1.symm
    exact hqℓ ((hℓ.dvd_iff_eq hq.ne_one).mp hqdl).symm

/-- **Van der Waerden's lemma (prime existence).** For `a > 1`, a prime `ℓ`, `e ≥ 1`, a bound `B`
and a finite set `S` of primes there is a prime `p > max B a`, `p ∉ S`, with
`ℓ^e ∣ orderOf ((a : ZMod p))`. -/
theorem vdwPrimeExistsProved (a ℓ e B : ℕ) (ha : 1 < a) (hℓ : ℓ.Prime) (he : 0 < e)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧ p ∉ S ∧ a < p ∧ ℓ ^ e ∣ orderOf ((a : ZMod p)) := by
  classical
  -- the finite set of primes to avoid, and the auxiliary modulus
  set F : Finset ℕ := S ∪ (Finset.range (max B a + 1)).filter Nat.Prime with hF
  have hFprime : ∀ q ∈ F, q.Prime := by
    intro q hq
    rcases Finset.mem_union.mp (hF ▸ hq) with h | h
    · exact hS q h
    · exact (Finset.mem_filter.mp h).2
  set F' : Finset ℕ := insert ℓ F with hF'
  have hF'prime : ∀ q ∈ F', q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp (hF' ▸ hq) with rfl | h
    · exact hℓ
    · exact hFprime q h
  have hℓF' : ℓ ∈ F' := hF' ▸ Finset.mem_insert_self ℓ F
  set M : ℕ := ∏ q ∈ F', (q - 1) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact Finset.prod_pos fun q hq => by
      have h2 : 2 ≤ q := (hF'prime q hq).two_le
      omega
  set b : ℕ := a ^ M with hb
  set Q : ℕ := ∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e) with hQ
  have hb2 : 1 < b := by
    rw [hb]
    exact Nat.one_lt_pow hMpos.ne' ha
  -- `Q > ℓ`
  have hQgt : ℓ < Q := by
    have hmem1 : 1 ∈ Finset.range ℓ := Finset.mem_range.mpr hℓ.one_lt
    have hle : b ^ (ℓ ^ e) ≤ Q := by
      rw [hQ]
      simpa using Finset.single_le_sum (f := fun i => b ^ (i * ℓ ^ e))
        (fun i _ => by positivity) hmem1
    have h2 : ℓ < b ^ (ℓ ^ e) := by
      have h4 : 2 ^ ℓ ≤ b ^ ℓ := Nat.pow_le_pow_left (by omega) ℓ
      have h5 : ℓ ≤ ℓ ^ e := by
        calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
          _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he
      have h6 : 2 ^ ℓ ≤ b ^ (ℓ ^ e) := by
        calc 2 ^ ℓ ≤ b ^ ℓ := h4
          _ ≤ b ^ (ℓ ^ e) := Nat.pow_le_pow_right (by omega) h5
      have h7 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
      omega
    omega
  -- every `q ∈ F'` dividing `Q` equals `ℓ`
  have hqQ : ∀ q ∈ F', q ∣ Q → q = ℓ := by
    intro q hqF' hqdvd
    by_contra hqne
    have hMq : q - 1 ∣ M := by
      rw [hM]
      exact Finset.dvd_prod_of_mem _ hqF'
    have := not_dvd_geomSum_of_small (e := e) (hF'prime q hqF') hℓ hMq ha hMpos hqne
    exact this hqdvd
  -- `ℓ² ∤ Q`
  have hsq : ¬ ℓ ^ 2 ∣ Q := by
    rcases hℓ.eq_two_or_odd with h2 | hodd2
    · subst h2
      rw [hQ]
      exact notFourDvdGeomSumTwo hb2 he
    · have hodd : Odd ℓ := Nat.odd_iff.mpr hodd2
      rw [hQ]
      by_cases hℓa : ℓ ∣ a
      · -- then every term with `i ≥ 1` vanishes mod `ℓ`
        intro hdvd
        have hℓQ : ℓ ∣ Q := dvd_trans (by norm_num : ℓ ∣ ℓ ^ 2) hdvd
        have hℓb : ℓ ∣ b := dvd_trans hℓa (dvd_pow_self a hMpos.ne')
        haveI : Fact ℓ.Prime := ⟨hℓ⟩
        have hbℓ : ((b : ZMod ℓ)) = 0 := (ZMod.natCast_eq_zero_iff b ℓ).mpr hℓb
        have h1 : ((Q : ℕ) : ZMod ℓ) = 1 := by
          rw [hQ, Nat.cast_sum]
          rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hℓ.pos)]
          · simp
          · intro i hi hi0
            rw [Nat.cast_pow, hbℓ]
            exact zero_pow (mul_ne_zero hi0 (pow_ne_zero e hℓ.ne_zero))
        have h2' : ((Q : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff Q ℓ).mpr hℓQ
        rw [h2'] at h1
        exact one_ne_zero h1.symm
      · refine notSqDvdGeomSum hb2 hℓ hodd he ?_
        -- `ℓ ∣ b - 1` from Fermat
        have hMℓ : ℓ - 1 ∣ M := by
          rw [hM]
          exact Finset.dvd_prod_of_mem _ hℓF'
        obtain ⟨k, hk⟩ := hMℓ
        haveI : Fact ℓ.Prime := ⟨hℓ⟩
        have hane : (a : ZMod ℓ) ≠ 0 := fun h => hℓa ((ZMod.natCast_eq_zero_iff a ℓ).mp h)
        have hb1 : ((b : ZMod ℓ)) = 1 := by
          rw [hb, Nat.cast_pow, hk, pow_mul, ZMod.pow_card_sub_one_eq_one hane, one_pow]
        have hmod : b ≡ 1 [MOD ℓ] := by
          have := (ZMod.natCast_eq_natCast_iff b 1 ℓ).mp (by simpa using hb1)
          simpa using this
        exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ b)).mp hmod.symm
  -- extract the prime
  obtain ⟨p, hp, hpQ, hpne, hpF'⟩ := existsPrimeDvdNotMem hℓ hQgt hsq hqQ
  have hple : p ∉ F := fun h => hpF' (hF' ▸ Finset.mem_insert.mpr (Or.inr h))
  have hlarge : max B a < p := by
    by_contra hcon
    refine hple ((hF ▸ Finset.mem_union.mpr) (Or.inr (Finset.mem_filter.mpr ⟨?_, hp⟩)))
    exact Finset.mem_range.mpr (by omega)
  refine ⟨p, hp, by omega, fun hS' => hple ((hF ▸ Finset.mem_union.mpr) (Or.inl hS')), by omega, ?_⟩
  -- the order computation
  have hord : orderOf ((b : ZMod p)) = ℓ ^ (e + 1) := by
    rw [hQ] at hpQ
    exact orderOf_eq_prime_pow_of_dvd_geomSum hb2 hℓ he hp hpQ hpne
  have hdvd : orderOf ((b : ZMod p)) ∣ orderOf ((a : ZMod p)) := by
    rw [orderOf_dvd_iff_pow_eq_one, hb, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  rw [hord] at hdvd
  exact dvd_trans (pow_dvd_pow ℓ (by omega)) hdvd


end NK.CFTLib.ArtinReciprocityIdeal
