import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Element bound for the Ionescu–Wainger set `P_{≤l}`

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages* (Annals of Math. 195 (2022)), shows that every element of the IW
denominator set `P_{≤l}` is at most `2^{C_ρ · 2^{ρ l}}`.  This file proves that bound for the
formalisation `iwP ρ l` of `Submission.Work.Analysis.IonescuWainger.Basic`, i.e.

`Work.Analysis.IonescuWainger.iwP_element_le`.

The proof splits on the definition of `iwP`:

* for `l ≤ iwC0 ρ` we have `iwP ρ l = [1, 2^l]`, and it suffices to note that
  `(l : ℝ) * log 2 ≤ 2^{ρ l} / ρ` (the `x log 2 ≤ 2^x` inequality), which gives `l ≤ C 2^{ρ l}`;
* for `l > iwC0 ρ` every `q ∈ P_{≤l}` is `q = Q * w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`
  and `w ∈ W_{≤l}`.  Here `N_0^{(l)} = ⌊2^{ρ l/2}⌋ + 1 ≤ 2 · 2^{ρ l/2}`, so
  `log Q ≤ D_ρ · N_0 log N_0 ≤ 2 D_ρ (1 + log 2) 2^{ρ l}`, while each element of `W_{≤l}` is a
  product of at most `D_ρ` distinct primes `≤ 2^l` taken to powers `≤ D_ρ`, hence at most
  `(2^l)^{D_ρ^2}`, giving `log w ≤ D_ρ^2 l log 2 ≤ (D_ρ^2/ρ) 2^{ρ l}`.

Both cases are subsumed by the single constant
`C = (2 D_ρ (1 + log 2) + D_ρ^2/ρ + 1/ρ + 1) / log 2`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-! ## Elementary estimates -/

/-- `x * log 2 ≤ 2 ^ x` for every real `x`: this is the elementary bound that compares the linear
scale with the exponential scale. -/
private lemma mul_log_two_le_two_rpow (x : ℝ) : x * Real.log 2 ≤ (2 : ℝ) ^ x := by
  have h := Real.add_one_le_exp (x * Real.log 2)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x, mul_comm (Real.log 2) x]
  linarith

/-- The factorization of a product of primes to given powers. -/
private theorem prod_prime_pow_factorization {S : Finset ℕ} {e : ℕ → ℕ}
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (S.prod (fun p => p ^ e p)).factorization q = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun x hx => pow_ne_zero _ (hp x hx).ne_zero)]
  have key : ∀ p ∈ S, ((p ^ e p).factorization q) = if p = q then e p else 0 := by
    intro p hp'
    rw [(hp p hp').factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl key]
  simp

/-- The exponent of any prime in an element of `W_{≤l}` is at most `D_ρ`, and if it is nonzero the
prime lies in `(N_0^{(l)}, 2^l]`. -/
private theorem iwW_factorization_le {ρ : ℝ} {l w q : ℕ} (hw : w ∈ iwW ρ l) :
    w.factorization q ≤ if q ∈ iwPrimeRange ρ l then iwD ρ else 0 := by
  obtain ⟨hdvd, -⟩ := mem_iwW.mp hw
  classical
  have hle : w.factorization q ≤ (iwProd ρ l).factorization q :=
    Nat.factorization_le_factorization_of_dvd_right hdvd
      (pos_of_mem_iwW hw).ne' (iwProd_ne_zero ρ l)
  have hprod : (iwProd ρ l).factorization q
      = if q ∈ iwPrimeRange ρ l then iwD ρ else 0 :=
    prod_prime_pow_factorization (fun p hp => (Finset.mem_filter.mp hp).2) q
  rw [hprod] at hle; exact hle

/-- **Element bound for `W_{≤l}`.**  An element of `W_{≤l}` is a product of at most `D_ρ` distinct
primes from `(N_0^{(l)}, 2^l]`, each taken to a power at most `D_ρ`, hence at most
`(2^l)^{D_ρ · D_ρ}`. -/
private theorem iwW_le {ρ : ℝ} {l w : ℕ} (hw : w ∈ iwW ρ l) :
    w ≤ (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  classical
  have hw0 : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  have hfact : ∀ p, w.factorization p ≤ iwD ρ := by
    intro p
    have h := iwW_factorization_le hw (q := p)
    split_ifs at h with hmem
    · exact h
    · exact h.trans (Nat.zero_le _)
  have hple : ∀ p ∈ w.factorization.support, p ≤ 2 ^ l := by
    intro p hp
    have hne : w.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    by_cases hmem : p ∈ iwPrimeRange ρ l
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    · have h := iwW_factorization_le hw (q := p)
      rw [if_neg hmem] at h
      exact absurd (le_antisymm h (Nat.zero_le _)) hne
  calc w = ∏ p ∈ w.factorization.support, p ^ w.factorization p :=
        (Nat.prod_factorization_pow_eq_self hw0).symm
    _ ≤ ∏ _p ∈ w.factorization.support, (2 ^ l) ^ iwD ρ := by
        refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) fun p hp => ?_
        calc p ^ w.factorization p ≤ (2 ^ l) ^ w.factorization p :=
              Nat.pow_le_pow_left (hple p hp) _
          _ ≤ (2 ^ l) ^ iwD ρ := Nat.pow_le_pow_right (by positivity) (hfact p)
    _ = ((2 ^ l) ^ iwD ρ) ^ (w.factorization.support.card) := Finset.prod_const _
    _ ≤ ((2 ^ l) ^ iwD ρ) ^ iwD ρ :=
        Nat.pow_le_pow_right (by positivity) (mem_iwW.mp hw).2
    _ = (2 ^ l) ^ (iwD ρ * iwD ρ) := by rw [pow_mul]

/-- **Logarithmic bound for `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`.**  With `N_0^{(l)} ≤ 2·2^{ρl/2}` and
`N_0! ≤ N_0^{N_0}` we get `log Q_0 ≤ D_ρ · N_0 log N_0 ≤ 2 D_ρ (1 + log 2) 2^{ρl}`. -/
private lemma log_iwQ0_le {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    Real.log ((iwQ0 ρ l : ℕ) : ℝ)
      ≤ 2 * (iwD ρ : ℝ) * (1 + Real.log 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hSdef
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by
    rw [htdef]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have htt : t * t = S := by
    rw [htdef, hSdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have htS : t ≤ S := by
    have h : t ≤ t * t := by nlinarith [ht1, htpos]
    linarith [htt]
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxL : (ρ * (l : ℝ) / 2) * Real.log 2 ≤ t := by
    rw [htdef]; exact mul_log_two_le_two_rpow _
  have hN0pos : (0 : ℝ) < ((iwN0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  have hN0le : ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := by
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (le_of_lt htpos)
    have heq : ((iwN0 ρ l : ℕ) : ℝ) = ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
      rw [iwN0, ← htdef, Nat.cast_add, Nat.cast_one]
    rw [heq]; linarith
  have hlogN0 : Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2 := by
    have h1 : Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ Real.log (2 * t) :=
      Real.log_le_log hN0pos hN0le
    have h2 : Real.log (2 * t) = Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt htpos), htdef,
        Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    linarith [h1, h2.le]
  have hlogN0pos : 0 ≤ Real.log ((iwN0 ρ l : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ iwN0 ρ l by rw [iwN0]; exact Nat.le_add_left 1 _))
  have hfact : Real.log (((iwN0 ρ l).factorial : ℕ) : ℝ)
      ≤ ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ) := by
    have h := Nat.factorial_le_pow (iwN0 ρ l)
    have hR : (((iwN0 ρ l).factorial : ℕ) : ℝ) ≤ (((iwN0 ρ l) ^ (iwN0 ρ l) : ℕ) : ℝ) := by
      exact_mod_cast h
    have hp : (0 : ℝ) < (((iwN0 ρ l).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have h2 := Real.log_le_log hp hR
    rw [Nat.cast_pow, Real.log_pow] at h2
    exact h2
  have hD0 : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  rw [iwQ0, Nat.cast_pow, Real.log_pow]
  have hstep1 := mul_le_mul_of_nonneg_left hfact hD0
  have hstep2 : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2) := by
    calc ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
        ≤ (2 * t) * Real.log ((iwN0 ρ l : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hN0le hlogN0pos
      _ ≤ (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogN0 (by positivity)
  have hstep3 : (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2)
      ≤ 2 * (1 + Real.log 2) * S := by
    nlinarith [hxL, htS, hLpos, htpos, htt]
  have hstep4 := mul_le_mul_of_nonneg_left hstep3 hD0
  have hstep2' := mul_le_mul_of_nonneg_left hstep2 hD0
  nlinarith [hstep1, hstep2', hstep4]

/-! ## The element bound -/

/-- Every element of `iwP ρ l = P_{≤l}` is bounded by `2^{C 2^{ρ l}}`. -/
theorem iwP_element_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l q, q ∈ iwP ρ l → (q : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
  set D : ℝ := (iwD ρ : ℝ) with hDdef
  set L : ℝ := Real.log 2 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by norm_num)
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    exact_mod_cast (show 1 ≤ iwD ρ by rw [iwD]; exact Nat.le_add_left 1 _)
  have hDnn : 0 ≤ D := le_trans zero_le_one hD1
  set K : ℝ := (2 * D * (1 + L) + D * D / ρ + 1 / ρ + 1) / L with hKdef
  have hρinv : 0 < 1 / ρ := one_div_pos.mpr hρ
  have hnumpos : 0 < 2 * D * (1 + L) + D * D / ρ + 1 / ρ + 1 := by
    have h1 : 0 < 2 * D * (1 + L) := by nlinarith [hD1, hLpos]
    have h2 : 0 ≤ D * D / ρ := div_nonneg (mul_nonneg hDnn hDnn) hρ.le
    linarith
  have hKpos : 0 < K := by
    rw [hKdef]; exact div_pos hnumpos hLpos
  have hKL : K * L = 2 * D * (1 + L) + D * D / ρ + 1 / ρ + 1 := by
    rw [hKdef, div_mul_cancel₀ _ (ne_of_gt hLpos)]
  have hY1 : 1 / ρ ≤ K * L := by
    rw [hKL]
    have h1 : 0 ≤ 2 * D * (1 + L) := le_of_lt (by nlinarith [hD1, hLpos])
    have h2 : 0 ≤ D * D / ρ := div_nonneg (mul_nonneg hDnn hDnn) hρ.le
    linarith
  have hY2 : 2 * D * (1 + L) + D * D / ρ ≤ K * L := by
    rw [hKL]; linarith [le_of_lt hρinv]
  refine ⟨K, hKpos, ?_⟩
  intro l q hq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast pos_of_mem_iwP hq
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hSdef
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by
    rw [htdef]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have htt : t * t = S := by
    rw [htdef, hSdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have htS : t ≤ S := by
    have h : t ≤ t * t := by nlinarith [ht1, htpos]
    linarith [htt]
  have hA1 : (l : ℝ) * L ≤ S / ρ := by
    rw [hLdef, hSdef, le_div_iff₀ hρ]
    have h := mul_log_two_le_two_rpow (ρ * (l : ℝ))
    nlinarith [h]
  have hA2 : (ρ * (l : ℝ) / 2) * L ≤ t := by
    rw [hLdef, htdef]
    exact mul_log_two_le_two_rpow _
  have hlog : Real.log (q : ℝ) ≤ K * S * L := by
    rw [mem_iwP] at hq
    rcases hq with ⟨_, _, hq2⟩ | ⟨_, hqP⟩
    · -- `l ≤ iwC0 ρ`: `q ≤ 2 ^ l`
      have h1 : Real.log (q : ℝ) ≤ (l : ℝ) * L := by
        have hq2R : (q : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by exact_mod_cast hq2
        have h := Real.log_le_log hqpos hq2R
        rw [Nat.cast_pow, Real.log_pow] at h
        push_cast at h
        rw [← hLdef] at h
        exact h
      have h2 : (l : ℝ) * L ≤ K * S * L := by
        have h3 : S / ρ ≤ S * (K * L) := by
          have h4 : S * (1 / ρ) ≤ S * (K * L) := mul_le_mul_of_nonneg_left hY1 hSpos.le
          rwa [mul_one_div] at h4
        have h5 : S * (K * L) = K * S * L := by ring
        linarith [hA1, h3, h5.le, h5.ge]
      linarith
    · -- `l > iwC0 ρ`: `q = Q * w`
      obtain ⟨Q, hQ, w, hw, rfl⟩ := mem_iwPconcrete.mp hqP
      obtain ⟨hdvd, hQ0ne⟩ := Nat.mem_divisors.mp hQ
      have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hQ
      have hwpos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast pos_of_mem_iwW hw
      have hlogQ : Real.log (Q : ℝ) ≤ 2 * D * (1 + L) * S := by
        have hQle : Q ≤ iwQ0 ρ l := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0ne) hdvd
        have h1 : Real.log (Q : ℝ) ≤ Real.log ((iwQ0 ρ l : ℕ) : ℝ) :=
          Real.log_le_log hQpos (by exact_mod_cast hQle)
        have h2 := log_iwQ0_le hρ l
        rw [← hDdef, ← hLdef, ← hSdef] at h2
        linarith
      have hlogw : Real.log (w : ℝ) ≤ D * D / ρ * S := by
        have h1 : Real.log (w : ℝ)
            ≤ Real.log ((((2 ^ l) ^ (iwD ρ * iwD ρ) : ℕ)) : ℝ) :=
          Real.log_le_log hwpos (by exact_mod_cast iwW_le hw)
        rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow] at h1
        push_cast at h1
        rw [← hDdef, ← hLdef] at h1
        have h2 : D * D * ((l : ℝ) * L) ≤ D * D / ρ * S := by
          have h3 := mul_le_mul_of_nonneg_left hA1 (mul_nonneg hDnn hDnn)
          calc D * D * ((l : ℝ) * L) = (D * D) * ((l : ℝ) * L) := by ring
            _ ≤ (D * D) * (S / ρ) := h3
            _ = D * D / ρ * S := by ring
        linarith
      have hmain : Real.log (Q : ℝ) + Real.log (w : ℝ) ≤ K * S * L := by
        have h3 : (2 * D * (1 + L)) * S + (D * D / ρ) * S ≤ (K * L) * S := by
          have h4 := mul_le_mul_of_nonneg_right hY2 hSpos.le
          rwa [add_mul] at h4
        nlinarith [hlogQ, hlogw, h3]
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hQpos) (ne_of_gt hwpos)]
      exact hmain
  have hfin : (q : ℝ) ≤ (2 : ℝ) ^ (K * S) := by
    have h1 : Real.log (q : ℝ) ≤ Real.log ((2 : ℝ) ^ (K * S)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2) (K * S)]
      simpa [hLdef] using hlog
    exact (Real.log_le_log_iff hqpos (Real.rpow_pos_of_pos (by norm_num) (K * S))).mp h1
  simpa [hSdef] using hfin

end Work.Analysis.IonescuWainger
