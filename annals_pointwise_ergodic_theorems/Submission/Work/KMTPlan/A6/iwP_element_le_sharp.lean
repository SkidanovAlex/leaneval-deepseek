import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Sharp element bound for the Ionescu–Wainger set `P_{≤l}`

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. 195 (2022), shows that every element of the IW
denominator set `P_{≤l}` is at most `2^{C_ρ (1 + l 2^{ρ l/2} + l)}` — i.e. only *linear* in
`l` times `2^{ρl/2}`, not fully exponential in `2^{ρl}`.

This is the sharp form of `Work.Analysis.IonescuWainger.iwP_element_le` (which loses a factor
by replacing `l` by `2^{ρl/2}` in the estimate for `N_0 log N_0`).  The proof repeats the
structural analysis of that file:

* for `l ≤ iwC0 ρ` we have `iwP ρ l = [1, 2^l]`, and `log q ≤ l log 2 ≤ C (1 + l 2^{ρl/2} + l)`;
* for `l > iwC0 ρ` every `q ∈ P_{≤l}` is `q = Q * w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`
  and `w ∈ W_{≤l}`.  Here `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1 ≤ 2 · 2^{ρl/2}`, so
  `log Q ≤ D_ρ · N_0 log N_0 ≤ 2 D_ρ (1 + ρl/2) 2^{ρl/2} log 2 ≤ 4 D_ρ (l 2^{ρl/2}) log 2`,
  while each element of `W_{≤l}` is a product of at most `D_ρ` distinct primes `≤ 2^l` taken to
  powers `≤ D_ρ`, hence at most `(2^l)^{D_ρ^2}`, giving `log w ≤ D_ρ^2 l log 2`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-! ## The factorisation of a product of primes to given powers -/

private theorem sh_factorization_prod_prime_pow {S : Finset ℕ} {e : ℕ → ℕ}
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (S.prod (fun p => p ^ e p)).factorization q = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun x hx => pow_ne_zero _ (hp x hx).ne_zero)]
  have key : ∀ p ∈ S, ((p ^ e p).factorization q) = if p = q then e p else 0 := by
    intro p hp'
    rw [(hp p hp').factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl key]
  simp

/-- The exponent of any prime in an element of `W_{≤l}` is at most `D_ρ`, and if it is nonzero
the prime lies in `(N_0^{(l)}, 2^l]`. -/
private theorem sh_factorization_le_of_mem_iwW {ρ : ℝ} {l w q : ℕ} (hw : w ∈ iwW ρ l) :
    w.factorization q ≤ if q ∈ iwPrimeRange ρ l then iwD ρ else 0 := by
  obtain ⟨hdvd, -⟩ := mem_iwW.mp hw
  classical
  have hle : w.factorization q ≤ (iwProd ρ l).factorization q :=
    Nat.factorization_le_factorization_of_dvd_right hdvd
      (pos_of_mem_iwW hw).ne' (iwProd_ne_zero ρ l)
  have hprod : (iwProd ρ l).factorization q
      = if q ∈ iwPrimeRange ρ l then iwD ρ else 0 :=
    sh_factorization_prod_prime_pow (fun p hp => (Finset.mem_filter.mp hp).2) q
  rw [hprod] at hle; exact hle

/-- **Element bound for `W_{≤l}`.**  An element of `W_{≤l}` is a product of at most `D_ρ`
distinct primes from `(N_0^{(l)}, 2^l]`, each taken to a power at most `D_ρ`, hence at most
`(2^l)^{D_ρ · D_ρ}`. -/
private theorem sh_iwW_le {ρ : ℝ} {l w : ℕ} (hw : w ∈ iwW ρ l) :
    w ≤ (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  classical
  have hw0 : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  have hfact : ∀ p, w.factorization p ≤ iwD ρ := by
    intro p
    have h := sh_factorization_le_of_mem_iwW hw (q := p)
    split_ifs at h with hmem
    · exact h
    · exact h.trans (Nat.zero_le _)
  have hple : ∀ p ∈ w.factorization.support, p ≤ 2 ^ l := by
    intro p hp
    have hne : w.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    by_cases hmem : p ∈ iwPrimeRange ρ l
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    · have h := sh_factorization_le_of_mem_iwW hw (q := p)
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

/-! ## The two logarithmic estimates -/

/-- **Logarithmic bound for `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`, sharp form.**  With
`N_0^{(l)} ≤ 2·2^{ρl/2}` and `N_0! ≤ N_0^{N_0}` we get
`log Q_0 ≤ D_ρ · N_0 log N_0 ≤ 4 D_ρ (l 2^{ρl/2}) log 2`. -/
private lemma sh_log_iwQ0_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (hl : 1 ≤ l) :
    Real.log (((iwQ0 ρ l : ℕ) : ℝ))
      ≤ 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by rw [htdef]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
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
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := le_of_lt (by linarith)
  have hchain : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ 4 * Real.log 2 * (l : ℝ) * t := by
    have h1 : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
        ≤ (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2) :=
      mul_le_mul hN0le hlogN0 hlogN0pos (by positivity)
    have h2 : (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2)
        = 2 * Real.log 2 * t * (1 + ρ * (l : ℝ) / 2) := by ring
    have h3 : 1 + ρ * (l : ℝ) / 2 ≤ 2 * (l : ℝ) := by
      have h41 : ρ * (l : ℝ) ≤ (l : ℝ) := by
        have := mul_le_mul_of_nonneg_right hρ1 hl0
        simpa using this
      linarith [h41, hl1]
    have h4 : (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2)
        ≤ 2 * Real.log 2 * t * (2 * (l : ℝ)) := by
      rw [h2]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * Real.log 2 * t * (2 * (l : ℝ)) = 4 * Real.log 2 * (l : ℝ) * t := by ring
    linarith [h1, h4, h5.le, h5.ge]
  rw [iwQ0, Nat.cast_pow, Real.log_pow]
  have hstep1 : (iwD ρ : ℝ) * Real.log (((iwN0 ρ l).factorial : ℕ) : ℝ)
      ≤ (iwD ρ : ℝ) * (((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hfact hD0
  have hfinle : (iwD ρ : ℝ) * (((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ))
      ≤ (iwD ρ : ℝ) * (4 * Real.log 2 * (l : ℝ) * t) :=
    mul_le_mul_of_nonneg_left hchain hD0
  have e : 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2)
      = (iwD ρ : ℝ) * (4 * Real.log 2 * (l : ℝ) * t) := by rw [htdef]; ring
  rw [e]
  linarith [hstep1, hfinle]

/-- **Logarithmic bound for `W_{≤l}`.** -/
private lemma sh_log_iwW_le {ρ : ℝ} {l w : ℕ} (hw : w ∈ iwW ρ l) :
    Real.log ((w : ℕ) : ℝ) ≤ (iwD ρ : ℝ) * (iwD ρ : ℝ) * (Real.log 2 * (l : ℝ)) := by
  have hwpos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast pos_of_mem_iwW hw
  have h1 : Real.log ((w : ℕ) : ℝ) ≤ Real.log ((((2 ^ l) ^ (iwD ρ * iwD ρ) : ℕ)) : ℝ) :=
    Real.log_le_log hwpos (by exact_mod_cast sh_iwW_le hw)
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow] at h1
  push_cast at h1
  nlinarith [h1]

/-! ## The element bound -/

/-- Every element of `iwP ρ l = P_{≤l}` is bounded by `2^{C (1 + l 2^{ρ l / 2} + l)}`. -/
theorem iwP_element_le_sharp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l q, q ∈ Work.Analysis.IonescuWainger.iwP ρ l →
      (q : ℝ) ≤ (2 : ℝ) ^ (C * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))) := by
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLle : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hD1 : 1 ≤ (iwD ρ : ℝ) := by
    have : 1 ≤ iwD ρ := by rw [iwD]; exact Nat.le_add_left 1 _
    exact_mod_cast this
  have hD0 : (0 : ℝ) ≤ (iwD ρ : ℝ) := le_of_lt (by linarith)
  set Kr : ℝ := (4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ) + 1) / Real.log 2 with hK
  have hKrpos : 0 < Kr := by
    rw [hK]; exact div_pos (by nlinarith [hD1]) hLpos
  have hKrL : Kr * Real.log 2 = 4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ) + 1 := by
    rw [hK, div_mul_cancel₀ _ (ne_of_gt hLpos)]
  have hKrLle : Kr * Real.log 2 ≤ Kr := by
    have h := mul_le_mul_of_nonneg_left hLle (le_of_lt hKrpos)
    simpa using h
  have hKr1 : 1 ≤ Kr := by
    have hnum : (1 : ℝ) ≤ 4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ) + 1 := by
      nlinarith [hD1]
    linarith [hKrLle, hKrL, hnum]
  refine ⟨Kr, hKrpos, ?_⟩
  intro l q hq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast pos_of_mem_iwP hq
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht0 : 0 ≤ t := le_of_lt htpos
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have hgoal : Real.log (q : ℝ) ≤ Kr * (1 + (l : ℝ) * t + (l : ℝ)) * Real.log 2 := by
    rw [mem_iwP] at hq
    rcases hq with ⟨-, hq1, hq2⟩ | ⟨hlt, hqP⟩
    · -- regime `l ≤ iwC0 ρ`: `q ≤ 2 ^ l`
      have h1 : Real.log (q : ℝ) ≤ (l : ℝ) * Real.log 2 := by
        have hq2R : (q : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by exact_mod_cast hq2
        have h := Real.log_le_log hqpos hq2R
        rw [Nat.cast_pow, Real.log_pow] at h
        push_cast at h
        exact h
      have hlt1 : (l : ℝ) ≤ 1 + (l : ℝ) * t + (l : ℝ) := by
        have h : 0 ≤ (l : ℝ) * t := mul_nonneg hl0 ht0
        linarith
      have hnonneg : 0 ≤ 1 + (l : ℝ) * t + (l : ℝ) := by
        have h : 0 ≤ (l : ℝ) * t := mul_nonneg hl0 ht0
        linarith
      have h2 : (l : ℝ) ≤ Kr * (1 + (l : ℝ) * t + (l : ℝ)) := by
        calc (l : ℝ) ≤ 1 * (1 + (l : ℝ) * t + (l : ℝ)) := by rw [one_mul]; exact hlt1
          _ ≤ Kr * (1 + (l : ℝ) * t + (l : ℝ)) := mul_le_mul_of_nonneg_right hKr1 hnonneg
      have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hLpos)
      linarith [h1, h3]
    · -- regime `l > iwC0 ρ`: `q = Q * w`
      have hl : 1 ≤ l := by omega
      obtain ⟨Q, hQ, w, hw, rfl⟩ := mem_iwPconcrete.mp hqP
      obtain ⟨hdvd, hQ0ne⟩ := Nat.mem_divisors.mp hQ
      have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hQ
      have hwpos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast pos_of_mem_iwW hw
      have hlogQ : Real.log (Q : ℝ) ≤ 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * t := by
        have hQle : Q ≤ iwQ0 ρ l := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0ne) hdvd
        have h1 : Real.log (Q : ℝ) ≤ Real.log (((iwQ0 ρ l : ℕ) : ℝ)) :=
          Real.log_le_log hQpos (by exact_mod_cast hQle)
        have h2 := sh_log_iwQ0_le hρ hρ1 hl
        rw [← htdef] at h2
        linarith [h1, h2]
      have hlogw : Real.log (w : ℝ) ≤ (iwD ρ : ℝ) * (iwD ρ : ℝ) * (Real.log 2 * (l : ℝ)) :=
        sh_log_iwW_le hw
      have hKrL2 : Kr * (1 + (l : ℝ) * t + (l : ℝ)) * Real.log 2
          = (4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ) + 1)
            * (1 + (l : ℝ) * t + (l : ℝ)) := by
        rw [mul_assoc, mul_comm (1 + (l : ℝ) * t + (l : ℝ)) (Real.log 2), ← mul_assoc, hKrL]
      have hnonneg : 0 ≤ 1 + (l : ℝ) * t + (l : ℝ) := by
        have h : 0 ≤ (l : ℝ) * t := mul_nonneg hl0 ht0
        linarith
      have hkey : 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * t
            + (iwD ρ : ℝ) * (iwD ρ : ℝ) * (Real.log 2 * (l : ℝ))
            ≤ Kr * (1 + (l : ℝ) * t + (l : ℝ)) * Real.log 2 := by
        rw [hKrL2]
        have htl : t * (l : ℝ) ≤ 1 + (l : ℝ) * t + (l : ℝ) := by
          have h : 0 ≤ (l : ℝ) * t := mul_nonneg hl0 ht0
          nlinarith [h]
        have hl_le : (l : ℝ) ≤ 1 + (l : ℝ) * t + (l : ℝ) := by
          have h : 0 ≤ (l : ℝ) * t := mul_nonneg hl0 ht0
          linarith
        have f1 : 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * t
            ≤ 4 * (iwD ρ : ℝ) * ((l : ℝ) * t) := by
          have e : 4 * (iwD ρ : ℝ) * Real.log 2 * (l : ℝ) * t
              = (4 * (iwD ρ : ℝ) * ((l : ℝ) * t)) * Real.log 2 := by ring
          rw [e]
          exact mul_le_of_le_one_right (by positivity) hLle
        have f2 : 4 * (iwD ρ : ℝ) * ((l : ℝ) * t)
            ≤ 4 * (iwD ρ : ℝ) * (1 + (l : ℝ) * t + (l : ℝ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [htl]) (by positivity)
        have f3 : (iwD ρ : ℝ) * (iwD ρ : ℝ) * (Real.log 2 * (l : ℝ))
            ≤ (iwD ρ : ℝ) * (iwD ρ : ℝ) * (l : ℝ) := by
          have e : (iwD ρ : ℝ) * (iwD ρ : ℝ) * (Real.log 2 * (l : ℝ))
              = ((iwD ρ : ℝ) * (iwD ρ : ℝ) * (l : ℝ)) * Real.log 2 := by ring
          rw [e]
          exact mul_le_of_le_one_right (by positivity) hLle
        have f4 : (iwD ρ : ℝ) * (iwD ρ : ℝ) * (l : ℝ)
            ≤ (iwD ρ : ℝ) * (iwD ρ : ℝ) * (1 + (l : ℝ) * t + (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hl_le (by positivity)
        have f5 : (4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ)) * (1 + (l : ℝ) * t + (l : ℝ))
            ≤ (4 * (iwD ρ : ℝ) + (iwD ρ : ℝ) * (iwD ρ : ℝ) + 1)
              * (1 + (l : ℝ) * t + (l : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hnonneg
          linarith
        linarith [f1, f2, f3, f4, f5]
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hQpos) (ne_of_gt hwpos)]
      linarith [hlogQ, hlogw, hkey]
  have hfin : (q : ℝ) ≤ (2 : ℝ) ^ (Kr * (1 + (l : ℝ) * t + (l : ℝ))) := by
    have h1 : Real.log (q : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (Kr * (1 + (l : ℝ) * t + (l : ℝ)))) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      exact hgoal
    exact (Real.log_le_log_iff hqpos (Real.rpow_pos_of_pos (by norm_num) _)).mp h1
  simpa only [htdef] using hfin

end Work.KMTPlan.A6
