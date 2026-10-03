import Mathlib

namespace Work.FIArea4

open Finset

/-- Möbius inversion in divisorial form: the sum of the Möbius function over the divisors
of `m` is the indicator of `m = 1`.  Immediate from `μ * ζ = 1` and
`(f * ζ) m = ∑ d ∣ m, f d`. -/
lemma sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) = if m = 1 then 1 else 0 := by
  have h : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ)
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) m :=
    (ArithmeticFunction.coe_mul_zeta_apply
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℂ))).symm
  rw [h, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The radical `rad c = ∏ p ∈ c.primeFactors, p` of a nonzero `c` has exactly the same
prime divisors as `c`, hence `n` is coprime to `rad c` iff it is coprime to `c`. -/
lemma coprime_radical {c : ℕ} (hc : c ≠ 0) (n : ℕ) :
    n.gcd (∏ p ∈ c.primeFactors, p) = 1 ↔ n.gcd c = 1 := by
  rw [← Nat.coprime_iff_gcd_eq_one, ← Nat.coprime_iff_gcd_eq_one]
  have hR0 : (∏ p ∈ c.primeFactors, p) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hpf : (∏ p ∈ c.primeFactors, p).primeFactors = c.primeFactors :=
    Nat.primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have hdiv : ∀ p : ℕ, Nat.Prime p → (p ∣ ∏ p ∈ c.primeFactors, p ↔ p ∣ c) := by
    intro p hp
    have h1 : p ∈ (∏ p ∈ c.primeFactors, p).primeFactors ↔ p ∣ ∏ p ∈ c.primeFactors, p :=
      (Nat.mem_primeFactors_of_ne_zero hR0).trans (and_iff_right hp)
    have h2 : p ∈ c.primeFactors ↔ p ∣ c :=
      (Nat.mem_primeFactors_of_ne_zero hc).trans (and_iff_right hp)
    rw [← h1, ← h2, hpf]
  rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨p, hp, hpn, hpr⟩
    exact ⟨p, hp, hpn, (hdiv p hp).mp hpr⟩
  · rintro ⟨p, hp, hpn, hpc⟩
    exact ⟨p, hp, hpn, (hdiv p hp).mpr hpc⟩

/-- The Möbius sieve: `∑_{d ∣ rad c} μ(d) [d ∣ n] = [gcd(n,c) = 1]`, i.e. the coprimality
indicator of `n` to `c` is the Möbius sum over the divisors of the radical of `c`. -/
lemma sum_ite_dvd_moebius {c : ℕ} (hc : c ≠ 0) (n : ℕ) :
    ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
        (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0)
      = if n.gcd c = 1 then 1 else 0 := by
  have hR0 : (∏ p ∈ c.primeFactors, p) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hfilt : (∏ p ∈ c.primeFactors, p).divisors.filter (fun d => d ∣ n)
      = (n.gcd (∏ p ∈ c.primeFactors, p)).divisors := by
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdR, -⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdR, Nat.gcd_ne_zero_right hR0⟩
    · rintro ⟨hdg, -⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_right n _), hR0⟩, hdg.trans (Nat.gcd_dvd_left n _)⟩
  rw [← Finset.sum_filter, hfilt, sum_moebius_divisors]
  by_cases h : n.gcd c = 1
  · rw [if_pos h, if_pos ((coprime_radical hc n).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((coprime_radical hc n).mp h'))]

/-- Reindexing a range sum restricted to the multiples of `d` by writing `n = d * n'`. -/
lemma sum_Icc_filter_dvd_eq {d N : ℕ} (hd : 0 < d) (g : ℕ → ℂ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), g n
      = ∑ n' ∈ Finset.Icc 1 (N / d), g (d * n') := by
  refine (Finset.sum_bij (f := fun n' => g (d * n')) (g := g)
    (s := Finset.Icc 1 (N / d)) (t := (Finset.Icc 1 N).filter (fun n => d ∣ n))
    (fun n' _ => d * n') ?_ ?_ ?_ ?_).symm
  · intro n' hn'
    simp only [Finset.mem_Icc] at hn'
    obtain ⟨h1, h2⟩ := hn'
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right d n'⟩
    · simpa using Nat.mul_le_mul hd h1
    · have := (Nat.le_div_iff_mul_le hd).mp h2
      simpa [Nat.mul_comm] using this
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hbN⟩, hdb⟩ := hb
    refine ⟨b / d, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨?_, Nat.div_le_div_right hbN⟩
      rw [Nat.le_div_iff_mul_le hd]
      simpa using Nat.le_of_dvd (by omega) hdb
    · exact Nat.mul_div_cancel' hdb
  · intro _ _
    rfl

/-- **Coprimality sieve (Möbius).** For a completely multiplicative `f : ℕ → ℂ` with `f 1 = 1`
and `c ≠ 0`, the sum over `n ≤ N` coprime to `c` equals the finite combination
`∑_{d | rad c} μ(d) f(d) ∑_{n' ≤ N/d} f(n')`, where `rad c = ∏ p ∈ c.primeFactors, p`.
Proof: replace the coprimality indicator by `∑_{d ∣ gcd(n, rad c)} μ(d)` (Möbius inversion:
`∑_{d ∣ r} μ(d) = if r = 1 then 1 else 0`), swap the two finite sums, and use
`f (d * n') = f d * f n'` together with the reindexing `n = d * n'`. -/
theorem sum_coprime_mul_eq {c N : ℕ} (hc : c ≠ 0) (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.gcd c = 1), f n
      = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          (ArithmeticFunction.moebius d : ℂ) * f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
  have _hf1 : f 1 = 1 := hf1
  calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.gcd c = 1), f n
      = ∑ n ∈ Finset.Icc 1 N, (if n.gcd c = 1 then f n else 0) :=
        Finset.sum_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 N,
          f n * (∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
                    (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [sum_ite_dvd_moebius hc n]
        by_cases h : n.gcd c = 1 <;> simp [h]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.mul_sum]
    _ = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors, ∑ n ∈ Finset.Icc 1 N,
          f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          (ArithmeticFunction.moebius d : ℂ) * f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        have hstep : ∑ n ∈ Finset.Icc 1 N,
              f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0)
            = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f n)
              * (ArithmeticFunction.moebius d : ℂ) := by
          rw [Finset.sum_mul, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : d ∣ n <;> simp [h]
        rw [hstep, sum_Icc_filter_dvd_eq hdpos f]
        have hsum : ∑ n' ∈ Finset.Icc 1 (N / d), f (d * n')
            = f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n' _
          rw [hfmul]
        rw [hsum]
        ring

end Work.FIArea4
