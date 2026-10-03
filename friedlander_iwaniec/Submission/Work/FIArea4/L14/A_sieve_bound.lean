import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.sum_coprime_mul_eq

namespace Work.FIArea4.L14

open Finset

set_option linter.style.haveILetI false

/-! ### Real-valued Möbius sieve

We need the sieve with **real** values (the target inequality is over `ℝ`), so we reproduce the
ℂ-valued lemmas of `Work.FIArea4.sum_coprime_mul_eq` in `ℝ` (they are ring-agnostic). -/

/-- The sum of the Möbius function over the divisors of `m` is the indicator of `m = 1`. -/
lemma sum_moebius_divisors_real (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) = if m = 1 then 1 else 0 := by
  have h : ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ)
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta) m :=
    (ArithmeticFunction.coe_mul_zeta_apply
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ))).symm
  rw [h, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- `n` is coprime to `rad c = ∏ p ∈ c.primeFactors, p` iff it is coprime to `c`. -/
lemma coprime_radical_real {c : ℕ} (hc : c ≠ 0) (n : ℕ) :
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

/-- The coprimality indicator of `n` to `c` as a Möbius sum over the divisors of `rad c`. -/
lemma sum_ite_dvd_moebius_real {c : ℕ} (hc : c ≠ 0) (n : ℕ) :
    ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
        (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)
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
  rw [← Finset.sum_filter, hfilt, sum_moebius_divisors_real]
  by_cases h : n.gcd c = 1
  · rw [if_pos h, if_pos ((coprime_radical_real hc n).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((coprime_radical_real hc n).mp h'))]

/-- Reindexing a range sum restricted to the multiples of `d` by `n = d * n'` (any additive
commutative monoid, in particular `ℝ`). -/
lemma sum_Icc_filter_dvd_eq_gen {M : Type*} [AddCommMonoid M] {d N : ℕ} (hd : 0 < d)
    (g : ℕ → M) :
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

/-- **Real Möbius coprimality sieve.** For a completely multiplicative `f : ℕ → ℝ` with
`f 1 = 1` and `c ≠ 0`, the sum over `n ≤ N` coprime to `c` equals
`∑_{d | rad c} μ(d) f(d) ∑_{n' ≤ N/d} f(n')`. -/
theorem sum_coprime_mul_eq_real {c N : ℕ} (hc : c ≠ 0) (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.gcd c = 1), f n
      = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          (ArithmeticFunction.moebius d : ℝ) * f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
  have _hf1 : f 1 = 1 := hf1
  calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.gcd c = 1), f n
      = ∑ n ∈ Finset.Icc 1 N, (if n.gcd c = 1 then f n else 0) := Finset.sum_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 N,
          f n * (∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
                    (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [sum_ite_dvd_moebius_real hc n]
        by_cases h : n.gcd c = 1 <;> simp [h]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.mul_sum]
    _ = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors, ∑ n ∈ Finset.Icc 1 N,
          f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ (∏ p ∈ c.primeFactors, p).divisors,
          (ArithmeticFunction.moebius d : ℝ) * f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        have hstep : ∑ n ∈ Finset.Icc 1 N,
              f n * (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)
            = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f n)
              * (ArithmeticFunction.moebius d : ℝ) := by
          rw [Finset.sum_mul, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : d ∣ n <;> simp [h]
        rw [hstep, sum_Icc_filter_dvd_eq_gen hdpos f]
        have hsum : ∑ n' ∈ Finset.Icc 1 (N / d), f (d * n')
            = f d * ∑ n' ∈ Finset.Icc 1 (N / d), f n' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n' _
          rw [hfmul]
        rw [hsum]
        ring

/-! ### The character identity on the `e`-part -/

/-- `J(n | b)² = [gcd(n,b) = 1]` for `b ≠ 0`: the Jacobi symbol is `±1` on coprime arguments
and `0` otherwise. -/
lemma jacobiSym_sq_eq_ite_coprime (n b : ℕ) (hb : b ≠ 0) :
    (jacobiSym (n : ℤ) b) ^ 2 = if n.gcd b = 1 then 1 else 0 := by
  haveI : NeZero b := ⟨hb⟩
  by_cases h : n.gcd b = 1
  · rw [if_pos h]
    have hg : ((n : ℤ).gcd (b : ℤ)) = 1 := by rw [Int.gcd_natCast_natCast]; exact h
    rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1 <;> rw [h1] <;> norm_num
  · rw [if_neg h]
    have hg : ((n : ℤ).gcd (b : ℤ)) ≠ 1 := by rw [Int.gcd_natCast_natCast]; exact h
    rw [jacobiSym.eq_zero_iff_not_coprime.mpr hg]
    norm_num

/-- Since `(r | e'²b₁'b₂') = (r | e'²)(r | b₁'b₂') = [gcd(r,e') = 1] · (r | b₁'b₂')`. -/
lemma jacobiSym_oddPart_mul_eq (e b1 b2 : ℕ) (he : 1 ≤ e)
    (hm0 : Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2 ≠ 0) (n : ℕ) :
    jacobiSym (n : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2))
      = (if n.gcd (Work.FIPlan.oddPart e) = 1 then 1 else 0)
          * jacobiSym (n : ℤ) (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) := by
  have hene : e ≠ 0 := by omega
  have hEne : Work.FIPlan.oddPart e ≠ 0 := (Nat.ordCompl_pos 2 hene).ne'
  have h1 : Work.FIPlan.oddPart (e * b1) = Work.FIPlan.oddPart e * Work.FIPlan.oddPart b1 :=
    Nat.ordCompl_mul e b1 2
  have h2 : Work.FIPlan.oddPart (e * b2) = Work.FIPlan.oddPart e * Work.FIPlan.oddPart b2 :=
    Nat.ordCompl_mul e b2 2
  have hmod : Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)
      = Work.FIPlan.oddPart e ^ 2 * (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) := by
    rw [h1, h2]; ring
  rw [hmod, jacobiSym.mul_right' (n : ℤ) (pow_ne_zero 2 hEne) hm0, jacobiSym.pow_right,
      jacobiSym_sq_eq_ite_coprime n (Work.FIPlan.oddPart e) hEne]

/-! ### The sieve bound -/

/-- The Möbius sieve plus Cauchy–Schwarz, abstractly: if the character `J(·|M)` factors through
the coprimality indicator to `e' = E` and the character `J(·|m₀)`, then the squared partial sum
of `J(·|M)` is bounded by `#(rad E).divisors` times the sum of the squared partial sums of
`J(·|m₀)`. -/
lemma sieve_bound_general (E m0 M R : ℕ) (hE : E ≠ 0) (_hm0 : m0 ≠ 0)
    (hpt : ∀ r : ℕ, jacobiSym (r : ℤ) M
      = (if r.gcd E = 1 then 1 else 0) * jacobiSym (r : ℤ) m0) :
    (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) M : ℝ))^2
      ≤ (((∏ p ∈ E.primeFactors, p).divisors.card : ℝ)) *
        ∑ d ∈ (∏ p ∈ E.primeFactors, p).divisors,
          (∑ m ∈ Finset.Icc 1 (R / d),
            (jacobiSym (m : ℤ) m0 : ℝ))^2 := by
  set F : ℕ → ℝ := fun m => (jacobiSym (m : ℤ) m0 : ℝ) with hF
  have hF1 : F 1 = 1 := by simp only [hF]; simp
  have hFmul : ∀ a b : ℕ, F (a * b) = F a * F b := by
    intro a b; simp only [hF]; push_cast; rw [jacobiSym.mul_left]; push_cast; rfl
  have hptR : ∀ r : ℕ, (jacobiSym (r : ℤ) M : ℝ)
      = (if r.gcd E = 1 then (1 : ℝ) else 0) * F r := by
    intro r
    simp only [hF]
    rw [hpt r]
    by_cases h : r.gcd E = 1 <;> simp [h]
  have hL : ∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) M : ℝ)
      = ∑ r ∈ (Finset.Icc 1 R).filter (fun r => r.gcd E = 1), F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    rw [hptR r]
    by_cases h : r.gcd E = 1 <;> simp [h]
  have hterm : ∀ d, ((ArithmeticFunction.moebius d : ℝ) * F d)^2 ≤ 1 := by
    intro d
    have h1 : (ArithmeticFunction.moebius d : ℝ)^2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num
    have h2 : (F d)^2 ≤ 1 := by
      have := jacobiSym.trichotomy (d : ℤ) m0
      simp only [hF] at this ⊢
      rcases this with h | h | h <;> rw [h] <;> norm_num
    have hmul : ((ArithmeticFunction.moebius d : ℝ) * F d)^2
        = (ArithmeticFunction.moebius d : ℝ)^2 * (F d)^2 := by ring
    rw [hmul]
    nlinarith [sq_nonneg (ArithmeticFunction.moebius d : ℝ), sq_nonneg (F d)]
  rw [hL, sum_coprime_mul_eq_real hE F hF1 hFmul]
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq (∏ p ∈ E.primeFactors, p).divisors
      (fun d => (ArithmeticFunction.moebius d : ℝ) * F d)
      (fun d => ∑ m ∈ Finset.Icc 1 (R / d), F m)) ?_
  apply mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun d _ => sq_nonneg _))
  calc (∑ d ∈ (∏ p ∈ E.primeFactors, p).divisors,
          ((ArithmeticFunction.moebius d : ℝ) * F d)^2)
      ≤ ∑ d ∈ (∏ p ∈ E.primeFactors, p).divisors, (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ = (((∏ p ∈ E.primeFactors, p).divisors.card : ℝ)) := by simp

/-- Möbius sieve on the `e`-part of the Jacobi modulus: for `e ≥ 1`, put `e' = oddPart e`. Since
`(r | e'² b₁'b₂') = (r | b₁'b₂') · [(r,e')=1]`, the full character sum over `r ≤ R` equals the
coprimality-restricted sum, and the Möbius sieve (`Work.FIArea4.sum_coprime_mul_eq`, applied to
`f r = (r | b₁'b₂')`) plus Cauchy–Schwarz gives the stated bound. -/
theorem A_sieve_bound (e b1 b2 R : ℕ) (he : 1 ≤ e) :
    (∑ r ∈ Finset.Icc 1 R,
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) : ℝ))^2
      ≤ (((∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors.card : ℝ)) *
        ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
          (∑ m ∈ Finset.Icc 1 (R / d),
            (jacobiSym (m : ℤ) (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) : ℝ))^2
    := by
  have hene : e ≠ 0 := by omega
  have hEne : Work.FIPlan.oddPart e ≠ 0 := (Nat.ordCompl_pos 2 hene).ne'
  by_cases hm0 : Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2 = 0
  · -- degenerate case: `b₁' b₂' = 0`, so both moduli vanish
    have hmod : Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2) = 0 := by
      have h1 : Work.FIPlan.oddPart (e * b1) = Work.FIPlan.oddPart e * Work.FIPlan.oddPart b1 :=
        Nat.ordCompl_mul e b1 2
      have h2 : Work.FIPlan.oddPart (e * b2) = Work.FIPlan.oddPart e * Work.FIPlan.oddPart b2 :=
        Nat.ordCompl_mul e b2 2
      have h3 : Work.FIPlan.oddPart e * Work.FIPlan.oddPart b1
          * (Work.FIPlan.oddPart e * Work.FIPlan.oddPart b2)
          = Work.FIPlan.oddPart e ^ 2 * (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) := by
        ring
      rw [h1, h2, h3, hm0]; ring
    have hLHS : ∑ r ∈ Finset.Icc 1 R,
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) : ℝ)
        = ((R : ℕ) : ℝ) := by
      rw [hmod]
      simp [jacobiSym.zero_right, Nat.card_Icc]
    have hrad0 : (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.ne_zero
    have h1mem : (1 : ℕ) ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors :=
      Nat.one_mem_divisors.mpr hrad0
    have hinner : ∀ d : ℕ, (∑ m ∈ Finset.Icc 1 (R / d),
        (jacobiSym (m : ℤ) (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) : ℝ))
        = (((R / d : ℕ)) : ℝ) := by
      intro d
      rw [hm0]
      simp [jacobiSym.zero_right, Nat.card_Icc]
    have hsum_eq : ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
        (∑ m ∈ Finset.Icc 1 (R / d),
          (jacobiSym (m : ℤ) (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) : ℝ))^2
        = ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
            ((((R / d : ℕ)) : ℝ))^2 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hinner d]
    have hsingle : (((R : ℕ)) : ℝ)^2
        ≤ ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
            ((((R / d : ℕ)) : ℝ))^2 := by
      have := Finset.single_le_sum
        (s := (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors)
        (f := fun d => ((((R / d : ℕ)) : ℝ))^2) (fun i _ => sq_nonneg _) h1mem
      simpa using this
    have hcard_ge : (1 : ℝ)
        ≤ (((∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors.card : ℝ)) := by
      have : 0 < (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors.card :=
        Finset.card_pos.mpr ⟨1, h1mem⟩
      exact_mod_cast this
    rw [hLHS, hsum_eq]
    calc (((R : ℕ)) : ℝ)^2
        ≤ ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
            ((((R / d : ℕ)) : ℝ))^2 := hsingle
      _ = (1 : ℝ) * ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
            ((((R / d : ℕ)) : ℝ))^2 := by rw [one_mul]
      _ ≤ (((∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors.card : ℝ)) *
            ∑ d ∈ (∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p).divisors,
              ((((R / d : ℕ)) : ℝ))^2 :=
          mul_le_mul_of_nonneg_right hcard_ge (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · -- main case: `b₁'b₂' ≠ 0`
    exact sieve_bound_general (Work.FIPlan.oddPart e)
      (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2)
      (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) R hEne hm0
      (jacobiSym_oddPart_mul_eq e b1 b2 he hm0)

end Work.FIArea4.L14
