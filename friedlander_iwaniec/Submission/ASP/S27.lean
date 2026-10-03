/-
  **The companion's Theorem 2, wired up for the Friedlander–Iwaniec sequence.**

  `S12.TheoremOne_of_estimates` gives the prime-sum asymptotic for the squarefree-supported
  sequence `ã = atil FIa` (Theorem 1), and `S9f.transfer_abs` transfers it back to `FIa`
  (Theorem 2), using

    * `Htil · G = H`, and
    * the companion's (9.12):  `|Acount ã(x) − G·Acount a(x)| ≤ G·Acount a(x)·δ`.

  Hence the *only* inputs left for the prime-sum asymptotic of `FIa` are the five estimates
  (4.5), (5.1), (6.6), (7.2), (8.5) applied to `ã` — which is the standard reduction of the
  companion's machine to `(B′)` and the Selberg-sieve axioms — together with (9.12).
-/
import Mathlib
import Submission.ASP.S26
import Submission.ASP.Smooth
import Submission.ASP.S11
import Submission.ASP.S9f
import Submission.ASP.S9h
import Submission.Final
import Submission.Commons.NumberTheory.FriedlanderIwaniec.ncard_int_pow_two_add_pow_four_prime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_prime_sq_le_half

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

lemma FIa_nonneg (n : ℕ) : 0 ≤ FIa n := by
  rw [FIa]; exact_mod_cast Nat.zero_le _

/-! ## The link with `Final.lean`'s `apos` / `primeSum` -/

/-- For a prime `p`, every solution of `a² + c⁴ = p` has `a ≠ 0 ≠ c`, and `(a,c) ↦ (|a|,|c|)`
is exactly 4-to-1 onto the *positive* solutions; hence `an p = 4·apos p`. -/
theorem an_prime_eq_four_mul_apos {p : ℕ} (hp : p.Prime) :
    Submission.an p = 4 * Submission.apos p :=
  Commons.NumberTheory.FriedlanderIwaniec.ncard_int_pow_two_add_pow_four_prime hp

/-- `Final.lean`'s prime sum is a quarter of the companion's prime sum for `FIa`. -/
theorem primeSum_eq_quarter (N : ℕ) :
    primeSum N
      = (1/4) * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * FIa p := by
  rw [primeSum, Nat.primesBelow_eq_filter_range]
  have hset : (Finset.range (N + 1)).filter Nat.Prime
      = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨le_trans (by norm_num) h2.two_le, Nat.lt_succ_iff.mp h1⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Nat.lt_succ_iff.mpr h2, h3⟩
  rw [hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [FIa, an_prime_eq_four_mul_apos hp.2]
  push_cast
  ring

/-! ## The density `g̃` of the squarefree-supported sequence `ã = atil FIa` -/

/-- The density of `ã`: `g̃(d) = ∏_{p ∣ d} (g(p) − g(p²))/(1 − g(p²))` for squarefree `d`, `0`
otherwise.  (`S9h.gtilVal` is the Euler factor at one prime.) -/
noncomputable def FIgtil (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, gtilVal FIg p else 0

lemma FIgtil_one : FIgtil 1 = 1 := by
  rw [FIgtil, if_pos squarefree_one, Nat.primeFactors_one, Finset.prod_empty]

lemma FIgtil_eq_zero {d : ℕ} (h : ¬ Squarefree d) : FIgtil d = 0 := by
  rw [FIgtil, if_neg h]

lemma FIgtil_prime {p : ℕ} (hp : p.Prime) : FIgtil p = gtilVal FIg p := by
  rw [FIgtil, if_pos hp.prime.squarefree, hp.primeFactors, Finset.prod_singleton]

lemma FIgtil_nonneg (d : ℕ) : 0 ≤ FIgtil d := by
  rw [FIgtil]
  by_cases h : Squarefree d
  · rw [if_pos h]
    refine Finset.prod_nonneg fun p hp => ?_
    obtain ⟨hp1, -, -⟩ := Nat.mem_primeFactors.mp hp
    exact gtilVal_nonneg (FIg_nonneg (p ^ 2))
      (FI_gdens_prime_sq_le p hp1).1 (FI_gdens_prime_nonneg hp1).2
  · rw [if_neg h]

lemma not_squarefree_zero : ¬ Squarefree (0:ℕ) := by
  intro h
  have h1 : IsUnit (2:ℕ) := h 2 (by norm_num)
  have h2 : (2:ℕ) ∣ 1 := h1.dvd
  omega

lemma FIgtil_mul {m n : ℕ} (h : m.Coprime n) :
    FIgtil (m * n) = FIgtil m * FIgtil n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h
    subst h
    rw [mul_one, FIgtil_one, mul_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    subst h
    rw [one_mul, FIgtil_one, FIgtil_eq_zero not_squarefree_zero, mul_zero]
  by_cases hmn : Squarefree (m * n)
  · obtain ⟨-, hsm, hsn⟩ := Nat.squarefree_mul_iff.mp hmn
    simp only [FIgtil, if_pos hmn, if_pos hsm, if_pos hsn, Nat.primeFactors_mul hm hn]
    rw [Finset.prod_union ((Nat.disjoint_primeFactors hm hn).mpr h)]
  · have hnot : ¬ (Squarefree m ∧ Squarefree n) :=
      fun hh => hmn (Nat.squarefree_mul_iff.mpr ⟨h, hh.1, hh.2⟩)
    by_cases hmm : Squarefree m
    · have hnn : ¬ Squarefree n := fun hn' => hnot ⟨hmm, hn'⟩
      rw [FIgtil_eq_zero hmn, FIgtil_eq_zero hnn, mul_zero]
    · rw [FIgtil_eq_zero hmn, FIgtil_eq_zero hmm, zero_mul]

lemma FIg_prime_sq_le_half {p : ℕ} (hp : p.Prime) : FIg (p ^ 2) ≤ 1/2 := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.gdens_prime_sq_le_half (p := p) hp
  have h2 : ((Submission.gdens (p ^ 2) : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast h
  simpa [FIg] using h2

lemma FIgtil_lt_one {p : ℕ} (hp : p.Prime) : FIgtil p < 1 := by
  rw [FIgtil_prime hp]
  exact gtilVal_lt_one (FI_gdens_prime_nonneg hp).2 (by
    have h := FIg_prime_sq_le_half hp
    linarith)

lemma FIgtil_bound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → FIgtil p ≤ C / (p : ℝ) := by
  obtain ⟨C0, hC0, hC0'⟩ := FI_gdens_bound
  refine ⟨2 * C0, by positivity, fun p hp => ?_⟩
  rw [FIgtil_prime hp]
  have h1 : gtilVal FIg p ≤ 2 * C0 / (p : ℝ) :=
    gtilVal_le (g := FIg) (p := p) hC0.le (hC0' p hp) (FIg_nonneg (p ^ 2))
      (FIg_prime_sq_le_half hp)
  linarith [h1]

/-! ## (1.9) for the density `g̃` -/

/-- `g(p) − g̃(p) ≥ 0`, with the exact form `g(p²)(1−g(p))/(1−g(p²))`. -/
lemma FIgtil_correction_eq {p : ℕ} (hp : p.Prime) :
    FIg p - gtilVal FIg p = FIg (p ^ 2) * (1 - FIg p) / (1 - FIg (p ^ 2)) :=
  sub_gtilVal_eq FIg (by have h := FIg_prime_sq_le_half hp; linarith)

lemma FIgtil_correction_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ FIg p - gtilVal FIg p := by
  rw [FIgtil_correction_eq hp]
  refine div_nonneg (mul_nonneg (FIg_nonneg _) (by linarith [(FI_gdens_prime_nonneg hp).2])) ?_
  have h := FIg_prime_sq_le_half hp
  linarith

lemma FIgtil_correction_le {p : ℕ} (hp : p.Prime) :
    FIg p - gtilVal FIg p ≤ 8 / (p : ℝ) ^ 2 := by
  rw [FIgtil_correction_eq hp]
  have hp0 : (0:ℝ) ≤ 1 - FIg p := by linarith [(FI_gdens_prime_nonneg hp).2]
  have hp1 : (0:ℝ) < 1 - FIg (p ^ 2) := by
    have h := FIg_prime_sq_le_half hp
    linarith
  have hden : 1 / 2 ≤ 1 - FIg (p ^ 2) := by
    have h := FIg_prime_sq_le_half hp
    linarith
  have hnum : FIg (p ^ 2) * (1 - FIg p) ≤ FIg (p ^ 2) := by
    have h1 : (1 - FIg p) ≤ 1 := by linarith [(FI_gdens_prime_nonneg hp).1]
    nlinarith [FIg_nonneg (p ^ 2), h1]
  have h4 : FIg (p ^ 2) ≤ 4 / (p : ℝ) ^ 2 := by
    have hp2 : (0:ℝ) < (p:ℝ)^2 := pow_pos (by exact_mod_cast hp.pos) 2
    rw [le_div_iff₀ hp2]
    exact (FI_gdens_prime_sq_le p hp).2
  calc FIg (p ^ 2) * (1 - FIg p) / (1 - FIg (p ^ 2))
      ≤ FIg (p ^ 2) / (1 - FIg (p ^ 2)) := by
        refine div_le_div_of_nonneg_right hnum (le_of_lt hp1)
    _ ≤ FIg (p ^ 2) / (1 / 2) := by
        refine div_le_div_of_nonneg_left (FIg_nonneg _) (by norm_num) hden
    _ = 2 * FIg (p ^ 2) := by ring
    _ ≤ 2 * (4 / (p : ℝ) ^ 2) := by linarith
    _ = 8 / (p : ℝ) ^ 2 := by ring

/-- The correction sum `∑_p (g(p) − g̃(p))` converges at rate `16/y`. -/
lemma FIgtil_corr_sum (y : ℕ) (hy : 1 ≤ y) :
    |(∑' n : ℕ, gcorrect FIg n)
        - ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (FIg p - gtilVal FIg p)|
      ≤ 2 * 8 / (y : ℝ) :=
  abs_gcorrect_sub_le FIg (by norm_num) (fun p hp => FIgtil_correction_nonneg hp)
    (fun p hp => FIgtil_correction_le hp) y hy

open scoped Classical in
/-- **(1.9) for `g̃`**, in the `ℕ`-indexed form. -/
theorem FIgtil_sum_19_nat :
    ∃ c C : ℝ, ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, FIgtil p)
          - Real.log (Real.log (y : ℝ)) - c|
        ≤ C * ((Real.log (y : ℝ))^(-(10:ℝ)) + 1 / (y : ℝ)) := by
  obtain ⟨c0, hc0⟩ := FI_gdens_prime_sum
  obtain ⟨C0, hC0, hB⟩ := hc0 10 (by norm_num)
  set Hc : ℝ := ∑' n : ℕ, gcorrect FIg n with hHc
  have herr0 : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, FIg p) - Real.log (Real.log (y:ℝ)) - c0|
        ≤ C0 * ((Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) := by
    intro y hy
    have h := hB (y:ℝ) (by exact_mod_cast hy)
    rw [Nat.floor_natCast] at h
    have hset : (Finset.Icc 2 y).filter Nat.Prime = (Finset.Icc 1 y).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨le_trans (by norm_num) h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3.two_le, h2⟩, h3⟩
    rw [hset] at h
    have hlogpos : (0:ℝ) < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have h10 : C0 / (Real.log (y:ℝ))^((10:ℝ))
        = C0 * (Real.log (y:ℝ))^(-(10:ℝ)) := by
      rw [Real.rpow_neg hlogpos.le]
      ring
    refine le_trans h ?_
    rw [h10]
    have h2 : (0:ℝ) ≤ 1 / (y:ℝ) := by positivity
    have h3 : (0:ℝ) ≤ (Real.log (y:ℝ))^(-(10:ℝ)) := Real.rpow_nonneg hlogpos.le _
    nlinarith [hC0.le, h3, h2]
  have herr1 : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (FIg p - gtilVal FIg p)) - Hc|
        ≤ 16 * ((Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) := by
    intro y hy
    have h := FIgtil_corr_sum y (by omega)
    have hy0 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
    have h2 : 2 * 8 / (y:ℝ) ≤ 16 * ((Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) := by
      have h3 : (0:ℝ) ≤ (Real.log (y:ℝ))^(-(10:ℝ)) := by positivity
      have h4 : (0:ℝ) ≤ 1 / (y:ℝ) := by positivity
      have h5 : 2 * 8 / (y:ℝ) = 16 * (1 / (y:ℝ)) := by ring
      rw [h5]
      nlinarith
    rw [abs_sub_comm] at h
    exact le_trans h h2
  have hmain := sum_gtilVal_19 (g := FIg) (c := c0) (Hc := Hc) (K := C0) (Kc := 16)
    (err := fun y => (Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) herr0
    (fun y hy => herr1 y hy)
  refine ⟨c0 - Hc, C0 + 16, fun y hy => ?_⟩
  have h := hmain y hy
  have hsum : (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, gtilVal FIg p)
      = ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, FIgtil p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    exact (FIgtil_prime hp.2).symm
  rw [hsum] at h
  have hC0' : (0:ℝ) ≤ C0 + 16 := by linarith
  calc |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, FIgtil p)
          - Real.log (Real.log (y : ℝ)) - (c0 - Hc)|
      ≤ (C0 + 16) * ((Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) := h
    _ = (C0 + 16) * ((Real.log (y:ℝ))^(-(10:ℝ)) + 1 / (y:ℝ)) := rfl

end

end Submission.ASP
