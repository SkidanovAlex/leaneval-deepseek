/-
Copyright: public domain.

A Mertens-type bound for the sum of reciprocals of primes in a range `(P, Y]`.

The proof rests on the two *sharp* first-Mertens bounds already available in the
workspace library,

  `sum_log_prime_div_prime_le_log`   : `Σ_{p ≤ x} (log p)/p ≤ log x`        (`x ≥ 2`),
  `log_prime_div_prime_ge_log_sub_two` : `log x - 2 ≤ Σ_{p ≤ x} (log p)/p` (`x ≥ 2`),

transported to the reciprocal-prime sum by Abel's identity
(`primeRecips_eq_logDiv_div_log_add_integral`).  Both bounds carry the *same*
coefficient `1` in front of `log (log x)`, so their difference — which is the sum
over the range — inherits coefficient `1` with a bounded additive constant.
-/
import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log
import Submission.Commons.NumberTheory.Mertens.log_prime_div_prime_ge_log_sub_two

namespace Work.FIArea6

open scoped BigOperators
open Finset Real
open MeasureTheory

noncomputable section

/-- The first Mertens function `logDiv x = Σ_{p ≤ x} (log p)/p` is at most `log x`
for `x ≥ 2` (sharp form of the first Mertens theorem). -/
lemma logDiv_le_log {x : ℝ} (hx : 2 ≤ x) :
    Commons.NumberTheory.Mertens.logDiv x ≤ Real.log x := by
  simpa only [Commons.NumberTheory.Mertens.logDiv] using
    Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log x hx

/-- The first Mertens function `logDiv x = Σ_{p ≤ x} (log p)/p` is at least
`log x - 2` for `x ≥ 2`. -/
lemma log_sub_two_le_logDiv {x : ℝ} (hx : 2 ≤ x) :
    Real.log x - 2 ≤ Commons.NumberTheory.Mertens.logDiv x := by
  simpa only [Commons.NumberTheory.Mertens.logDiv] using
    Commons.NumberTheory.Mertens.log_prime_div_prime_ge_log_sub_two x hx

/-- Upper bound for the prime reciprocal sum, with coefficient `1`:
`Σ_{p ≤ x} 1/p ≤ log log x + (1 - log log 2)` for `x ≥ 2`. -/
lemma primeRecips_upper {x : ℝ} (hx : 2 ≤ x) :
    Commons.NumberTheory.Mertens.primeRecips x ≤
      Real.log (Real.log x) + (1 - Real.log (Real.log 2)) := by
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have h2 : (1 : ℝ) < 2 := by norm_num
  rw [Commons.NumberTheory.Mertens.primeRecips_eq_logDiv_div_log_add_integral hx]
  have hterm : Commons.NumberTheory.Mertens.logDiv x / Real.log x ≤ 1 := by
    rw [div_le_one hlogx]
    exact logDiv_le_log hx
  have hIntF : IntervalIntegrable
      (fun t : ℝ => Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)) volume 2 x :=
    Commons.NumberTheory.Mertens.intervalIntegrable_logDiv_div_id_log_sq hx
  have hIntG : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume 2 x :=
    (Commons.NumberTheory.Mertens.contOn_inv_log (x := x)).intervalIntegrable_of_Icc hx
  have hint : (∫ t in 2..x, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2))
      ≤ ∫ t in 2..x, t⁻¹ / Real.log t := by
    refine intervalIntegral.integral_mono_on hx hIntF hIntG ?_
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have ht1 : 1 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hden : 0 ≤ t * (Real.log t) ^ 2 := by positivity
    have h1 : Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)
        ≤ Real.log t / (t * (Real.log t) ^ 2) :=
      div_le_div_of_nonneg_right (logDiv_le_log ht2) hden
    have h2' : Real.log t / (t * (Real.log t) ^ 2) = t⁻¹ / Real.log t := by
      field_simp
    linarith [h1, h2'.le, h2'.ge]
  have hval : (∫ t in 2..x, t⁻¹ / Real.log t) =
      Real.log (Real.log x) - Real.log (Real.log 2) := integral_inv_div_log h2 hx1
  linarith [hterm, hint, hval]

/-- Lower bound for the prime reciprocal sum, with coefficient `1`:
`log log x + (1 - log log 2) - 2/log 2 ≤ Σ_{p ≤ x} 1/p` for `x ≥ 2`. -/
lemma primeRecips_lower {x : ℝ} (hx : 2 ≤ x) :
    Real.log (Real.log x) + (1 - Real.log (Real.log 2)) - 2 / Real.log 2
      ≤ Commons.NumberTheory.Mertens.primeRecips x := by
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have h2 : (1 : ℝ) < 2 := by norm_num
  rw [Commons.NumberTheory.Mertens.primeRecips_eq_logDiv_div_log_add_integral hx]
  have hterm : (Real.log x - 2) / Real.log x ≤
      Commons.NumberTheory.Mertens.logDiv x / Real.log x :=
    div_le_div_of_nonneg_right (log_sub_two_le_logDiv hx) hlogx.le
  have hIntF : IntervalIntegrable
      (fun t : ℝ => Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)) volume 2 x :=
    Commons.NumberTheory.Mertens.intervalIntegrable_logDiv_div_id_log_sq hx
  have hIntLog : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume 2 x :=
    (Commons.NumberTheory.Mertens.contOn_inv_log (x := x)).intervalIntegrable_of_Icc hx
  have hIntLogSq : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 x :=
    (Commons.NumberTheory.Mertens.contOn_inv_log_sq (x := x)).intervalIntegrable_of_Icc hx
  have hIntG : IntervalIntegrable
      (fun t : ℝ => t⁻¹ / Real.log t - 2 * (t⁻¹ / Real.log t ^ 2)) volume 2 x :=
    hIntLog.sub (hIntLogSq.const_mul 2)
  have hint : (∫ t in 2..x, (t⁻¹ / Real.log t - 2 * (t⁻¹ / Real.log t ^ 2)))
      ≤ ∫ t in 2..x, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2) := by
    refine intervalIntegral.integral_mono_on hx hIntG hIntF ?_
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have ht1 : 1 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hld := log_sub_two_le_logDiv ht2
    have hden : 0 ≤ t * (Real.log t) ^ 2 := by positivity
    have h1 : (Real.log t - 2) / (t * (Real.log t) ^ 2)
        ≤ Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2) :=
      div_le_div_of_nonneg_right hld hden
    have h2' : (Real.log t - 2) / (t * (Real.log t) ^ 2)
        = t⁻¹ / Real.log t - 2 * (t⁻¹ / Real.log t ^ 2) := by
      field_simp
    linarith [h1, h2'.ge]
  have hval : (∫ t in 2..x, (t⁻¹ / Real.log t - 2 * (t⁻¹ / Real.log t ^ 2)))
      = (Real.log (Real.log x) - Real.log (Real.log 2)) - 2 * (1 / Real.log 2 - 1 / Real.log x) := by
    rw [intervalIntegral.integral_sub hIntLog (hIntLogSq.const_mul 2),
      intervalIntegral.integral_const_mul, integral_inv_div_log h2 hx1,
      integral_inv_div_log_sq h2 hx1]
    ring
  have hkey : (Real.log (Real.log x) - Real.log (Real.log 2) - 2 * (1 / Real.log 2 - 1 / Real.log x))
      + (Real.log x - 2) / Real.log x
      = Real.log (Real.log x) + (1 - Real.log (Real.log 2)) - 2 / Real.log 2 := by
    field_simp
    ring
  linarith [hterm, hint, hval, hkey]

/-- **Friedlander–Iwaniec, Mertens-type reciprocal prime range bound.**
For `2 ≤ P ≤ Y` and any finite set `s` of primes `p` with `P < p ≤ Y`,
`Σ_{p ∈ s} 1/p ≤ 4 (log(log Y / log P) + 1)`. -/
theorem prime_recip_sum_le (P Y : ℕ) (hP : 2 ≤ P) (hPY : P ≤ Y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hs2 : ∀ p ∈ s, P < p) (hs3 : ∀ p ∈ s, p ≤ Y) :
    (∑ p ∈ s, (1 : ℝ) / (p : ℝ)) ≤ 4 * (Real.log (Real.log Y / Real.log P) + 1) := by
  have hPpos : (0:ℝ) < (P:ℝ) := by positivity
  have hlogPpos : 0 < Real.log (P:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlogYpos : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hrecY : Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
      = ∑ p ∈ Nat.primesLE Y, (1:ℝ)/(p:ℝ) := by
    simp only [Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast]
  have hrecP : Commons.NumberTheory.Mertens.primeRecips (P:ℝ)
      = ∑ p ∈ Nat.primesLE P, (1:ℝ)/(p:ℝ) := by
    simp only [Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast]
  have hsub : s ⊆ Nat.primesLE Y \ Nat.primesLE P := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
    refine ⟨⟨hs3 p hp, hs p hp⟩, ?_⟩
    intro hle
    have := hs2 p hp
    omega
  have hsum_le : (∑ p ∈ s, (1:ℝ)/(p:ℝ))
      ≤ ∑ p ∈ Nat.primesLE Y \ Nat.primesLE P, (1:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hsubsetLE : Nat.primesLE P ⊆ Nat.primesLE Y := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (by exact_mod_cast hPY), hp.2⟩
  have hsdiff := Finset.sum_sdiff hsubsetLE (f := fun p : ℕ => (1:ℝ)/(p:ℝ))
  have hsd' : ∑ p ∈ Nat.primesLE Y \ Nat.primesLE P, (1:ℝ)/(p:ℝ)
      = Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
        - Commons.NumberTheory.Mertens.primeRecips (P:ℝ) := by
    rw [hrecY, hrecP]
    linarith [hsdiff]
  have hY2 : (2:ℝ) ≤ (Y:ℝ) := by exact_mod_cast le_trans hP hPY
  have hP2 : (2:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
  have hub := primeRecips_upper hY2
  have hlb := primeRecips_lower hP2
  have hdivlog : Real.log (Real.log (Y:ℝ) / Real.log (P:ℝ))
      = Real.log (Real.log (Y:ℝ)) - Real.log (Real.log (P:ℝ)) :=
    Real.log_div (ne_of_gt hlogYpos) (ne_of_gt hlogPpos)
  have hbound : ∑ p ∈ Nat.primesLE Y \ Nat.primesLE P, (1:ℝ)/(p:ℝ)
      ≤ Real.log (Real.log (Y:ℝ) / Real.log (P:ℝ)) + 2 / Real.log 2 := by
    rw [hsd', hdivlog]
    linarith [hub, hlb]
  have hLnonneg : 0 ≤ Real.log (Real.log (Y:ℝ) / Real.log (P:ℝ)) := by
    apply Real.log_nonneg
    rw [one_le_div hlogPpos]
    exact Real.log_le_log hPpos (by exact_mod_cast hPY)
  calc (∑ p ∈ s, (1:ℝ)/(p:ℝ)) ≤ ∑ p ∈ Nat.primesLE Y \ Nat.primesLE P, (1:ℝ)/(p:ℝ) := hsum_le
    _ ≤ Real.log (Real.log (Y:ℝ) / Real.log (P:ℝ)) + 2 / Real.log 2 := hbound
    _ ≤ 4 * (Real.log (Real.log (Y:ℝ) / Real.log (P:ℝ)) + 1) := by
        have hlog2 : (1:ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
        have h2log2 : 2 / Real.log 2 ≤ 4 := by
          rw [div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
          linarith
        linarith

end

end Work.FIArea6
