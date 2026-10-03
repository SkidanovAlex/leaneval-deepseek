import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **(16.17), Euler product, `HasProd` form.**  The finite partial products of the local factors
`Σ_ν λ(p^ν)p^{-νs}` converge (as a net over finite sets of primes) to the Hecke `L`-series
`L(s,ψ) = Σ_n λ(n)n^{-s}` in the half-plane `re s > 1`.  This is the `HasProd`-phrased companion of
`heckeLSeries_eulerProduct`, obtained from Mathlib's `EulerProduct.eulerProduct_hasProd` applied to
`n ↦ λ(n)n^{-s}` (multiplicative on coprime arguments, `f 1 = 1`, `f 0 = 0`, and `‖f ·‖` summable
by the bound `‖λ(n)‖ ≤ 4τ(n)`). -/
theorem heckeLSeries_eulerProduct_hasProd (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi1 : chi 1 = 1) (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchi_bd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ (e * s)))
      (heckeLSeries chi k s) := by
  classical
  have hf1 : heckeLSeriesCoeff chi k s 1 = 1 := by
    simp only [heckeLSeriesCoeff_apply, heckeLam_one, hchi1, Nat.cast_one, Complex.one_cpow,
      div_one]
  have hf0 : heckeLSeriesCoeff chi k s 0 = 0 := by
    simp only [heckeLSeriesCoeff_apply, heckeLam_zero, Nat.cast_zero, zero_div]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      heckeLSeriesCoeff chi k s (m * n)
        = heckeLSeriesCoeff chi k s m * heckeLSeriesCoeff chi k s n := by
    intro m n hcop
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hcop
      subst hn1
      simp only [hf0, zero_mul]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hcop
      subst hm1
      simp only [hf0, mul_zero]
    simp only [heckeLSeriesCoeff_apply]
    rw [heckeLam_mul chi k hchi hmpos hnpos hcop, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ← div_mul_div_comm]
  have hbd : ∀ n : ℕ,
      ‖heckeLSeriesCoeff chi k s n‖ ≤ 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re)) := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp only [heckeLSeriesCoeff_apply, heckeLam_zero, Nat.cast_zero, zero_div, norm_zero,
        Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
      rw [Real.zero_rpow (show -s.re ≠ 0 by linarith)]
      norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [heckeLSeriesCoeff_apply, norm_div, Complex.norm_natCast_cpow_of_pos hnpos]
      have h1 : ‖heckeLam chi k n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
        heckeLam_bound chi k hchi_bd (Nat.one_le_iff_ne_zero.mpr hn)
      have hpos : (0 : ℝ) < (n : ℝ) ^ s.re :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
      calc ‖heckeLam chi k n‖ / (n : ℝ) ^ s.re
          ≤ (4 * ((n.divisors.card : ℕ) : ℝ)) / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right h1 hpos.le
        _ = 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re)) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n)]; ring
  have hsum : Summable (fun n : ℕ => ‖heckeLSeriesCoeff chi k s n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbd ?_
    exact (summable_card_divisors_mul_rpow_neg hs).mul_left 4
  have key := EulerProduct.eulerProduct_hasProd (R := ℂ) (f := heckeLSeriesCoeff chi k s)
    hf1 hmul hsum hf0
  have hloc : ∀ p : Nat.Primes,
      (∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ (e * s)))
        = ∑' e : ℕ, heckeLSeriesCoeff chi k s ((p : ℕ) ^ e) := by
    intro p
    refine tsum_congr fun e => ?_
    simp only [heckeLSeriesCoeff_apply]
    have hpow : ((((p : ℕ) ^ e : ℕ) : ℂ)) ^ s = ((p : ℕ) : ℂ) ^ (e * s) := by
      rw [Nat.cast_pow]
      exact (Complex.natCast_cpow_natCast_mul (p : ℕ) e s).symm
    rw [hpow]
  have hR : (∑' n : ℕ, heckeLSeriesCoeff chi k s n) = heckeLSeries chi k s := by
    rw [heckeLSeries, LSeries_def₀ (heckeLam_zero chi k) s]
    exact tsum_congr fun n => by simp only [heckeLSeriesCoeff_apply]
  have key2 : HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ (e * s)))
      (∑' n : ℕ, heckeLSeriesCoeff chi k s n) := key.congr_fun hloc
  rwa [hR] at key2

end

end Work.FIArea5.S16Hecke
