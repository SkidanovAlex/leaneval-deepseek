import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

/-!
# Vocabulary for the two-sided Graham (Barban–Vehov) estimate

This file sets up the two quantities that the proof of `grahamCrossTwoSided` uses:

* the truncated von Mangoldt sum `Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` (real cutoff `z`,
  defined in `bvDefs.lean`);
* the **correction term** `Bz z n = Σ_{d ∣ n, z < d} μ(d)·log(d/z)`,

together with the pointwise identity `Lz z n = Λ(n) + Bz z n` (`n ≥ 2`), which splits every
truncated von Mangoldt sum into the von Mangoldt function plus a Möbius correction supported on
the integers having a divisor larger than the cutoff.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **The correction term of the truncated von Mangoldt sum.**
`Bz z n = Σ_{d ∣ n, z < d} μ(d)·log(d/z)`; for `n ≥ 2` one has `Lz z n = Λ(n) + Bz z n`. -/
def Bz (z : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => z < (d : ℝ)),
    (ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / z)

/-- The truncated von Mangoldt sum vanishes identically at cutoff `1`. -/
lemma Lz_one (n : ℕ) : Lz 1 n = 0 := by
  unfold Lz
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.mem_filter] at hd
  have hle : (d : ℝ) ≤ 1 := hd.2
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd.1).2)
  have hdle : d ≤ 1 := by exact_mod_cast hle
  have hd1 : d = 1 := by omega
  subst hd1
  simp

/-- `Bz z n = 0` when `n ≤ z` with `z ≥ 0`: all divisors of `n` are `≤ n ≤ z`. -/
lemma Bz_eq_zero_of_le {z : ℝ} (hz : 0 ≤ z) {n : ℕ} (hn : (n : ℝ) ≤ z) : Bz z n = 0 := by
  unfold Bz
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.mem_filter] at hd
  have := Nat.divisor_le hd.1
  have : (d : ℝ) ≤ z := le_trans (by exact_mod_cast this) hn
  exact absurd hd.2 (not_lt.mpr this)

/-- `Σ_{d ∣ n} μ(d)·log(z/d) = Λ(n)` for `n ≥ 2` and `z > 0`. -/
lemma sum_moebius_log_div (z : ℝ) (hz : 0 < z) {n : ℕ} (hn : 2 ≤ n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ)))
      = ArithmeticFunction.vonMangoldt n := by
  have h1 : ∀ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))
        = (ArithmeticFunction.moebius d : ℝ) * Real.log z
          - (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by
      have : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      exact_mod_cast this.ne'
    rw [Real.log_div (ne_of_gt hz) hd0, mul_sub]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  have h2 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
    rw [show (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))
          = ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) by push_cast; rfl,
      Commons.NumberTheory.Moebius.sum_moebius_divisors n]
    simp [show n ≠ 1 by omega]
  have h3 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))
      = -ArithmeticFunction.vonMangoldt n := ArithmeticFunction.sum_moebius_mul_log_eq
  rw [← Finset.sum_mul, h2, zero_mul, h3]
  ring

/-- **Pointwise splitting of the truncated von Mangoldt sum**: for `n ≥ 2` and any real `z > 0`,
`Lz z n = Λ(n) + Bz z n`. -/
theorem Lz_eq_vonMangoldt_add_Bz {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 2 ≤ n) :
    Lz z n = ArithmeticFunction.vonMangoldt n + Bz z n := by
  have hfull := sum_moebius_log_div z hz hn
  have hsplit : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ)))
      = (∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
            (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ)))
        + (∑ d ∈ n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
            (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hLz : (∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z),
      (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))) = Lz z n := rfl
  have hneg : (∑ d ∈ n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z),
      (ArithmeticFunction.moebius d : ℝ) * Real.log (z / (d : ℝ))) = - Bz z n := by
    have hf : n.divisors.filter (fun d : ℕ => ¬ (d : ℝ) ≤ z)
        = n.divisors.filter (fun d : ℕ => z < (d : ℝ)) := by
      ext d; simp only [Finset.mem_filter, not_le]
    rw [hf, Bz, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : z < (d : ℝ) := (Finset.mem_filter.mp hd).2
    have hdpos : 0 < d := by
      have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      exact Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [Real.log_div (ne_of_gt hz) hd0, Real.log_div hd0 (ne_of_gt hz)]
    ring
  rw [hLz, hneg] at hsplit
  linarith [hfull, hsplit]

end

end Work.ZeroDensity.Jutila
