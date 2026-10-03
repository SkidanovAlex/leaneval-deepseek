import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_one
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeEigenvalue_mul
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The coefficient sequence `n ↦ λ(n)/n^s` of the Hecke `L`-series (16.17), to which the
Euler-product theorem is applied. -/
def heckeLSeriesCoeff (chi : GaussianInt → ℂ) (k : ℤ) (s : ℂ) : ℕ → ℂ :=
  fun n => heckeLam chi k n / (n : ℂ) ^ s

@[simp] lemma heckeLSeriesCoeff_apply (chi : GaussianInt → ℂ) (k : ℤ) (s : ℂ) (n : ℕ) :
    heckeLSeriesCoeff chi k s n = heckeLam chi k n / (n : ℂ) ^ s := rfl

/-- **(16.17), Euler product.** The Hecke `L`-series `L(s,ψ) = Σ_n λ(n)n^{-s}` of the
eigenvalue sequence `λ(n) = Σ_{z primary, |z|² = n} ψ(z)` factors, in the half-plane `re s > 1`, as
the product over primes of its local factors `Σ_ν λ(p^ν)p^{-νs}`.  This is the product form (16.17)
of the `L`-function; downstream it is combined with the local recursion for `λ(p^ν)` to see that the
`p`-factor is a polynomial of degree `2` in `p^{-s}` and that `∏_{p>P}(1-λ(p)p^{-s})·L(s,ψ)`
converges absolutely in `re s > 1/2`, which is what (16.31) consumes.

Ingredients available in this workspace: `heckeEigenvalue_mul` (multiplicativity of `λ` on coprime
arguments, from multiplicativity of `χ`), `heckeLam_one` for `λ(1) = χ(1)`, `λ(0) = 0`, and
`‖λ(n)‖ ≤ 4·τ(n)` (see `S16Hecke/heckeLam_bound`; `τ(p^ν) = ν+1`, so `Σ_n ‖λ(n)‖n^{-σ}` converges
for `σ > 1` — a crude bound `τ(n) ≤ 2√n` suffices for `σ > 3/2`, and the full range follows from
`Σ τ(n)n^{-σ} = ζ(σ)²`).  Mathlib's `EulerProduct.eulerProduct_tprod` then gives the product over
`Nat.Primes` for a multiplicative `f` with `f 0 = 0`, `f 1 = 1` and `Summable (‖f ·‖)`, applied to
`f n = λ(n)/n^s`. -/
theorem heckeLSeries_eulerProduct (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi1 : chi 1 = 1) (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchi_bd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, ∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ (e * s)))
      = heckeLSeries chi k s := by
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
  have key := EulerProduct.eulerProduct_tprod (R := ℂ) (f := heckeLSeriesCoeff chi k s)
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
  rw [tprod_congr hloc, key, hR]

end

end Work.FIArea5.S16Hecke
