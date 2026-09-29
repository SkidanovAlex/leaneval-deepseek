import Mathlib
import Submission.Work.CPull.defs

/-!
# Area CPull — `evp` is additive and multiplicative

`evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (see `Submission.Work.CPull.defs`).

For the sum this is just `tsum_add`.  For the product, note that `Summable` in Mathlib is
*unconditional* summation: for a complete normed space it is equivalent to absolute convergence
(`Summable.norm`, `Summable.of_norm`), so the hypotheses give absolute convergence of both
series.  Hence the Cauchy product formula
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` applies, and the `n`-th coefficient of
`f * g` is precisely the sum over `Finset.antidiagonal n` of `(coeff k f) * (coeff l g)`.
-/

namespace Work.CPull

open PowerSeries

theorem evp_add_mul (f g : PowerSeries ℚ) (z : ℂ)
    (hf : Summable fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n)
    (hg : Summable fun n : ℕ => ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n) :
    (evp (f + g) z = evp f z + evp g z) ∧ (evp (f * g) z = evp f z * evp g z) := by
  constructor
  · -- additivity
    have h : (fun n : ℕ => ((PowerSeries.coeff n (f + g) : ℚ) : ℂ) * z ^ n)
        = fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n
            + ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n := by
      funext n
      rw [map_add]
      push_cast
      ring
    simp only [evp, h]
    rw [Summable.tsum_add hf hg]
  · -- multiplicativity
    have hAn : Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖ := hf.norm
    have hBn : Summable fun n : ℕ => ‖((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n‖ := hg.norm
    have hkey := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hAn hBn
    have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n (f * g) : ℚ) : ℂ) * z ^ n
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            (((PowerSeries.coeff kl.1 f : ℚ) : ℂ) * z ^ kl.1)
              * (((PowerSeries.coeff kl.2 g : ℚ) : ℂ) * z ^ kl.2) := by
      intro n
      rw [PowerSeries.coeff_mul]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [← hp', pow_add]
      ring
    simp only [evp]
    rw [tsum_congr hcoeff]
    exact hkey.symm

end Work.CPull
