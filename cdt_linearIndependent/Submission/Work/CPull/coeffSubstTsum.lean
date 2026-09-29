import Mathlib
import Submission.Work.CPull.evp_aux

namespace Work.CPull

/-- The `n`-th coefficient of `f.subst b` (over `ℚ`), read in `ℂ`, is the sum over `d` of
`coeff d f` times the `n`-th coefficient of `b ^ d`.  Since `constantCoeff b = 0` the sum has
finite support, so the `tsum` over `ℕ` is really a finite sum. -/
theorem coeffSubstTsum (f b : PowerSeries ℚ) (hb0 : PowerSeries.constantCoeff b = 0) (n : ℕ) :
    ((PowerSeries.coeff n (f.subst b) : ℚ) : ℂ)
      = ∑' d : ℕ, ((PowerSeries.coeff d f : ℚ) : ℂ) * ((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) := by
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  -- Mathlib's substitution formula, in `ℚ`.
  rw [PowerSeries.coeff_subst' hb f n]
  simp only [smul_eq_mul]
  have hfin : Function.HasFiniteSupport
      (fun d : ℕ => PowerSeries.coeff d f * PowerSeries.coeff n (b ^ d)) := by
    simpa only [smul_eq_mul] using PowerSeries.coeff_subst_finite' hb f n
  have hsupp : Function.support
      (fun d : ℕ => ((PowerSeries.coeff d f : ℚ) : ℂ) * ((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ))
      ⊆ ↑(Set.Finite.toFinset hfin) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset hfin, Function.mem_support]
    intro h0
    exact hd (by rw [← Rat.cast_mul, h0, Rat.cast_zero])
  -- the `finsum` over `ℚ` and the `tsum` over `ℂ` are both the finite sum over the support.
  rw [finsum_eq_sum _ hfin, tsum_eq_sum' (s := Set.Finite.toFinset hfin) hsupp]
  push_cast
  rfl

end Work.CPull
