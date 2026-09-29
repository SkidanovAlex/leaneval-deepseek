import Mathlib
import Submission.Work.CPull.defs

/-!
# Area C17I — `evp` on polynomials

`Work.CPull.evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (see `Submission.Work.CPull.defs`).

For a polynomial `p : ℚ[X]`, viewed in `ℚ⟦X⟧` via `Polynomial.toPowerSeries`, all but finitely
many coefficients vanish (`Polynomial.coeff_coe` identifies the `n`-th coefficient of the power
series with `p.coeff n`).  Hence `tsum_eq_sum` rewrites the (infinite) defining sum of `evp` as a
finite sum over `p.support`, which is literally `Polynomial.eval₂` at `z` (`Polynomial.eval₂_eq_sum`).
-/

namespace Work.C17I

theorem evp_poly (p : Polynomial ℚ) (z : ℂ) :
    Work.CPull.evp (p : PowerSeries ℚ) z = p.eval₂ (algebraMap ℚ ℂ) z := by
  rw [Work.CPull.evp]
  rw [tsum_eq_sum (s := p.support) ?_]
  · rw [Polynomial.eval₂_eq_sum]
    rw [Polynomial.sum]
    exact Finset.sum_congr rfl (fun n _ => by simp)
  · intro n hn
    rw [Polynomial.coeff_coe]
    have h0 : p.coeff n = 0 := by
      by_contra h
      exact hn (Polynomial.mem_support_iff.mpr h)
    simp [h0]

end Work.C17I
