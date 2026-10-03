import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

theorem coeff_mul_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (a : A) (f : SkewLaurentSeries A) (n : ℤ) :
    (coeff a * f).1 n = a * f.1 n := by
  rw [mul_apply_of_bounds (coeff a) f 0 (lo f)
    (fun m hm => by
      have : m ≠ 0 := by omega
      simp [coeff_apply, this])
    (fun m hm => lt_lo hm) n]
  rw [Finset.sum_eq_single 0]
  · simp [coeff_apply]
  · intro b hb hb0
    simp [coeff_apply, hb0]
  · intro h0
    have hn : n < lo f := by
      by_contra hc
      exact h0 (Finset.mem_Icc.mpr ⟨le_refl 0, by omega⟩)
    simp [coeff_apply, lt_lo hn]

end Work.ORHughesFree.SkewLaurentSeries
