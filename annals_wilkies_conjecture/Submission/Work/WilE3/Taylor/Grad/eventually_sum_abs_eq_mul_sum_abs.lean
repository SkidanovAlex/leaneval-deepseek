import Mathlib

namespace Work.WilE3.Taylor.Grad

theorem eventually_sum_abs_eq_mul_sum_abs {k : ℕ} {v w : Fin k → ℝ → ℝ} {n : ℕ}
    (hvw : ∀ j, v j =ᶠ[nhds (0:ℝ)] fun t => t ^ n * w j t) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∑ j, |v j t| = t ^ n * ∑ j, |w j t| := by
  -- combine the finitely many germ identities into one eventual identity
  have h : ∀ᶠ t in nhds (0:ℝ), ∀ j, v j t = t ^ n * w j t :=
    Filter.eventually_all.mpr hvw
  have h' : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ j, v j t = t ^ n * w j t :=
    h.filter_mono nhdsWithin_le_nhds
  filter_upwards [h', self_mem_nhdsWithin] with t ht htpos
  have ht0 : (0:ℝ) ≤ t := le_of_lt htpos
  calc ∑ j, |v j t| = ∑ j, |t ^ n * w j t| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ht j]
    _ = ∑ j, t ^ n * |w j t| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 n)]
    _ = t ^ n * ∑ j, |w j t| := by rw [Finset.mul_sum]

end Work.WilE3.Taylor.Grad
