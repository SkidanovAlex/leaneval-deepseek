import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

theorem t_mul_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) (n : ℤ) :
    (t * f).1 n = (Multiplicative.ofAdd (1 : ℤ)) • f.1 (n - 1) := by
  rw [mul_apply_of_bounds (f := t) (g := f) (Nf := 0) (Ng := lo f)
    (fun k hk => by simp [t_apply, show k ≠ 1 by omega])
    (fun k hk => lt_lo hk) n]
  have hφ : ∀ k : ℤ, (t : SkewLaurentSeries A).1 k * ((Multiplicative.ofAdd k) • f.1 (n - k))
      = if k = 1 then (Multiplicative.ofAdd (1 : ℤ)) • f.1 (n - 1) else 0 := by
    intro k
    by_cases hk : k = 1
    · subst hk; simp
    · simp [t_apply, hk]
  simp only [hφ, Finset.sum_ite_eq']
  by_cases h : (1 : ℤ) ∈ Finset.Icc 0 (n - lo f)
  · rw [if_pos h]
  · rw [if_neg h]
    have hlt : n - 1 < lo f := by
      have h1 : ¬ ((1 : ℤ) ≤ n - lo f) := fun hle => h (by simp [Finset.mem_Icc, hle])
      have h1' : n - lo f < 1 := not_le.mp h1
      omega
    rw [lt_lo (f := f) (n := n - 1) hlt, smul_zero]

end Work.ORHughesFree.SkewLaurentSeries
