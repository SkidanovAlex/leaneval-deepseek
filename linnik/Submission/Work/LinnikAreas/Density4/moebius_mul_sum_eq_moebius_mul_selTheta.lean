import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

/-- Möbius multiplicativity, in "coprime-or-zero" form: if `l` and `m` are coprime,
`μ (l * m) = μ l * μ m`; if they are not coprime then `l * m` is not squarefree
(a common prime `p` divides both, so `p ^ 2 ∣ l * m`) and `μ (l * m) = 0`. -/
private lemma moebius_mul_cast (l m : ℕ) :
    (ArithmeticFunction.moebius (l * m) : ℝ) =
      (if Nat.Coprime l m then
        (ArithmeticFunction.moebius l : ℝ) * (ArithmeticFunction.moebius m : ℝ) else 0) := by
  by_cases h : Nat.Coprime l m
  · rw [if_pos h,
      ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius h]
    push_cast
    ring
  · rw [if_neg h]
    have hs : ¬ Squarefree (l * m) := by
      intro hsf
      obtain ⟨p, hp, hpl, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (mul_dvd_mul hpl hpm)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

theorem moebius_mul_sum_eq_moebius_mul_selTheta (z l : ℕ) (hl : 1 ≤ l) :
    (∑ m ∈ Finset.Icc 1 (z / l),
        (ArithmeticFunction.moebius (l * m) : ℝ) *
          Real.log ((z : ℝ) / ((l * m : ℕ) : ℝ)) / (m : ℝ))
      = (ArithmeticFunction.moebius l : ℝ) *
          Work.LinnikAreas.Density4.selTheta ((z : ℝ) / (l : ℝ)) l := by
  classical
  -- `⌊z / l⌋₊ = z / l` for natural `z`, `l`, so both sides sum over the same range.
  have hfloor : ⌊(z : ℝ) / (l : ℝ)⌋₊ = z / l := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  -- `z / (l * m) = (z / l) / m` as real numbers, so the logarithms agree.
  have hlog : ∀ m : ℕ,
      Real.log ((z : ℝ) / ((l * m : ℕ) : ℝ)) = Real.log (((z : ℝ) / (l : ℝ)) / (m : ℝ)) := by
    intro m
    congr 1
    rw [Nat.cast_mul, div_div]
  simp only [Work.LinnikAreas.Density4.selTheta, hfloor]
  rw [Finset.mul_sum]
  -- replace `μ (l * m)` by `μ l * μ m` on the coprime terms and delete the other terms
  have hL : (∑ m ∈ Finset.Icc 1 (z / l),
        (ArithmeticFunction.moebius (l * m) : ℝ) *
          Real.log ((z : ℝ) / ((l * m : ℕ) : ℝ)) / (m : ℝ))
      = ∑ m ∈ (Finset.Icc 1 (z / l)).filter (fun m => Nat.Coprime l m),
          (ArithmeticFunction.moebius l : ℝ) * ((ArithmeticFunction.moebius m : ℝ)
            * Real.log ((z : ℝ) / ((l * m : ℕ) : ℝ)) / (m : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    rw [moebius_mul_cast]
    by_cases h : Nat.Coprime l m
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hL]
  -- both sums are now over the same range, with the same coprimality filter and the same
  -- logarithms; only the order of the coprimality condition differs.
  refine Finset.sum_congr ?_ (fun m _ => ?_)
  · apply Finset.filter_congr
    intro m _
    exact Nat.coprime_comm
  · rw [hlog]

end Work.LinnikAreas.Density4
