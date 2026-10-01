import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.moebius_mul_sum_eq_moebius_mul_selTheta

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

/-- Real-parameter form of the existing integer-parameter identity
`Work.LinnikAreas.Density4.moebius_mul_sum_eq_moebius_mul_selTheta`: for `1 ≤ l`, summing
`μ(l*k)·log((Q/l)/k)/k` over `k ≤ ⌊Q⌋₊/l` gives `μ(l)·Θ(Q/l, l)`, where
`Θ(y,k) = Σ_{m ≤ y, (m,k)=1} μ(m)·log(y/m)/m` is `Work.LinnikAreas.Density4.selTheta`
(use `Nat.floor_div_natCast` for `⌊Q/l⌋₊ = ⌊Q⌋₊/l`, and `div_div` to identify the log arguments). -/
theorem moebius_mul_selTheta_real (Q : ℝ) (l : ℕ) (hl : 1 ≤ l) :
    (∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / l),
        (ArithmeticFunction.moebius (l * k) : ℝ) * Real.log ((Q / (l : ℝ)) / (k : ℝ)) / (k : ℝ))
      = (ArithmeticFunction.moebius l : ℝ) * Work.LinnikAreas.Density4.selTheta (Q / (l : ℝ)) l := by
  classical
  -- `⌊Q / l⌋₊ = ⌊Q⌋₊ / l`, so both sides sum over the same range.
  have hfloor : ⌊Q / (l : ℝ)⌋₊ = ⌊Q⌋₊ / l := by
    rw [Nat.floor_div_natCast]
  simp only [Work.LinnikAreas.Density4.selTheta, hfloor]
  rw [Finset.mul_sum]
  -- replace `μ (l * k)` by `μ l * μ k` on the coprime terms and delete the other terms
  have hL : (∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / l),
        (ArithmeticFunction.moebius (l * k) : ℝ) *
          Real.log ((Q / (l : ℝ)) / (k : ℝ)) / (k : ℝ))
      = ∑ k ∈ (Finset.Icc 1 (⌊Q⌋₊ / l)).filter (fun k => Nat.Coprime l k),
          (ArithmeticFunction.moebius l : ℝ) * ((ArithmeticFunction.moebius k : ℝ)
            * Real.log ((Q / (l : ℝ)) / (k : ℝ)) / (k : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    rw [moebius_mul_cast]
    by_cases h : Nat.Coprime l k
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hL]
  -- both sums now have the same range, coprimality filter and logarithms; only the
  -- order of the coprimality condition differs.
  refine Finset.sum_congr ?_ (fun m _ => ?_)
  · apply Finset.filter_congr
    intro m _
    exact Nat.coprime_comm
  · rfl

end Work.LinnikAreas.Density4
