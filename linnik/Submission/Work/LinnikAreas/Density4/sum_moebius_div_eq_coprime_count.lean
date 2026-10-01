import Mathlib
import Submission.Work.LinnikAreas.Density4.coprime_indicator_moebius
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex

namespace Work.LinnikAreas.Density4

/-- Textbook Möbius count: `#{k ≤ X : (k,r)=1} = Σ_{b|r} μ(b)·⌊X/b⌋`.
Proof route: for `b ∈ r.divisors` (so `b ≥ 1`), `⌊X/b⌋ = #(multiples of b in Icc 1 X)` via
`sum_Icc_filter_dvd_reindex` with `φ := fun _ => 1` and `Nat.card_Icc`; rewrite the count as a
`Finset.card_filter`, cast to ℝ, expand `(μ b : ℝ) * (card : ℝ)` as a sum of `(μ b : ℝ)` over the
filtered Finset, then `Finset.sum_comm` the double sum and finish with the existing
`coprime_indicator_moebius` (with `F = 1`). -/
theorem sum_moebius_div_eq_coprime_count (r X : ℕ) (hr : 1 ≤ r) :
    (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) * ((X / b : ℕ) : ℝ))
      = ∑ k ∈ Finset.Icc 1 X, (if Nat.Coprime k r then (1 : ℝ) else 0) := by
  classical
  -- `∑_{m ∈ s} 1 = #s` in `ℝ`.
  have ones_eq : ∀ s : Finset ℕ, (∑ m ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
    intro s
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- `⌊X/b⌋` is the number of multiples of `b` in `Icc 1 X`.
  have hcard : ∀ b ∈ r.divisors,
      ((X / b : ℕ) : ℝ) = (((Finset.Icc 1 X).filter (fun m => b ∣ m)).card : ℝ) := by
    intro b hb
    have hb1 : 1 ≤ b := by
      have hdvd : b ∣ r := (Nat.mem_divisors.mp hb).1
      exact Nat.pos_of_dvd_of_pos hdvd (by omega)
    have h := sum_Icc_filter_dvd_reindex X b hb1 (fun _ => (1 : ℝ))
    rw [ones_eq, ones_eq, Nat.card_Icc] at h
    simpa using h.symm
  have h1 : (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) * ((X / b : ℕ) : ℝ))
      = ∑ b ∈ r.divisors, ∑ m ∈ (Finset.Icc 1 X).filter (fun m => b ∣ m),
          (ArithmeticFunction.moebius b : ℝ) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [hcard b hb, ← ones_eq ((Finset.Icc 1 X).filter (fun m => b ∣ m))]
    rw [Finset.mul_sum]
    simp
  have h2 : (∑ b ∈ r.divisors, ∑ m ∈ (Finset.Icc 1 X).filter (fun m => b ∣ m),
            (ArithmeticFunction.moebius b : ℝ))
      = ∑ b ∈ r.divisors, ∑ m ∈ Finset.Icc 1 X,
          (if b ∣ m then (ArithmeticFunction.moebius b : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_filter]
  have h3 : (∑ b ∈ r.divisors, ∑ m ∈ Finset.Icc 1 X,
            (if b ∣ m then (ArithmeticFunction.moebius b : ℝ) else 0))
      = ∑ m ∈ Finset.Icc 1 X, ∑ b ∈ r.divisors,
          (if b ∣ m then (ArithmeticFunction.moebius b : ℝ) else 0) :=
    Finset.sum_comm
  have h4 : (∑ m ∈ Finset.Icc 1 X, ∑ b ∈ r.divisors,
            (if b ∣ m then (ArithmeticFunction.moebius b : ℝ) else 0))
      = ∑ m ∈ Finset.Icc 1 X, (if Nat.Coprime m r then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simpa using (coprime_indicator_moebius m r hr (1 : ℝ)).symm
  rw [h1, h2, h3, h4]

end Work.LinnikAreas.Density4
