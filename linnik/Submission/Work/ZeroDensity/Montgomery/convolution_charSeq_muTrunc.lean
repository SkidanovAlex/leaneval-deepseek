import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerronAux

namespace Work.ZeroDensity.Montgomery

/-- Pointwise, the Dirichlet convolution of the coefficient sequence of `L(s,χ)` with the
truncated Möbius–character sequence is the sequence `n ↦ mCoef X n · χ(n)`. -/
theorem convolution_charSeq_muTrunc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ)
    (n : ℕ) :
    LSeries.convolution (charSeq χ) (muTrunc χ X) n = mCoef X n * χ (n : ZMod q) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.convolution_map_zero, mCoef_zero, zero_mul]
  · simp only [LSeries.convolution_def]
    -- `χ` is multiplicative, so on the antidiagonal `p.1 * p.2 = n` the two character
    -- factors combine into the single factor `χ n`.
    have hchi : ∀ p ∈ n.divisorsAntidiagonal,
        χ (p.1 : ZMod q) * χ (p.2 : ZMod q) = χ (n : ZMod q) := by
      intro p hp
      rw [← map_mul, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
    have hterm : ∀ p ∈ n.divisorsAntidiagonal, charSeq χ p.1 * muTrunc χ X p.2
        = χ (n : ZMod q) *
            (if (p.2 : ℝ) ≤ X then (ArithmeticFunction.moebius p.2 : ℂ) else 0) := by
      intro p hp
      simp only [charSeq, muTrunc]
      split_ifs with h
      · calc χ (p.1 : ZMod q) * ((ArithmeticFunction.moebius p.2 : ℂ) * χ (p.2 : ZMod q))
            = (χ (p.1 : ZMod q) * χ (p.2 : ZMod q)) *
                (ArithmeticFunction.moebius p.2 : ℂ) := by ring
          _ = χ (n : ZMod q) * (ArithmeticFunction.moebius p.2 : ℂ) := by rw [hchi p hp]
      · ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      mul_comm (mCoef X n) (χ (n : ZMod q))]
    congr 1
    -- Reindex the antidiagonal sum by its second component `n / i`, then identify the
    -- resulting filtered divisor sum with `mCoef X n`.
    rw [mCoef, Finset.sum_filter,
      Nat.sum_divisorsAntidiagonal'
        (f := fun a b => if (b : ℝ) ≤ X then (ArithmeticFunction.moebius b : ℂ) else 0)]

end Work.ZeroDensity.Montgomery
