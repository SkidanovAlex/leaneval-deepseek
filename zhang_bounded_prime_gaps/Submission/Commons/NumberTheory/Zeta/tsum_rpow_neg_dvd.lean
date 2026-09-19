import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron

open scoped BigOperators

namespace Commons.NumberTheory.Zeta

/-- Reindexing a `p`-divisibility sum: for `p > 0` and any real exponent `s`,
`∑_{d : p ∣ d} d^{-s} = p^{-s} · ∑_m m^{-s}`.

The map `m ↦ p * m` is a bijection `ℕ ≃ {d // p ∣ d}`, and `(p * m)^{-s} =
p^{-s} · m^{-s}` by `Real.mul_rpow`; the equality holds in `ℝ` for every `s`,
including the non-summable cases `s ≤ 0` where both sides are `0`. -/
theorem tsum_rpow_neg_dvd {p : ℕ} (hp : 0 < p) (s : ℝ) :
    (∑' d : ℕ, if p ∣ d then (d : ℝ) ^ (-s) else 0)
      = (p : ℝ) ^ (-s) * ∑' m : ℕ, (m : ℝ) ^ (-s) := by
  -- the bijection `m ↦ p * m` between `ℕ` and the multiples of `p`
  let e : ℕ ≃ {d : ℕ // p ∣ d} :=
    { toFun := fun m => ⟨p * m, dvd_mul_right p m⟩
      invFun := fun d => d.1 / p
      left_inv := fun m => by
        show p * m / p = m
        rw [Nat.mul_div_right _ hp]
      right_inv := fun d => by
        ext
        show p * (d.1 / p) = d.1
        rw [Nat.mul_div_cancel' d.2] }
  have he : ∀ m : ℕ, (e m : ℕ) = p * m := fun m => rfl
  -- rewrite the divisibility indicator as a sum over the subtype of multiples
  have hset : (∑' d : ℕ, if p ∣ d then (d : ℝ) ^ (-s) else 0)
      = ∑' d : {d : ℕ // p ∣ d}, (d : ℝ) ^ (-s) := by
    rw [show (∑' d : {d : ℕ // p ∣ d}, (d : ℝ) ^ (-s))
          = ∑' d : {d : ℕ | p ∣ d}, (d : ℝ) ^ (-s) from rfl]
    rw [tsum_subtype (s := {d : ℕ | p ∣ d}) (f := fun d : ℕ => (d : ℝ) ^ (-s))]
    exact tsum_congr fun d => by simp [Set.indicator_apply]
  rw [hset]
  -- reindex along `m ↦ p * m`
  rw [← Equiv.tsum_eq e (fun d : {d : ℕ // p ∣ d} => (d : ℝ) ^ (-s))]
  simp only [he]
  -- `(p * m) ^ (-s) = p ^ (-s) * m ^ (-s)`
  rw [tsum_congr (fun m : ℕ => by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg m)])]
  -- factor out the constant
  rw [tsum_mul_left]

end Commons.NumberTheory.Zeta