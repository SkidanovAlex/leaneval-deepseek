import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open DirichletCharacter

/-- If the error term `E(x) = A(x) - x·L(1,χ)` is `O(√x)`, then the partial sums
`Σ_{k ≤ n} λ(k)` of `λ(n) = Σ_{d | n} χ(d)` are `O(n)`.

Indeed, for `n ≥ 1`, `⌊n⌋₊ = n` so `A(n) = Σ_{k ∈ Icc 1 n} λ(k)` and
`A(n) = E(n) + n·L(1,χ)`, hence `‖A(n)‖ ≤ K√n + n‖L(1,χ)‖ ≤ (K + ‖L(1,χ)‖)·n`. -/
theorem AsumPartialIsBigO {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Work.LinnikAreas.lam χ k)
      =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨K + ‖LFunction χ 1‖, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  -- `K ≥ 0`, since the hypothesis at `x = 1` reads `‖E(1)‖ ≤ K`.
  have hK : 0 ≤ K := by
    have h1 := hE 1 le_rfl
    rw [Real.sqrt_one, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr (by exact_mod_cast hn)
  have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `Asum χ n = Σ_{k ≤ n} λ(k)`.
  have hAsum : Asum χ (n : ℝ) = ∑ k ∈ Finset.Icc 1 n, lam χ k := by
    rw [Asum_apply, Nat.floor_natCast]
  -- `‖Asum χ n‖ ≤ K√n + n‖L(1,χ)‖`.
  have hb : ‖Asum χ (n : ℝ)‖ ≤ K * Real.sqrt (n : ℝ) + (n : ℝ) * ‖LFunction χ 1‖ := by
    have h := hE (n : ℝ) hcast
    have hsplit : Asum χ (n : ℝ) = Efun χ (n : ℝ) + (n : ℝ) * LFunction χ 1 := by
      rw [Efun_apply]; ring
    rw [hsplit]
    calc ‖Efun χ (n : ℝ) + (n : ℝ) * LFunction χ 1‖
        ≤ ‖Efun χ (n : ℝ)‖ + ‖(n : ℝ) * LFunction χ 1‖ := norm_add_le _ _
      _ ≤ K * Real.sqrt (n : ℝ) + (n : ℝ) * ‖LFunction χ 1‖ :=
          add_le_add h (by rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast])
  have hnorm : ‖(n : ℝ) ^ (1 : ℝ)‖ = (n : ℝ) := by
    rw [Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  rw [hnorm, ← hAsum]
  have step1 : K * Real.sqrt (n : ℝ) ≤ K * (n : ℝ) := mul_le_mul_of_nonneg_left hsqrt hK
  linarith [hb, step1]

end Work.LinnikAreas
