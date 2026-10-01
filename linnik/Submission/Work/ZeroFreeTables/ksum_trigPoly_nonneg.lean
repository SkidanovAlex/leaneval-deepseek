/-
# ZeroFreeTables — ksum_trigPoly_nonneg.lean

The positivity transfer that turns the non-negativity of a Chebyshev polynomial
`P(x) = ∑_{k ≤ d} c k · T k(x)` on `[-1,1]` into the non-negativity of the
Heath-Brown `P₃`-type combination

`∑_{k ≤ d} c k · K(β + i k γ, χ^k)`

of the von Mangoldt sums `K(s,χ) = ∑'_n Λ(n) ℜ(χ(n)/n^s) f(log n / L)`.

The mechanism is the classical one: for `n` coprime to `q` the point
`w = χ(n) n^{-iγ}` lies on the unit circle and `ℜ(w^k) = T k(ℜ w)`, so the
`k`-sum at a fixed `n` collapses to `P(ℜ w) ≥ 0`; for `n` not coprime to `q`
every `χ^k(n)` vanishes.  The `tsum`s are finite because the test function `f`
is supported below `x₀`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.TrigPolyPos
import Submission.Work.ZeroFreeTables.tsum_finset_sum_nonneg
import Submission.Work.ZeroFreeTables.ksum_trigPoly_pointwise

namespace Work.ZeroFreeTables

theorem ksum_trigPoly_nonneg {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ : ℝ} (hL : 0 < L) (hx₀ : 0 ≤ x₀) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {c : ℕ → ℝ} {d : ℕ}
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x)
    (χ : DirichletCharacter ℂ q) :
    0 ≤ ∑ k ∈ Finset.range (d + 1), c k *
      Work.ZeroFreeTables.Ksum q f L ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I) (χ ^ k) := by
  classical
  -- beyond `N` the weight `f(log n / L)` vanishes, so every `tsum` is finite
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    refine ⟨Nat.ceil (Real.exp (x₀ * L)) + 1, fun n hn => ?_⟩
    have h1 : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have : (Nat.ceil (Real.exp (x₀ * L)) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hn)
      exact le_trans (Nat.le_ceil _) this
    have h2 : x₀ * L ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hL]
    linarith
  -- push the finite `k`-sum inside every `tsum`
  have key : 0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) *
      (((χ ^ k) (n : ZMod q)) / (n : ℂ) ^ ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I)).re
      * f (Real.log n / L)) := by
    refine tsum_finset_sum_nonneg (N := N) (g := fun k n =>
      (ArithmeticFunction.vonMangoldt n : ℝ) *
      (((χ ^ k) (n : ZMod q)) / (n : ℂ) ^ ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I)).re
      * f (Real.log n / L)) ?_ ?_
    · -- the weight vanishes past `N`
      intro k n hn
      rw [hsupp _ (hN n hn)]
      ring
    · -- the integrand is pointwise non-negative
      intro n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
        rw [Finset.sum_eq_zero (fun k _ => by rw [hΛ0]; simp)]
      · exact ksum_trigPoly_pointwise hf hP χ h
  simpa only [Ksum] using key

end Work.ZeroFreeTables
