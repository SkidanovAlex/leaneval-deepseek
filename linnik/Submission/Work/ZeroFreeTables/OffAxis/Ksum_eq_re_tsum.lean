import Mathlib
import Submission.Work.ZeroFreeTables.CertData

open scoped BigOperators Classical

namespace Work.ZeroFreeTables.OffAxis

/-- The real part of `(a : ℂ) * z * (r : ℂ)` with `a r : ℝ` is `a * z.re * r`. -/
private lemma re_mul_mul_ofReal (a r : ℝ) (z : ℂ) :
    (((a : ℂ) * z * (r : ℂ))).re = a * z.re * r := by
  simp [Complex.mul_re, mul_assoc]

/-- `Ksum` is the real part of the complex von Mangoldt sum, exactly:
`∑ Λ(n) Re(χ(n)/n^s) f(log n / L) = Re ∑ Λ(n) χ(n)/n^s (f(log n / L) : ℂ)`.

Both sums are finite: the test function `f` vanishes on `[x₀, ∞)`, so every term
with `log n / L ≥ x₀` (i.e. all `n ≥ exp(x₀ L)`) is zero. -/
theorem Ksum_eq_re_tsum {L x₀ : ℝ} (hL : 0 < L) (q : ℕ) [NeZero q] {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    Work.ZeroFreeTables.Ksum q f L s χ
      = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((χ (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
          ((f (Real.log n / L) : ℝ) : ℂ)).re := by
  -- a cut-off `N` beyond which `log n / L ≥ x₀`
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (Real.exp (x₀ * L)))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNe : Real.exp (x₀ * L) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hlog : ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log n / L := by
    intro n hn
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
    have hlogN : x₀ * L ≤ Real.log N := by
      have h := Real.log_le_log (Real.exp_pos (x₀ * L)) hNe
      rwa [Real.log_exp] at h
    have hlogn : Real.log N ≤ Real.log n := Real.log_le_log hNpos hnR
    rw [le_div_iff₀ hL]
    exact le_trans hlogN hlogn
  have hvan : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := fun n hn => hsupp _ (hlog n hn)
  -- both series reduce to the same finite sum over `Finset.range N`
  have hreal : Work.ZeroFreeTables.Ksum q f L s χ
      = ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (((χ (n : ZMod q) : ℂ)) / (n : ℂ) ^ s).re * f (Real.log n / L) := by
    simp only [Work.ZeroFreeTables.Ksum]
    refine tsum_eq_sum (s := Finset.range N) ?_
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hvan n hn]
    ring
  have hcplx : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((χ (n : ZMod q) : ℂ)) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ))
      = ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((χ (n : ZMod q) : ℂ)) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) := by
    refine tsum_eq_sum (s := Finset.range N) ?_
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hvan n hn]
    simp
  rw [hreal, hcplx, Complex.re_sum]
  -- termwise identification of the real parts
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [mul_div_assoc]
  have hcast : (ArithmeticFunction.vonMangoldt n : ℂ)
      = (((ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ) := by simp
  rw [hcast]
  exact (re_mul_mul_ofReal _ _ _).symm

end Work.ZeroFreeTables.OffAxis
