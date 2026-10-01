import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

/-!
# Integrability of `A(x) x^{-(s+1)}` on `(1, ∞)`

`Asum χ x = Σ_{n ≤ ⌊x⌋} λ(n)` is the summatory function of the coefficients of
`ζ(s)L(s,χ)`.  The hypothesis `‖Efun χ x‖ ≤ K √x` (i.e. `A(x) = x·L(1,χ) + O(√x)`) is
exactly the input available for a real quadratic character, and it gives

  `A(x) = x·L(1,χ) + O(√x)  ⟹  ‖A(x)‖ ≤ K√x + x‖L(1,χ)‖ ≤ (K + ‖L(1,χ)‖)·x  (x ≥ 1)`.

Since `‖x^{-(s+1)}‖ = x^{-(Re s + 1)}` for `x > 0`, the integrand is dominated by
`(K + ‖L(1,χ)‖)·x^{-Re s}`, which is integrable on `(1,∞)` as soon as `Re s > 1`.
-/

namespace Work.LinnikAreas

open MeasureTheory DirichletCharacter Complex
open scoped BigOperators
noncomputable section

/-- `Asum χ` is a measurable step function: it is the composition of the (monotone, hence
Borel measurable) floor map `x ↦ ⌊x⌋₊` with the prefix sum `N ↦ Σ_{n ≤ N} λ(n)`. -/
lemma measurable_Asum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Measurable fun t : ℝ => Asum χ t := by
  have h : (fun t : ℝ => Asum χ t)
      = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, lam χ n) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
  rw [h]
  exact (measurable_of_countable _).comp Nat.floor_mono.measurable

theorem AsumCPowIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x) {s : ℂ}
    (hs : 1 < s.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Asum χ t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  -- `A(x) = E(x) + x·L(1,χ)`, so `‖A(x)‖ ≤ (K + ‖L(1,χ)‖)·x` for `x ≥ 1`.
  have hKnn : 0 ≤ K := by
    have h := hE 1 le_rfl
    rw [Real.sqrt_one, mul_one] at h
    linarith [norm_nonneg (Efun χ 1)]
  have hkey : ∀ t : ℝ, 1 ≤ t →
      ‖Asum χ t * (t : ℂ) ^ (-(s + 1))‖ ≤ (K + ‖LFunction χ 1‖) * t ^ (-s.re) := by
    intro t ht
    have htpos : 0 < t := by linarith
    have ht0 : 0 ≤ t := by linarith
    have hsqrt : Real.sqrt t ≤ t := by
      nlinarith [Real.sq_sqrt ht0, Real.sqrt_nonneg t]
    have hnrm : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self ht0]
    have hAsum : ‖Asum χ t‖ ≤ K * t + t * ‖LFunction χ 1‖ := by
      have hsplit : Asum χ t = Efun χ t + (t : ℂ) * LFunction χ 1 := by
        rw [Efun]; ring
      calc ‖Asum χ t‖
          = ‖Efun χ t + (t : ℂ) * LFunction χ 1‖ := by rw [hsplit]
        _ ≤ ‖Efun χ t‖ + ‖(t : ℂ) * LFunction χ 1‖ := norm_add_le _ _
        _ = ‖Efun χ t‖ + t * ‖LFunction χ 1‖ := by rw [norm_mul, hnrm]
        _ ≤ K * Real.sqrt t + t * ‖LFunction χ 1‖ := by linarith [hE t ht]
        _ ≤ K * t + t * ‖LFunction χ 1‖ := by
              linarith [mul_le_mul_of_nonneg_left hsqrt hKnn]
    have hcpow : ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      simp [Complex.neg_re, Complex.add_re]
    calc ‖Asum χ t * (t : ℂ) ^ (-(s + 1))‖
        = ‖Asum χ t‖ * t ^ (-(s.re + 1)) := by rw [norm_mul, hcpow]
      _ ≤ (K * t + t * ‖LFunction χ 1‖) * t ^ (-(s.re + 1)) :=
            mul_le_mul_of_nonneg_right hAsum (Real.rpow_nonneg ht0 _)
      _ = (K + ‖LFunction χ 1‖) * (t * t ^ (-(s.re + 1))) := by ring
      _ = (K + ‖LFunction χ 1‖) * t ^ (-s.re) := by
            have he : t * t ^ (-(s.re + 1)) = t ^ (-s.re) := by
              have h := Real.rpow_add htpos (1 : ℝ) (-(s.re + 1))
              rw [Real.rpow_one] at h
              rw [← h]
              congr 1
              ring
            rw [he]
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (by intro h; rw [h] at ht; exact absurd ht (by norm_num)))).continuousWithinAt
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (K + ‖LFunction χ 1‖) * t ^ (-s.re)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) (by norm_num : (0:ℝ) < 1)).const_mul _
  exact Integrable.mono' hint
    ((measurable_Asum χ).aestronglyMeasurable.mul (hcont.aestronglyMeasurable measurableSet_Ioi))
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      exact hkey t (le_of_lt ht))

end
end Work.LinnikAreas
