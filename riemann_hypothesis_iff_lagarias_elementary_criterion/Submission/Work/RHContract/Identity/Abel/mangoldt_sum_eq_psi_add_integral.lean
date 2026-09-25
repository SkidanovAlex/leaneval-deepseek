import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity.Abel

open MeasureTheory

/-- The function `F t = 1/(t log t)` has derivative `-k(t)` for `t ≥ 2`, where
`k(t) = (log t + 1)/(t² log² t)` is the kernel `Work.RHContract.kW`. -/
private lemma deriv_inv_mul_log_eq_neg_kW (t : ℝ) (ht : 2 ≤ t) :
    deriv (fun s : ℝ => (s * Real.log s)⁻¹) t = -Work.RHContract.kW t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hG := Real.hasDerivAt_mul_log (x := t) ht0
  have hd : deriv (fun s : ℝ => (s * Real.log s)⁻¹) t = -(Real.log t + 1)/(t*Real.log t)^2 :=
    (hG.inv (mul_ne_zero ht0 hlog)).deriv
  rw [hd, Work.RHContract.kW, mul_pow, neg_div]

theorem mangoldt_sum_eq_psi_add_integral (x : ℝ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
      = Chebyshev.psi x / (x * Real.log x)
        + ∫ t in Set.Ioc (2 : ℝ) x, Chebyshev.psi t * Work.RHContract.kW t := by
  have hderiv : ∀ t : ℝ, 2 ≤ t → deriv (fun s : ℝ => (s * Real.log s)⁻¹) t = -Work.RHContract.kW t :=
    deriv_inv_mul_log_eq_neg_kW
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc (2:ℝ) x) := by
    apply ContinuousOn.log continuousOn_id
    intro t ht
    exact (by linarith [ht.1] : (0:ℝ) < t).ne'
  have hFdiff : ∀ t ∈ Set.Icc (2:ℝ) x, DifferentiableAt ℝ (fun s : ℝ => (s * Real.log s)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact (Real.hasDerivAt_mul_log (x := t) ht0).inv (mul_ne_zero ht0 hlog) |>.differentiableAt
  have hkWcont : ContinuousOn (fun t : ℝ => -Work.RHContract.kW t) (Set.Icc (2:ℝ) x) := by
    unfold Work.RHContract.kW
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · apply ContinuousOn.add
      · exact hlogcont
      · exact continuousOn_const
    · apply ContinuousOn.mul
      · exact continuousOn_id.pow 2
      · exact hlogcont.pow 2
    · intro t ht
      exact mul_ne_zero (pow_ne_zero 2 (by linarith [ht.1] : t ≠ 0))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1]))))
  have hFint : IntegrableOn (deriv (fun s : ℝ => (s * Real.log s)⁻¹)) (Set.Icc (2:ℝ) x) := by
    refine IntegrableOn.congr_fun (f := fun t : ℝ => -Work.RHContract.kW t) ?_ (fun t ht => ?_) measurableSet_Icc
    · exact hkWcont.integrableOn_compact isCompact_Icc
    · exact (hderiv t ht.1).symm
  have hc0 : (fun n : ℕ => ArithmeticFunction.vonMangoldt n) 0 = 0 := by simp
  have hc1 : (fun n : ℕ => ArithmeticFunction.vonMangoldt n) 1 = 0 :=
    ArithmeticFunction.vonMangoldt_apply_one
  have H := sum_mul_eq_sub_integral_mul₁ (𝕜 := ℝ)
    (c := fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (f := fun s : ℝ => (s * Real.log s)⁻¹) hc0 hc1 x hFdiff hFint
  have hLHS : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)))
      = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (fun s : ℝ => (s * Real.log s)⁻¹) k * ArithmeticFunction.vonMangoldt k := by
    rw [show Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    rw [show (fun s : ℝ => (s * Real.log s)⁻¹) ((0:ℕ):ℝ) * ArithmeticFunction.vonMangoldt 0 = 0 by
          simp, zero_add]
    exact Finset.sum_congr rfl (fun k hk => by rw [div_eq_mul_inv, mul_comm])
  rw [hLHS, H]
  have hsum_psi : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) = Chebyshev.psi x :=
    (Chebyshev.psi_eq_sum_Icc x).symm
  have hfx : (fun s : ℝ => (s * Real.log s)⁻¹) x * Chebyshev.psi x
      = Chebyshev.psi x / (x * Real.log x) := by
    rw [div_eq_mul_inv, mul_comm]
  have hint : ∫ t in Set.Ioc (2:ℝ) x,
        deriv (fun s : ℝ => (s*Real.log s)⁻¹) t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k)
      = - ∫ t in Set.Ioc (2:ℝ) x, Chebyshev.psi t * Work.RHContract.kW t := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht2 : (2:ℝ) ≤ t := le_of_lt ht.1
    change deriv (fun s : ℝ => (s * Real.log s)⁻¹) t *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k)
      = -(Chebyshev.psi t * Work.RHContract.kW t)
    rw [← Chebyshev.psi_eq_sum_Icc, hderiv t ht2]
    ring
  rw [hsum_psi, hfx, hint]
  ring

end Work.RHContract.Identity.Abel
