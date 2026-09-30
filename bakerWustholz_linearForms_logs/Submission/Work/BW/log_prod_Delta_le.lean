import Mathlib
import Submission.Work.BW.norm_Delta_le
import Submission.Work.BW.prod_Delta_le
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW §12: the `Π`-factor estimate, logarithmic form

`Delta z k = (z+1)⋯(z+k)/k!` is BW's `Δ(z;k)`. The §12 product estimate is

  `∏_i |Δ(x_i; t_i)| ≤ e^{T'} (1 + (∑_i |x_i|)/T')^{T'}`,  `T' = ∑_i t_i`,

which gives the logarithmic form stated below. Each factor is bounded by
`(e (1 + |x_i|/t_i))^{t_i}` (from `k! ≥ k^k e^{-k}`), and then weighted AM–GM finishes.
-/

namespace Work.BW

/-- Weighted AM–GM consequence used in the §12 `Π`-factor estimate: for nonnegative `x` and
natural weights `t` with `T = ∑ i, t i > 0`,
`∏_i (1 + x_i / t_i)^{t_i} ≤ (1 + (∑_i x_i)/T)^T`.
Zero weights are harmless: with the Lean convention `x/0 = 0` the corresponding factor is
`1^0 = 1` and contributes nothing to either side. -/
lemma prod_one_add_div_pow_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (t : ι → ℕ)
    (hx : ∀ i, 0 ≤ x i) (hT : 0 < ∑ i, t i) :
    ∏ i, (1 + x i / (t i : ℝ)) ^ (t i) ≤
      (1 + (∑ i, x i) / ((∑ i, t i : ℕ) : ℝ)) ^ (∑ i, t i) := by
  have hKpos : (0 : ℝ) < ((∑ i, t i : ℕ) : ℝ) := by exact_mod_cast hT
  have hfac : ∀ i, 0 ≤ 1 + x i / (t i : ℝ) := by
    intro i
    have h1 : 0 ≤ x i / (t i : ℝ) := div_nonneg (hx i) (Nat.cast_nonneg _)
    linarith
  have ham := geom_mean_nat_le_arith_mean Finset.univ t (fun i => 1 + x i / (t i : ℝ))
    (fun i _ => hfac i) hT
  have hnum_nn : 0 ≤ ∑ i, (t i : ℝ) * (1 + x i / (t i : ℝ)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hfac i)
  have hnum : (∑ i, (t i : ℝ) * (1 + x i / (t i : ℝ))) ≤ ((∑ i, t i : ℕ) : ℝ) + ∑ i, x i := by
    calc (∑ i, (t i : ℝ) * (1 + x i / (t i : ℝ)))
        ≤ ∑ i, ((t i : ℝ) + x i) :=
          Finset.sum_le_sum (fun i _ => mul_one_add_div_le (t i) (x i) (hx i))
      _ = ((∑ i, t i : ℕ) : ℝ) + ∑ i, x i := by
          rw [Finset.sum_add_distrib]; push_cast; rfl
  calc ∏ i, (1 + x i / (t i : ℝ)) ^ (t i)
      ≤ ((∑ i, (t i : ℝ) * (1 + x i / (t i : ℝ))) / ((∑ i, t i : ℕ) : ℝ)) ^ (∑ i, t i) := ham
    _ ≤ ((((∑ i, t i : ℕ) : ℝ) + ∑ i, x i) / ((∑ i, t i : ℕ) : ℝ)) ^ (∑ i, t i) := by
        apply pow_le_pow_left₀
        · exact div_nonneg hnum_nn hKpos.le
        · exact div_le_div_of_nonneg_right hnum hKpos.le
    _ = (1 + (∑ i, x i) / ((∑ i, t i : ℕ) : ℝ)) ^ (∑ i, t i) := by
        rw [add_div, div_self hKpos.ne']

/-- Distributing the constant `e = Real.exp 1` out of a power-product: for `y : ι → ℝ` and
`t : ι → ℕ`, `∏_i (e · y_i)^{t_i} = e^{∑_i t_i} · ∏_i y_i^{t_i}`. Used to pull the per-factor
exponential bound `|Δ(z;k)| ≤ (e(1+|z|/k))^k` out of a product. -/
lemma prod_exp_one_mul_pow {ι : Type*} [Fintype ι] (y : ι → ℝ) (t : ι → ℕ) :
    ∏ i, (Real.exp 1 * y i) ^ (t i) =
      Real.exp (∑ i, (t i : ℝ)) * ∏ i, y i ^ (t i) := by
  have h1 : ∏ i, Real.exp 1 ^ (t i) = Real.exp (∑ i, (t i : ℝ)) := by
    calc ∏ i, Real.exp 1 ^ (t i)
        = ∏ i, Real.exp ((t i : ℕ) : ℝ) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [← Real.exp_nat_mul]
          simp
      _ = Real.exp (∑ i, (t i : ℝ)) := by simp only [← Real.exp_sum]
  simp only [mul_pow, Finset.prod_mul_distrib, h1]

/-- The right-hand side of the §12 `Π`-factor estimate is nonnegative: for `T, S ≥ 0`,
`0 ≤ T * (1 + log (1 + S/T))`. For `T = 0` this is `0 = 0`; for `T > 0` we have `S/T ≥ 0`, hence
`log (1 + S/T) ≥ 0`. -/
lemma mul_one_add_log_one_add_div_nonneg (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S) :
    0 ≤ T * (1 + Real.log (1 + S / T)) := by
  rcases eq_or_lt_of_le hT with h | h
  · subst h; simp
  · apply mul_nonneg h.le
    have h1 : (1 : ℝ) ≤ 1 + S / T := by
      have : 0 ≤ S / T := div_nonneg hS h.le
      linarith
    have := Real.log_nonneg h1
    linarith

/-- BW §12: the `Π`-factor estimate. For complex `x_i` and naturals `t_i` with `T' = ∑ t_i`, `|∏_i Δ(x_i; t_i)| ≤ e^{T'}(1 + (∑|x_i|)/T')^{T'}`; logarithmic form as below. Per factor use `|Δ(x;t)| ≤ (e(1+|x|/t))^t` (`k! ≥ k^k e^{-k+1}`) and weighted AM-GM. -/
theorem log_prod_Delta_le {ι : Type*} [Fintype ι] (x : ι → ℂ) (t : ι → ℕ) :
    Real.log ‖∏ i, Delta (x i) (t i)‖ ≤
      (∑ i, (t i : ℝ)) * (1 + Real.log (1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ)))) := by
  have hTcast : ((∑ i, t i : ℕ) : ℝ) = ∑ i, (t i : ℝ) := by push_cast; rfl
  have hSnn : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  by_cases hT0 : ∑ i, t i = 0
  · have hall : ∀ i, t i = 0 := by
      intro i
      have hle : t i ≤ ∑ j, t j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hprod1 : ∏ i, Delta (x i) (t i) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [hall i]
      simp [Delta, deltaPoly]
    have hsum0 : (∑ i, (t i : ℝ)) = 0 := by rw [← hTcast, hT0]; norm_num
    simp [hprod1, hsum0]
  · have hTnat : 0 < ∑ i, t i := Nat.pos_of_ne_zero hT0
    have hTposR : 0 < ∑ i, (t i : ℝ) := by rw [← hTcast]; exact_mod_cast hTnat
    have hbase_pos : 0 < 1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ)) := by
      have : 0 ≤ (∑ i, ‖x i‖) / (∑ i, (t i : ℝ)) := div_nonneg hSnn hTposR.le
      linarith
    have hprod_le : ‖∏ i, Delta (x i) (t i)‖ ≤
        Real.exp (∑ i, (t i : ℝ)) *
          (1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ))) ^ (∑ i, t i) := by
      rw [norm_prod]
      calc ∏ i, ‖Delta (x i) (t i)‖
          ≤ ∏ i, (Real.exp 1 * (1 + ‖x i‖ / (t i : ℝ))) ^ (t i) :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
              (fun i _ => norm_Delta_le (x i) (t i))
        _ = Real.exp (∑ i, (t i : ℝ)) * ∏ i, (1 + ‖x i‖ / (t i : ℝ)) ^ (t i) :=
            prod_exp_one_mul_pow (fun i => 1 + ‖x i‖ / (t i : ℝ)) t
        _ ≤ Real.exp (∑ i, (t i : ℝ)) *
              (1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ))) ^ (∑ i, t i) := by
            have h := prod_one_add_div_pow_le (fun i => ‖x i‖) t
              (fun i => norm_nonneg _) hTnat
            rw [hTcast] at h
            exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    rcases eq_or_lt_of_le (norm_nonneg (∏ i, Delta (x i) (t i))) with hN0 | hNpos
    · have hN : ‖∏ i, Delta (x i) (t i)‖ = 0 := hN0.symm
      rw [hN, Real.log_zero]
      exact mul_one_add_log_one_add_div_nonneg _ _ hTposR.le hSnn
    · have hlog := Real.log_le_log hNpos hprod_le
      rw [Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ hbase_pos.ne'), Real.log_exp,
        Real.log_pow] at hlog
      rw [hTcast] at hlog
      calc Real.log ‖∏ i, Delta (x i) (t i)‖
          ≤ (∑ i, (t i : ℝ)) +
              (∑ i, (t i : ℝ)) * Real.log (1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ))) := hlog
        _ = (∑ i, (t i : ℝ)) *
              (1 + Real.log (1 + (∑ i, ‖x i‖) / (∑ i, (t i : ℝ)))) := by ring

end Work.BW
