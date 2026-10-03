import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Commons.Analysis.AbelKernel.abel_kernel_bounds
import Submission.Commons.Analysis.Series.summable_log_rpow_inv_div

namespace Commons.NumberTheory.FriedlanderIwaniec

open Filter Topology

/-- The Abel kernel `(a^{−σ} − (a+1)^{−σ})/σ` tends to `log ((a+1)/a)` as `σ → 0⁺`,
for `a ≥ 1`.  Both `σ ↦ a^{−σ}` and `σ ↦ (a+1)^{−σ}` are differentiable at `0`
(writing `a^{−σ} = (a⁻¹)^σ`), so the difference quotient has the stated limit. -/
private lemma tendsto_abel_kernel (a : ℝ) (ha : 1 ≤ a) :
    Filter.Tendsto (fun σ : ℝ => (a ^ (-σ) - (a + 1) ^ (-σ)) / σ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log ((a + 1) / a))) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha10 : 0 < a + 1 := by linarith
  have h1' : HasDerivAt (fun σ : ℝ => a ^ (-σ)) (- Real.log a) 0 := by
    have hbase : (fun σ : ℝ => a ^ (-σ)) = fun σ : ℝ => (a⁻¹) ^ σ := by
      funext σ; rw [Real.rpow_neg ha0.le, Real.inv_rpow ha0.le]
    rw [hbase]
    have hst := (Real.hasStrictDerivAt_const_rpow (inv_pos.mpr ha0) 0).hasDerivAt
    have he : (a⁻¹) ^ (0:ℝ) * Real.log (a⁻¹) = - Real.log a := by
      rw [Real.rpow_zero, one_mul, Real.log_inv]
    rwa [he] at hst
  have h2'' : HasDerivAt (fun σ : ℝ => (a + 1) ^ (-σ)) (- Real.log (a + 1)) 0 := by
    have hbase : (fun σ : ℝ => (a + 1) ^ (-σ)) = fun σ : ℝ => ((a + 1)⁻¹) ^ σ := by
      funext σ; rw [Real.rpow_neg ha10.le, Real.inv_rpow ha10.le]
    rw [hbase]
    have hst := (Real.hasStrictDerivAt_const_rpow (inv_pos.mpr ha10) 0).hasDerivAt
    have he : ((a + 1)⁻¹) ^ (0:ℝ) * Real.log ((a + 1)⁻¹) = - Real.log (a + 1) := by
      rw [Real.rpow_zero, one_mul, Real.log_inv]
    rwa [he] at hst
  have hsub := h1'.sub h2''
  have hderiv : -Real.log a - (-Real.log (a + 1)) = Real.log ((a + 1) / a) := by
    rw [Real.log_div (by linarith) (ne_of_gt ha0)]; ring
  rw [hderiv] at hsub
  have hsl := hsub.tendsto_slope_zero
  have hfac : (fun t : ℝ => t⁻¹ • (((fun σ : ℝ => a ^ (-σ)) - fun σ : ℝ => (a + 1) ^ (-σ)) (0 + t)
        - ((fun σ : ℝ => a ^ (-σ)) - fun σ : ℝ => (a + 1) ^ (-σ)) 0))
      = fun t : ℝ => t⁻¹ * (a ^ (-t) - (a + 1) ^ (-t)) := by
    funext t
    simp [Pi.sub_apply, Real.rpow_zero]
  rw [hfac] at hsl
  have hlim : Filter.Tendsto (fun t : ℝ => t⁻¹ * (a ^ (-t) - (a + 1) ^ (-t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log ((a + 1) / a))) := by
    refine hsl.mono_left ?_
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  simpa [div_eq_mul_inv, mul_comm] using hlim

/-- Dominated-convergence (Tannery) step for the Abel kernel
`g_σ(d) = (d^{-σ} - (d+1)^{-σ})/σ`, which increases to `log((d+1)/d)` as `σ → 0⁺`. If
`c 0 = 0` and `|c y| ≤ C (log y)^{-6}` for all `y ≥ 2`, then
`∑_d c d · g_σ(d) → ∑_d c d · log((d+1)/d)` as `σ → 0⁺`. -/
theorem tendsto_tsum_mul_abelskernel (c : ℕ → ℝ) (h0 : c 0 = 0)
    (h24 : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → |c y| ≤ C * (Real.log y) ^ (-6 : ℝ)) :
    Filter.Tendsto
      (fun σ : ℝ => ∑' d : ℕ, c d * (((d : ℝ) ^ (-σ) - ((d : ℝ) + 1) ^ (-σ)) / σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑' d : ℕ, c d * Real.log (((d : ℝ) + 1) / (d : ℝ)))) := by
  obtain ⟨C, hCpos, hCbound⟩ := h24
  -- Dominating summable majorant `|c y| · log((y+1)/y)`, bounded by `C (log y)^{-6}/y`.
  have hG : Summable (fun n : ℕ => (Real.log (n:ℝ))^(-6:ℝ)/(n:ℝ)) :=
    Commons.Analysis.Series.summable_log_rpow_inv_div 6 (by norm_num)
  have hGshift : Summable (fun n : ℕ => C * ((Real.log ((n+2:ℕ):ℝ))^(-6:ℝ)/((n+2:ℕ):ℝ))) := by
    have h1 : Summable (fun n : ℕ => (Real.log ((n+2:ℕ):ℝ))^(-6:ℝ)/((n+2:ℕ):ℝ)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (Real.log (n:ℝ))^(-6:ℝ)/(n:ℝ)) 2).mpr hG
    exact h1.mul_left C
  have key : ∀ d : ℕ, 2 ≤ d →
      |c d| * Real.log (((d:ℝ)+1)/(d:ℝ)) ≤ C * ((Real.log (d:ℝ))^(-6:ℝ)/(d:ℝ)) := by
    intro d hd2
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hlogd_pos : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
    have hlogd_nn : 0 ≤ (Real.log (d:ℝ))^(-6:ℝ) := le_of_lt (Real.rpow_pos_of_pos hlogd_pos _)
    have hcy := hCbound d hd2
    have hlr_nn : 0 ≤ Real.log (((d:ℝ)+1)/(d:ℝ)) := by
      apply Real.log_nonneg
      rw [one_le_div hd0]; linarith
    have hlr_le : Real.log (((d:ℝ)+1)/(d:ℝ)) ≤ 1/(d:ℝ) := by
      have hpos : (0:ℝ) < ((d:ℝ)+1)/(d:ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos hpos
      have heq : ((d:ℝ)+1)/(d:ℝ) - 1 = 1/(d:ℝ) := by field_simp; ring
      linarith [h, heq]
    calc |c d| * Real.log (((d:ℝ)+1)/(d:ℝ))
        ≤ (C * (Real.log (d:ℝ))^(-6:ℝ)) * Real.log (((d:ℝ)+1)/(d:ℝ)) :=
          mul_le_mul_of_nonneg_right hcy hlr_nn
      _ ≤ (C * (Real.log (d:ℝ))^(-6:ℝ)) * (1/(d:ℝ)) :=
          mul_le_mul_of_nonneg_left hlr_le (mul_nonneg (le_of_lt hCpos) hlogd_nn)
      _ = C * ((Real.log (d:ℝ))^(-6:ℝ)/(d:ℝ)) := by
          rw [one_div, div_eq_mul_inv, mul_assoc]
  have hbound2 : Summable (fun n : ℕ => |c (n+2)| * Real.log ((((n+2:ℕ):ℝ)+1)/((n+2:ℕ):ℝ))) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hGshift
    · intro n
      have hpos : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
      have hlog : 0 ≤ Real.log ((((n+2:ℕ):ℝ)+1)/((n+2:ℕ):ℝ)) := by
        apply Real.log_nonneg
        rw [one_le_div hpos]; linarith
      exact mul_nonneg (abs_nonneg _) hlog
    · intro n
      exact key (n+2) (by omega)
  have hsum : Summable (fun k : ℕ => |c k| * Real.log (((k:ℝ)+1)/(k:ℝ))) :=
    (summable_nat_add_iff (f := fun k : ℕ => |c k| * Real.log (((k:ℝ)+1)/(k:ℝ))) 2).mp hbound2
  -- Pointwise convergence of every summand.
  have hab : ∀ k : ℕ, Filter.Tendsto
      (fun σ : ℝ => c k * (((k:ℝ)^(-σ) - ((k:ℝ)+1)^(-σ))/σ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c k * Real.log (((k:ℝ)+1)/(k:ℝ)))) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [h0, zero_mul]
      exact tendsto_const_nhds
    · have ha : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      exact (tendsto_abel_kernel (k:ℝ) ha).const_mul (c k)
  -- Uniform domination by the summable majorant, for `σ > 0`.
  have hb : ∀ᶠ σ in (nhdsWithin 0 (Set.Ioi 0)), ∀ k : ℕ,
      ‖c k * (((k:ℝ)^(-σ) - ((k:ℝ)+1)^(-σ))/σ)‖ ≤ |c k| * Real.log (((k:ℝ)+1)/(k:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [h0]
    · have ha : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      obtain ⟨h1, h2⟩ := Commons.Analysis.AbelKernel.abel_kernel_bounds (k:ℝ) ha σ hσ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  exact tendsto_tsum_of_dominated_convergence hsum hab hb

end Commons.NumberTheory.FriedlanderIwaniec