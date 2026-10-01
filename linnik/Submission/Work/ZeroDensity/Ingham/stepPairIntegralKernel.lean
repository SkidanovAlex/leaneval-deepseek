import Mathlib
import Submission.Work.ZeroDensity.Ingham.fourthMomentDefs
import Submission.Work.Analysis.Integral.norm_intervalIntegral_exp_I_mul_le
import Submission.Work.Analysis.Real.log_diff_ge_div
import Submission.Work.ZeroDensity.Ingham.abs_sub_le_max_mul_abs_log_sub
import Submission.Work.ZeroDensity.Ingham.norm_intervalIntegral_exp_I_mul_le_arbitrary
import Submission.Work.ZeroDensity.Ingham.stepPair_mul_conj_eq

namespace Work.ZeroDensity.Ingham

open MeasureTheory

/-- **Indicator/exponential integral bound.**  For `θ ≠ 0` the interval integral over `[0,T]`
of the indicator of `[γ,∞)` times `exp (I θ s)` has modulus at most `2/|θ|`: the indicator
restricts the integral to a subinterval, on which the primitive `exp (I θ s)/(I θ)` gives the
bound `2/|θ|`, and the passage from the indicator to the subinterval is an almost-everywhere
identification of sets. -/
lemma norm_intervalIntegral_indicator_exp_le (γ T θ : ℝ) (hθ : θ ≠ 0) :
    ‖∫ t in (0 : ℝ)..T, (Set.Ici γ).indicator (fun s => Complex.exp (Complex.I * ((θ * s : ℝ) : ℂ))) t‖
      ≤ 2 / |θ| := by
  have hpos : (0:ℝ) < 2 / |θ| := by
    have h0 : (0:ℝ) < |θ| := abs_pos.mpr hθ
    positivity
  have key : ∀ a b : ℝ,
      ‖∫ t in Set.Ioc a b, Complex.exp (Complex.I * ((θ * t : ℝ) : ℂ))‖ ≤ 2 / |θ| := by
    intro a b
    rcases le_or_gt a b with hab | hba
    · rw [← intervalIntegral.integral_of_le hab]
      exact norm_intervalIntegral_exp_I_mul_le_arbitrary a b θ hθ
    · have hempty : Set.Ioc a b = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨h1, h2⟩
        exact (not_le.mpr hba) (le_trans (le_of_lt h1) h2)
      rw [hempty, MeasureTheory.setIntegral_empty]
      simpa using le_of_lt hpos
  have hae : ∀ a b : ℝ, a ≤ b →
      (Set.Ioc a b ∩ Set.Ici γ : Set ℝ) =ᵐ[volume] Set.Ioc (max γ a) b := by
    intro a b hab
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    refine MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := max γ a))
    intro x hx
    rw [Set.mem_singleton_iff]
    rw [Set.mem_symmDiff] at hx
    rcases hx with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩
    · rw [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici] at hxs
      rw [Set.mem_Ioc, not_and, not_le] at hxt
      by_cases h : max γ a < x
      · exact absurd (hxt h) (not_lt.mpr hxs.1.2)
      · exact le_antisymm (not_lt.mp h) (max_le hxs.2 (le_of_lt hxs.1.1))
    · exfalso
      apply hxs
      rw [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
      rw [Set.mem_Ioc] at hxt
      exact ⟨⟨lt_of_le_of_lt (le_max_right γ a) hxt.1, hxt.2⟩,
        le_trans (le_max_left γ a) (le_of_lt hxt.1)⟩
  have key2 : ∀ a b : ℝ, a ≤ b →
      ‖∫ t in a..b, (Set.Ici γ).indicator (fun s => Complex.exp (Complex.I * ((θ * s : ℝ) : ℂ))) t‖
        ≤ 2 / |θ| := by
    intro a b hab
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.setIntegral_indicator measurableSet_Ici,
      MeasureTheory.setIntegral_congr_set (hae a b hab)]
    exact key (max γ a) b
  rcases le_or_gt (0:ℝ) T with hT | hT
  · exact key2 0 T hT
  · rw [intervalIntegral.integral_symm T 0, norm_neg]
    exact key2 T 0 (le_of_lt hT)

theorem stepPairIntegralKernel (T : ℝ) (hT : 0 ≤ T) (p q : ℕ × ℕ)
    (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2) (hq1 : 1 ≤ q.1) (hq2 : 1 ≤ q.2) :
    ‖∫ t in (0:ℝ)..T, stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)‖
      ≤ pairKernel T (pairProd p) (pairProd q) := by
  have hp1R : (1:ℝ) ≤ (p.1:ℝ) := by exact_mod_cast hp1
  have hp2R : (1:ℝ) ≤ (p.2:ℝ) := by exact_mod_cast hp2
  have hq1R : (1:ℝ) ≤ (q.1:ℝ) := by exact_mod_cast hq1
  have hq2R : (1:ℝ) ≤ (q.2:ℝ) := by exact_mod_cast hq2
  have hpt : ∀ t : ℝ, stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)
      = ((Real.sqrt (((p.1 : ℝ) * (p.2 : ℝ)) * ((q.1 : ℝ) * (q.2 : ℝ))) : ℂ))⁻¹ *
        (Set.Ici (max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
                       (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2)))).indicator
          (fun s => Complex.exp (Complex.I * ((s * (Real.log ((q.1 : ℝ) * (q.2 : ℝ)) - Real.log ((p.1 : ℝ) * (p.2 : ℝ))) : ℝ) : ℂ))) t :=
    fun t => stepPair_mul_conj_eq p q hp1 hp2 hq1 hq2 t
  rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul,
    norm_mul]
  set Cc : ℂ := ((Real.sqrt (((p.1 : ℝ) * (p.2 : ℝ)) * ((q.1 : ℝ) * (q.2 : ℝ))) : ℂ))⁻¹ with hCc
  set γ : ℝ := max (max (2 * Real.pi * ((p.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((p.2 : ℝ) - 1) ^ 2))
                 (max (2 * Real.pi * ((q.1 : ℝ) - 1) ^ 2) (2 * Real.pi * ((q.2 : ℝ) - 1) ^ 2)) with hγ
  set Dl : ℝ := Real.log ((q.1 : ℝ) * (q.2 : ℝ)) - Real.log ((p.1 : ℝ) * (p.2 : ℝ)) with hDl
  have hCnorm : ‖Cc‖ = (Real.sqrt (((p.1 : ℝ) * (p.2 : ℝ)) * ((q.1 : ℝ) * (q.2 : ℝ))))⁻¹ := by
    rw [hCc, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hcomm : (fun s : ℝ => Complex.exp (Complex.I * ((s * Dl : ℝ) : ℂ)))
      = (fun s : ℝ => Complex.exp (Complex.I * ((Dl * s : ℝ) : ℂ))) := by
    funext s
    congr 1
    push_cast
    ring
  rw [hcomm]
  rw [pairProd_apply, pairProd_apply]
  by_cases hKK : p.1 * p.2 = q.1 * q.2
  · -- diagonal case
    rw [pairKernel_apply, if_pos hKK]
    simp only [Nat.cast_mul]
    have hposP : (0:ℝ) < (p.1:ℝ) * (p.2:ℝ) := by nlinarith
    have hAB : ((p.1:ℝ) * (p.2:ℝ)) = ((q.1:ℝ) * (q.2:ℝ)) := by
      have h1 : ((p.1 * p.2 : ℕ) : ℝ) = ((q.1 * q.2 : ℕ) : ℝ) := by rw [hKK]
      push_cast at h1
      exact h1
    have hDl0 : Dl = 0 := by rw [hDl, hAB, sub_self]
    have hbody : (fun s : ℝ => Complex.exp (Complex.I * ((Dl * s : ℝ) : ℂ))) = fun _ : ℝ => (1:ℂ) := by
      funext s
      rw [hDl0]
      simp
    rw [hbody]
    have hb : ‖∫ t in (0:ℝ)..T, (Set.Ici γ).indicator (fun _ : ℝ => (1:ℂ)) t‖ ≤ T := by
      have h1 : ∀ x ∈ Set.uIoc (0:ℝ) T, ‖(Set.Ici γ).indicator (fun _ : ℝ => (1:ℂ)) x‖ ≤ 1 := by
        intro x _
        by_cases hx : x ∈ Set.Ici γ
        · rw [Set.indicator_of_mem hx]; simp
        · rw [Set.indicator_of_notMem hx]; simp
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := T) (C := 1)
        (f := fun t : ℝ => (Set.Ici γ).indicator (fun _ : ℝ => (1:ℂ)) t) h1
      rw [sub_zero, abs_of_nonneg hT, one_mul] at h2
      exact h2
    have hCval : ‖Cc‖ = ((p.1:ℝ) * (p.2:ℝ))⁻¹ := by
      rw [hCnorm, ← hAB]
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hposP)]
    rw [hCval]
    calc ((p.1:ℝ) * (p.2:ℝ))⁻¹
          * ‖∫ t in (0:ℝ)..T, (Set.Ici γ).indicator (fun _ : ℝ => (1:ℂ)) t‖
        ≤ ((p.1:ℝ) * (p.2:ℝ))⁻¹ * T := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = T / ((p.1:ℝ) * (p.2:ℝ)) := by ring
  · -- off-diagonal case
    rw [pairKernel_apply, if_neg hKK]
    simp only [Nat.cast_mul]
    set A : ℝ := (p.1:ℝ) * (p.2:ℝ) with hA
    set B : ℝ := (q.1:ℝ) * (q.2:ℝ) with hB
    have hA1 : 1 ≤ A := by rw [hA]; nlinarith
    have hB1 : 1 ≤ B := by rw [hB]; nlinarith
    have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
    have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hX0 : 0 < Real.sqrt (A * B) := Real.sqrt_pos.mpr (mul_pos hA0 hB0)
    have hABne : A ≠ B := by
      intro h
      apply hKK
      have h1 : ((p.1 * p.2 : ℕ) : ℝ) = ((q.1 * q.2 : ℕ) : ℝ) := by
        rw [hA, hB] at h
        push_cast
        exact h
      exact Nat.cast_injective h1
    have hqpos : (0:ℝ) < (q.1:ℝ) * (q.2:ℝ) := by nlinarith
    have hppos : (0:ℝ) < (p.1:ℝ) * (p.2:ℝ) := by nlinarith
    have hDlne : Dl ≠ 0 := by
      intro h
      apply hABne
      have hlog : Real.log ((q.1:ℝ) * (q.2:ℝ)) = Real.log ((p.1:ℝ) * (p.2:ℝ)) := by
        rw [hDl] at h
        linarith
      have e1 : Real.exp (Real.log ((q.1:ℝ) * (q.2:ℝ)))
          = Real.exp (Real.log ((p.1:ℝ) * (p.2:ℝ))) := by rw [hlog]
      rw [Real.exp_log hqpos, Real.exp_log hppos] at e1
      rw [hA, hB]
      exact e1.symm
    have hδ0 : 0 < |A - B| := abs_pos.mpr (sub_ne_zero.mpr hABne)
    have hdl0 : 0 < |Dl| := abs_pos.mpr hDlne
    have hlogb : |A - B| ≤ max A B * |Dl| := by
      have hm : 1 ≤ p.1 * p.2 := by simpa using Nat.mul_le_mul hp1 hp2
      have hn : 1 ≤ q.1 * q.2 := by simpa using Nat.mul_le_mul hq1 hq2
      have h1 := abs_sub_le_max_mul_abs_log_sub (p.1 * p.2) (q.1 * q.2) hm hn
      have hh : |A - B| ≤ max A B * |Real.log A - Real.log B| := by
        rw [hA, hB]
        push_cast at h1
        exact h1
      have hDlabs : |Dl| = |Real.log A - Real.log B| := by
        rw [hDl, hB, hA, abs_sub_comm]
      rw [hDlabs]
      exact hh
    have hstep : (1:ℝ) / |Dl| ≤ max A B / |A - B| := by
      rw [div_le_div_iff₀ hdl0 hδ0]
      simpa using hlogb
    have hkey : (2:ℝ) / (Real.sqrt (A * B) * |Dl|) ≤ 2 * max A B / (Real.sqrt (A * B) * |A - B|) := by
      rw [div_le_div_iff₀ (mul_pos hX0 hdl0) (mul_pos hX0 hδ0)]
      have h1 : 2 * |A - B| ≤ 2 * (max A B * |Dl|) := by linarith
      have h2 : (2 * |A - B|) * Real.sqrt (A * B) ≤ (2 * (max A B * |Dl|)) * Real.sqrt (A * B) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hX0)
      linarith [h2]
    have hbound := norm_intervalIntegral_indicator_exp_le γ T Dl hDlne
    calc ‖Cc‖ * ‖∫ t in (0:ℝ)..T,
            (Set.Ici γ).indicator (fun s => Complex.exp (Complex.I * ((Dl * s : ℝ) : ℂ))) t‖
        ≤ ‖Cc‖ * (2 / |Dl|) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = (Real.sqrt (A * B))⁻¹ * (2 / |Dl|) := by simp only [hCnorm]
      _ = 2 / (Real.sqrt (A * B) * |Dl|) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
            ring
      _ ≤ 2 * max A B / (Real.sqrt (A * B) * |A - B|) := hkey

end Work.ZeroDensity.Ingham
