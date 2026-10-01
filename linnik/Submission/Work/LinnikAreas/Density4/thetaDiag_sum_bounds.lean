import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_h_one_add_integral_le
import Submission.Work.LinnikAreas.Density4.thetaDiag_logsum_core

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Set MeasureTheory intervalIntegral Real

/-- Evaluation of the improper integral `∫₀^∞ t^{σ-1} e^{-t/A} dt = Γ(σ) A^σ`. -/
lemma thetaDiag_integral_Ioi (σ A : ℝ) (hσ : 0 < σ) (hA : 0 < A) :
    ∫ x in Ioi (0:ℝ), x^(σ-1) * Real.exp (-x/A) = A^σ * Real.Gamma σ := by
  have key : ∫ x in Ioi (0:ℝ), x^(σ-1) * Real.exp (-(1/A) * x^(1:ℝ))
      = (1/A)^(-(σ-1+1)/(1:ℝ)) * (1/(1:ℝ)) * Real.Gamma ((σ-1+1)/(1:ℝ)) :=
    integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) (by positivity)
  rw [show (∫ x in Ioi (0:ℝ), x^(σ-1) * Real.exp (-x/A))
        = ∫ x in Ioi (0:ℝ), x^(σ-1) * Real.exp (-(1/A) * x^(1:ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx; simp only [rpow_one]; ring_nf]
  rw [key]
  rw [show ((σ-1)+1)/(1:ℝ) = σ by ring]
  rw [show (-((σ-1)+1))/(1:ℝ) = -σ by ring]
  rw [show (1:ℝ)/(1:ℝ) = 1 by norm_num, mul_one]
  rw [one_div, inv_rpow hA.le, ← rpow_neg hA.le, neg_neg]

/-- The majorant `h t = t^{σ-1} e^{-t/A}` is antitone on `[1,∞)` when `σ ≤ 1`, `A > 0`. -/
lemma thetaDiag_h_antitone (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) :
    AntitoneOn (fun t : ℝ => t^(σ-1) * Real.exp (-t/A)) (Ici (1:ℝ)) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have h1 : t^(σ-1) ≤ s^(σ-1) := by
    have h2 : s^((1:ℝ)-σ) ≤ t^(1-σ) := Real.rpow_le_rpow hs0.le hst (by linarith)
    have h3 : s^(σ-1) = (s^(1-σ))⁻¹ := by
      rw [show σ-1 = -((1:ℝ)-σ) by ring, Real.rpow_neg hs0.le]
    have h4 : t^(σ-1) = (t^(1-σ))⁻¹ := by
      rw [show σ-1 = -((1:ℝ)-σ) by ring, Real.rpow_neg ht0.le]
    rw [h3, h4]; exact inv_anti₀ (Real.rpow_pos_of_pos hs0 _) h2
  have h5 : Real.exp (-t/A) ≤ Real.exp (-s/A) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hA.le
    linarith
  exact mul_le_mul h1 h5 (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _)

/-- `h` is integrable on `(1,∞)`: it is dominated by `e^{-t/A}`. -/
lemma thetaDiag_h_integrableOn (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) :
    IntegrableOn (fun t : ℝ => t^(σ-1) * Real.exp (-t/A)) (Ioi (1:ℝ)) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-(1/A) * t)) (Ioi (1:ℝ)) :=
    integrableOn_exp_mul_Ioi (by rw [neg_lt_zero]; positivity) 1
  refine Integrable.mono' hg ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx; left; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_of_lt (mem_Ioi.mp ht)
    have ht0 : 0 < t := lt_trans one_pos (mem_Ioi.mp ht)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
    have hr : t^(σ-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    calc t^(σ-1) * Real.exp (-t/A) ≤ 1 * Real.exp (-t/A) :=
          mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
      _ = Real.exp (-(1/A)*t) := by rw [one_mul, show -t/A = -(1/A)*t by ring]

/-- First conclusion: `∑'ₙ h(n+1) ≤ Γ(σ) A^σ`. -/
theorem thetaDiag_conj1 (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A) :
    (∑' n : ℕ, ((n:ℝ)+1)^(σ-1) * Real.exp (-((n:ℝ)+1)/A)) ≤ Real.Gamma σ * A^σ := by
  have hApos : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hchild := thetaDiag_h_one_add_integral_le σ A hσ hσ1 hApos
  set h : ℝ → ℝ := fun t => t^(σ-1) * Real.exp (-t/A) with hh
  have hanti : AntitoneOn h (Ici (1:ℝ)) := thetaDiag_h_antitone σ A hσ1 hApos
  have hint : IntegrableOn h (Ioi (1:ℝ)) := thetaDiag_h_integrableOn σ A hσ1 hApos
  have hnonneg : ∀ t ∈ Ioi (1:ℝ), 0 ≤ h t := by
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans one_pos (mem_Ioi.mp ht))) _)
      (Real.exp_pos _).le
  have hsumm : Summable (fun n : ℕ => h (n:ℝ)) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 1) (by simpa using hanti)
      (by simpa using hint) (by simpa using hnonneg)
  have hsumm1 : Summable (fun n : ℕ => h ((n:ℝ)+1)) := by
    have h' : Summable (fun n : ℕ => h ((n+1 : ℕ) : ℝ)) :=
      (summable_nat_add_iff (f := fun m : ℕ => h (m:ℝ)) 1).mpr hsumm
    exact (summable_congr (fun n => by congr 1; push_cast; ring)).mp h'
  have step1 : (∑' n : ℕ, h ((n:ℝ)+1)) = h 1 + ∑' n : ℕ, h ((n:ℝ)+2) := by
    rw [Summable.tsum_eq_zero_add hsumm1]
    have e1 : h ((↑(0:ℕ):ℝ)+1) = h 1 := by norm_num
    have e2 : (∑' n : ℕ, h (((n+1:ℕ):ℝ)+1)) = ∑' n : ℕ, h ((n:ℝ)+2) := by
      apply tsum_congr; intro n; congr 1; push_cast; ring
    rw [e1, e2]
  have step2 : (∑' n : ℕ, h ((n:ℝ)+2)) ≤ ∫ x in Ioi (1:ℝ), h x := by
    have hb := AntitoneOn.tsum_comp_add_le_integral (f := h) 1 (by simpa using hanti)
      (by simpa using hint) (by simpa using hnonneg)
    have heq : (∑' n : ℕ, h ((n:ℝ)+2)) = ∑' n : ℕ, h (↑(n+1+1) : ℝ) := by
      apply tsum_congr; intro n; congr 1; push_cast; ring
    rw [heq]; simpa using hb
  have h1 : h 1 = Real.exp (-(1:ℝ)/A) := by
    simp only [hh]; rw [show (1:ℝ)^(σ-1) = 1 by exact Real.one_rpow _]; ring
  have hintegral : (∫ x in Ioi (0:ℝ), h x) = A^σ * Real.Gamma σ := thetaDiag_integral_Ioi σ A hσ hApos
  calc (∑' n : ℕ, ((n:ℝ)+1)^(σ-1) * Real.exp (-((n:ℝ)+1)/A))
      = ∑' n : ℕ, h ((n:ℝ)+1) := by rfl
    _ = h 1 + ∑' n : ℕ, h ((n:ℝ)+2) := step1
    _ ≤ Real.exp (-(1:ℝ)/A) + ∫ x in Ioi (1:ℝ), h x := by rw [h1]; gcongr
    _ ≤ ∫ x in Ioi (0:ℝ), h x := hchild
    _ = A^σ * Real.Gamma σ := hintegral
    _ = Real.Gamma σ * A^σ := by ring

/-- Second conclusion: the summation-by-parts bound with the endpoint `M · h 1`. -/
theorem thetaDiag_conj2 (σ A M : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A) (hM : 0 < M)
    (hAM : Real.exp M ≤ A) :
    ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp M →
      (∑ n ∈ Finset.Icc 2 N, (Real.log (n:ℝ) + 1) * ((n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)))
        ≤ (∫ t in (1:ℝ)..(Real.exp M+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
          + M * ((1:ℝ)^(σ-1) * Real.exp (-(1:ℝ)/A)) := by
  have hApos : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  intro N hN hNW
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hexp1 : (1:ℝ) ≤ Real.exp M + 1 := by linarith [Real.exp_pos M]
  have hW1 : (N:ℝ) + 1 ≤ Real.exp M + 1 := by linarith
  have hg_nonneg : 0 ≤ᵐ[volume.restrict (Ioc (1:ℝ) (Real.exp M + 1))]
      (fun t : ℝ => (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht.1
    have hlog : 0 ≤ Real.log t + 1 := by have := Real.log_nonneg ht1; linarith
    exact mul_nonneg hlog (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le)
  have hg_int : IntervalIntegrable
      (fun t : ℝ => (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A))) volume (1:ℝ) (Real.exp M + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hexp1]
    apply ContinuousOn.mul
    · apply ContinuousOn.add
      · apply ContinuousOn.log continuousOn_id
        intro x hx; exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)
      · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.rpow_const continuousOn_id
        intro x hx; left; simp only [id_eq]; exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)
      · fun_prop
  have hIntmono : (∫ t in (2:ℝ)..((N:ℝ)+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
      ≤ (∫ t in (1:ℝ)..(Real.exp M + 1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A))) := by
    refine integral_mono_interval (by norm_num) ?_ hW1 hg_nonneg hg_int
    have h1N : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : Real.log (N:ℝ) ≤ M := (Real.log_le_iff_le_exp hNpos).mpr hNW
  have hcorr : Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) ≤ M * Real.exp (-(1:ℝ)/A) := by
    have h1 : 0 ≤ Real.exp (-(1:ℝ)/A) := (Real.exp_pos _).le
    calc Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) ≤ Real.exp (-(1:ℝ)/A) * M :=
          mul_le_mul_of_nonneg_left hlogN h1
      _ = M * Real.exp (-(1:ℝ)/A) := by ring
  rw [show (1:ℝ)^(σ-1) * Real.exp (-(1:ℝ)/A) = Real.exp (-(1:ℝ)/A) by
        rw [Real.one_rpow, one_mul]]
  have hcore := thetaDiag_logsum_core σ A hσ hσ1 hApos N hN
  calc (∑ n ∈ Finset.Icc 2 N, (Real.log (n:ℝ) + 1) * ((n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)))
      ≤ (∫ t in (2:ℝ)..((N:ℝ)+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
          + Real.exp (-(1:ℝ)/A) * Real.log (N:ℝ) := hcore
    _ ≤ (∫ t in (1:ℝ)..(Real.exp M+1), (Real.log t + 1) * (t^(σ-1) * Real.exp (-t/A)))
          + M * Real.exp (-(1:ℝ)/A) := by linarith

theorem thetaDiag_sum_bounds (σ A M : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A) (hM : 0 < M)
    (hAM : Real.exp M ≤ A) :
    let W : ℝ := Real.exp M
    let h : ℝ → ℝ := fun t => t^(σ-1) * Real.exp (-t/A)
    ((∑' n : ℕ, h ((n:ℝ)+1)) ≤ Real.Gamma σ * A^σ) ∧
    (∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ W →
        (∑ n ∈ Finset.Icc 2 N, (Real.log (n:ℝ) + 1) * h (n:ℝ))
          ≤ (∫ t in (1:ℝ)..(W+1), (Real.log t + 1) * h t) + M * h 1) := by
  dsimp only
  exact ⟨thetaDiag_conj1 σ A hσ hσ1 hA, thetaDiag_conj2 σ A M hσ hσ1 hA hM hAM⟩

end Work.LinnikAreas.Density4
