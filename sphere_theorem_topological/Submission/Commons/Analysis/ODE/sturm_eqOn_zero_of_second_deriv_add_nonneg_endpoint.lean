import Mathlib
import Submission.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

theorem sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint {lam t₁ : ℝ} (hlam : 0 < lam)
    (ht₁ : 0 < t₁) (ht₁π : t₁ < Real.pi / Real.sqrt lam) {h g G : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 t₁)) (h0 : h 0 = 0)
    (hnn : ∀ t ∈ Set.Icc 0 t₁, 0 ≤ h t)
    (hd1 : ∀ t ∈ Set.Ioo 0 t₁, HasDerivAt h (g t) t)
    (hd2 : ∀ t ∈ Set.Ioo 0 t₁, HasDerivAt g (G t) t)
    (hineq : ∀ t ∈ Set.Ioo 0 t₁, 0 ≤ G t + lam * h t)
    (ht₁0 : h t₁ = 0) : Set.EqOn h (fun _ => 0) (Set.Icc 0 t₁) := by
  set a : ℝ := Real.sqrt lam with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; exact Real.sqrt_pos_of_pos hlam
  have ha_sq : a ^ 2 = lam := by rw [ha_def]; exact Real.sq_sqrt hlam.le
  have ht₁_lt_a : t₁ < Real.pi / a := by rw [ha_def]; exact ht₁π
  have hat1 : a * t₁ < Real.pi := by
    have h1 : a * t₁ < a * (Real.pi / a) := mul_lt_mul_of_pos_left ht₁_lt_a ha_pos
    have h2 : a * (Real.pi / a) = Real.pi := by field_simp
    linarith
  obtain ⟨c, hc_mem, hc_max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, left_mem_Icc.mpr ht₁.le⟩ hcont
  rcases eq_or_ne (h c) 0 with hM | hM
  · intro t ht
    have h1 : h t ≤ 0 := by rw [← hM]; exact hc_max ht
    have h2 : 0 ≤ h t := hnn t ht
    linarith
  · have hc_pos : 0 < h c := lt_of_le_of_ne' (hnn c hc_mem) hM
    have hc0 : 0 < c := by
      rcases eq_or_lt_of_le hc_mem.1 with h | h
      · rw [← h, h0] at hc_pos; exact absurd hc_pos (lt_irrefl 0)
      · exact h
    have hct₁ : c < t₁ := by
      rcases eq_or_lt_of_le hc_mem.2 with h | h
      · rw [h, ht₁0] at hc_pos; exact absurd hc_pos (lt_irrefl 0)
      · exact h
    have hc_Ioo : c ∈ Set.Ioo 0 t₁ := ⟨hc0, hct₁⟩
    have hgc : g c = 0 := by
      have hloc : IsLocalMax h c := by
        filter_upwards [Icc_mem_nhds hc0 hct₁] with t ht
        exact hc_max ht
      exact hloc.hasDerivAt_eq_zero (hd1 c hc_Ioo)
    have hsin_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.sin (a * (s - c)))
        (a * Real.cos (a * (t - c))) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
        have := (hasDerivAt_id t).sub_const c
        simpa using this.const_mul a
      have := h1.sin
      simpa [Real.cos_zero, mul_comm, sub_self, mul_zero] using this
    have hcos_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (a * (s - c)))
        (-(a * Real.sin (a * (t - c)))) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => a * (s - c)) a t := by
        have := (hasDerivAt_id t).sub_const c
        simpa using this.const_mul a
      have := h1.cos
      simpa [Real.sin_zero, mul_comm, sub_self, mul_zero] using this
    set w : ℝ → ℝ := fun t => h t - h c * Real.cos (a * (t - c)) with hw_def
    set w' : ℝ → ℝ := fun t => g t + h c * a * Real.sin (a * (t - c)) with hw'_def
    set F : ℝ → ℝ := fun t => G t + h c * a ^ 2 * Real.cos (a * (t - c)) with hF_def
    have hw_deriv : ∀ t ∈ Set.Ioo 0 t₁, HasDerivAt w (w' t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => h c * Real.cos (a * (s - c)))
          (h c * (-(a * Real.sin (a * (t - c))))) t := (hcos_deriv t).const_mul (h c)
      have hd := (hd1 t ht).sub h2
      have heqval : g t - h c * (-(a * Real.sin (a * (t - c)))) = w' t := by
        rw [hw'_def]; ring
      rw [hw_def, ← heqval]
      exact hd
    have hw'_deriv : ∀ t ∈ Set.Ioo 0 t₁, HasDerivAt w' (F t) t := by
      intro t ht
      have h2 : HasDerivAt (fun s : ℝ => h c * a * Real.sin (a * (s - c)))
          ((h c * a) * (a * Real.cos (a * (t - c)))) t := (hsin_deriv t).const_mul (h c * a)
      have hd := (hd2 t ht).add h2
      have heqval : G t + (h c * a) * (a * Real.cos (a * (t - c))) = F t := by
        rw [hF_def]; ring
      rw [hw'_def, ← heqval]
      exact hd
    have hF_nn : ∀ t ∈ Set.Ioo 0 t₁, 0 ≤ F t + a ^ 2 * w t := by
      intro t ht
      have hineq_t := hineq t ht
      have key : F t + a ^ 2 * w t = G t + lam * h t := by rw [hF_def, hw_def, ha_sq]; ring
      rw [key]; exact hineq_t
    have hwc : w c = 0 := by simp [hw_def]
    have hw'c : w' c = 0 := by simp [hw'_def, hgc]
    have hw_at_c : HasDerivAt w 0 c := by
      have h := hw_deriv c hc_Ioo
      rwa [hw'c] at h
    have hwcont_R : ContinuousOn w (Set.Icc c t₁) := by
      have h1 : ContinuousOn h (Set.Icc c t₁) :=
        hcont.mono (fun x hx => ⟨le_trans (le_of_lt hc0) hx.1, hx.2⟩)
      have h2 : ContinuousOn (fun s : ℝ => h c * Real.cos (a * (s - c))) (Set.Icc c t₁) :=
        (by continuity : Continuous (fun s : ℝ => h c * Real.cos (a * (s - c)))).continuousOn
      rw [hw_def]
      exact h1.sub h2
    have hR : ∀ t ∈ Set.Icc c t₁, 0 ≤ w t := by
      refine sturm_max_principle_right (w := w) (w' := w') (F := F) ha_pos hct₁ ?_ hwcont_R ?_ ?_ hw_at_c hwc ?_
      · have h1 : a * (t₁ - c) < a * t₁ := mul_lt_mul_of_pos_left (by linarith [hc0]) ha_pos
        linarith
      · intro t ht
        exact hw_deriv t ⟨lt_trans hc0 ht.1, ht.2⟩
      · intro t ht
        exact hw'_deriv t ⟨lt_trans hc0 ht.1, ht.2⟩
      · intro t ht
        exact hF_nn t ⟨lt_trans hc0 ht.1, ht.2⟩
    have hcos₁ : Real.cos (a * (t₁ - c)) ≤ 0 := by
      have hR1 := hR t₁ ⟨hct₁.le, le_refl t₁⟩
      have hw_eq : w t₁ = -h c * Real.cos (a * (t₁ - c)) := by
        simp only [hw_def, ht₁0]; ring
      rw [hw_eq] at hR1
      have h' : h c * Real.cos (a * (t₁ - c)) ≤ 0 := by linarith
      have h'0 : h c * Real.cos (a * (t₁ - c)) ≤ h c * 0 := by rw [mul_zero]; exact h'
      exact le_of_mul_le_mul_left h'0 hc_pos
    have hwcont_L : ContinuousOn w (Set.Icc 0 c) := by
      have h1 : ContinuousOn h (Set.Icc 0 c) :=
        hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hc_Ioo.2.le⟩)
      have h2 : ContinuousOn (fun s : ℝ => h c * Real.cos (a * (s - c))) (Set.Icc 0 c) :=
        (by continuity : Continuous (fun s : ℝ => h c * Real.cos (a * (s - c)))).continuousOn
      rw [hw_def]
      exact h1.sub h2
    have hL : ∀ t ∈ Set.Icc 0 c, 0 ≤ w t := by
      refine sturm_max_principle_left (w := w) (w' := w') (F := F) ha_pos hc0 ?_ hwcont_L ?_ ?_ hw_at_c hwc ?_
      · have h1 : a * c < a * t₁ := mul_lt_mul_of_pos_left hct₁ ha_pos
        linarith
      · intro t ht
        exact hw_deriv t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
      · intro t ht
        exact hw'_deriv t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
      · intro t ht
        exact hF_nn t ⟨ht.1, lt_trans ht.2 hc_Ioo.2⟩
    have hcos0 : Real.cos (a * c) ≤ 0 := by
      have hL1 := hL 0 ⟨le_refl 0, hc0.le⟩
      have hw_eq : w 0 = -h c * Real.cos (a * c) := by
        have harg : a * (0 - c) = -(a * c) := by ring
        simp only [hw_def, h0, harg, Real.cos_neg]
        ring
      rw [hw_eq] at hL1
      have h' : h c * Real.cos (a * c) ≤ 0 := by linarith
      have h'0 : h c * Real.cos (a * c) ≤ h c * 0 := by rw [mul_zero]; exact h'
      exact le_of_mul_le_mul_left h'0 hc_pos
    have hge1 : Real.pi / 2 ≤ a * (t₁ - c) := by
      have hpos : 0 < a * (t₁ - c) := mul_pos ha_pos (by linarith)
      by_contra hcon
      push Not at hcon
      have : 0 < Real.cos (a * (t₁ - c)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hcon⟩
      linarith
    have hge0 : Real.pi / 2 ≤ a * c := by
      have hpos : 0 < a * c := mul_pos ha_pos hc0
      by_contra hcon
      push Not at hcon
      have : 0 < Real.cos (a * c) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hcon⟩
      linarith
    have : Real.pi ≤ a * t₁ := by
      have : a * t₁ = a * c + a * (t₁ - c) := by ring
      linarith
    linarith

end Commons.Analysis.ODE
