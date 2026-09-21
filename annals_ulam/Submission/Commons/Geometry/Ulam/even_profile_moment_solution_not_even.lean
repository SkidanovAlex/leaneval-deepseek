import Mathlib
import Submission.Commons.Geometry.Ulam.support_subset_iff_zero_of_not_mem
import Submission.Commons.Geometry.Ulam.even_profile_deriv_sign

namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped ContDiff Pointwise RealInnerProductSpace Topology

set_option autoImplicit false

private lemma compact_support_deriv_sign_false_of_pos
    {a b : ℝ} (ha_pos : 0 < a) (hab : a < b) {h : ℝ → ℝ}
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (hh_supp : Function.support h ⊆ Set.Icc a b)
    (h_ne : ∃ s : ℝ, h s ≠ 0)
    (hsign : ∀ s : ℝ, 0 < s → (0 < h s → 0 < deriv h s) ∧ (h s < 0 → deriv h s < 0)) :
    False := by
  have hcont : Continuous h := continuousOn_univ.mp hh_cont.continuousOn
  have ha_zero : h a = 0 := by
    have h_left : h =ᶠ[𝓝[<] a] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht_not : t ∉ Set.Icc a b := by
        rw [Set.mem_Icc, not_and_or]
        left
        exact not_le_of_gt ht
      exact (Function.support_subset_iff'.1 hh_supp) t ht_not
    have htend_h : Tendsto h (𝓝[<] a) (𝓝 (h a)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htend_zero : Tendsto h (𝓝[<] a) (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] a) (𝓝 0) := tendsto_const_nhds
      exact (tendsto_congr' h_left).2 hconst
    exact tendsto_nhds_unique htend_h htend_zero
  have hb_zero : h b = 0 := by
    have h_right : h =ᶠ[𝓝[>] b] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht_not : t ∉ Set.Icc a b := by
        rw [Set.mem_Icc, not_and_or]
        right
        exact not_le_of_gt ht
      exact (Function.support_subset_iff'.1 hh_supp) t ht_not
    have htend_h : Tendsto h (𝓝[>] b) (𝓝 (h b)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htend_zero : Tendsto h (𝓝[>] b) (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] b) (𝓝 0) := tendsto_const_nhds
      exact (tendsto_congr' h_right).2 hconst
    exact tendsto_nhds_unique htend_h htend_zero
  rcases h_ne with ⟨c, hc_ne⟩
  have hc_mem : c ∈ Set.Icc a b := hh_supp (by simpa [Function.mem_support] using hc_ne)
  have hnonempty : (Set.Icc a b).Nonempty := ⟨c, hc_mem⟩
  have hcomp : IsCompact (Set.Icc a b) := isCompact_Icc
  by_cases hc_pos : 0 < h c
  · obtain ⟨m, hmIcc, hmax⟩ := hcomp.exists_isMaxOn hnonempty hcont.continuousOn
    have hm_pos : 0 < h m := lt_of_lt_of_le hc_pos (hmax hc_mem)
    have hm_ioo : m ∈ Set.Ioo a b := by
      constructor
      · exact lt_of_le_of_ne hmIcc.1 (by
          intro heq
          rw [← heq, ha_zero] at hm_pos
          linarith)
      · exact lt_of_le_of_ne hmIcc.2 (by
          intro heq
          rw [heq, hb_zero] at hm_pos
          linarith)
    have hmax_on_ioo : IsMaxOn h (Set.Ioo a b) m := by
      intro x hx
      exact hmax (Set.Ioo_subset_Icc_self hx)
    have hlocal_max : IsLocalMax h m := by
      have hloc_on : IsLocalMaxOn h (Set.Ioo a b) m := hmax_on_ioo.localize
      exact hloc_on.isLocalMax (Ioo_mem_nhds hm_ioo.1 hm_ioo.2)
    have hderiv_zero : deriv h m = 0 := hlocal_max.deriv_eq_zero
    have hm_gt_zero : 0 < m := lt_of_lt_of_le ha_pos hmIcc.1
    have hsign_m := (hsign m hm_gt_zero).1 hm_pos
    linarith
  · have hc_neg : h c < 0 := lt_of_le_of_ne (le_of_not_gt hc_pos) hc_ne
    obtain ⟨m, hmIcc, hmin⟩ := hcomp.exists_isMinOn hnonempty hcont.continuousOn
    have hm_neg : h m < 0 := lt_of_le_of_lt (hmin hc_mem) hc_neg
    have hm_ioo : m ∈ Set.Ioo a b := by
      constructor
      · exact lt_of_le_of_ne hmIcc.1 (by
          intro heq
          rw [← heq, ha_zero] at hm_neg
          linarith)
      · exact lt_of_le_of_ne hmIcc.2 (by
          intro heq
          rw [heq, hb_zero] at hm_neg
          linarith)
    have hmin_on_ioo : IsMinOn h (Set.Ioo a b) m := by
      intro x hx
      exact hmin (Set.Ioo_subset_Icc_self hx)
    have hlocal_min : IsLocalMin h m := by
      have hloc_on : IsLocalMinOn h (Set.Ioo a b) m := hmin_on_ioo.localize
      exact hloc_on.isLocalMin (Ioo_mem_nhds hm_ioo.1 hm_ioo.2)
    have hderiv_zero : deriv h m = 0 := hlocal_min.deriv_eq_zero
    have hm_gt_zero : 0 < m := lt_of_lt_of_le ha_pos hmIcc.1
    have hsign_m := (hsign m hm_gt_zero).2 hm_neg
    linarith

lemma even_profile_moment_solution_not_even
    (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} {h x y f : ℝ → ℝ}
    (hτ : 0 < τ) (hτsmall : 2 * τ < 1)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (h_ne : ∃ s : ℝ, h s ≠ 0)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (hf_supp : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ¬ ∀ t : ℝ, f (-t) = f t := by
  intro hf_even
  have hlower_pos : 0 < 1 - 2 * τ := by nlinarith
  have h0_not_mem : (0 : ℝ) ∉ Set.Icc (1 - 2 * τ) (1 - τ) := by
    rw [Set.mem_Icc]
    intro h
    nlinarith [h.1, hτsmall]
  have h0 : h 0 = 0 := support_subset_iff_zero_of_not_mem hh_supp h0_not_mem
  have hsign := even_profile_deriv_sign (n := n) hn (h := h) (x := x) (y := y) (f := f)
    hf_supp hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hf_even hxy hJ
  have hab : 1 - 2 * τ < 1 - τ := by nlinarith
  have hcontra : False := compact_support_deriv_sign_false_of_pos
    (a := 1 - 2 * τ) (b := 1 - τ) hlower_pos hab
    (h := h) hh_cont hh_supp h_ne hsign
  exact hcontra

end Commons.Geometry.Ulam
