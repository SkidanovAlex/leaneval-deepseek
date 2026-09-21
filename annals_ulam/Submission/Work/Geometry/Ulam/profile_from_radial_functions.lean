import Mathlib
import Submission.Work.Geometry.Ulam.profileGlue_concave
import Submission.Work.Geometry.Ulam.odd_radial_profile_defs

namespace Commons.Geometry.Ulam

open Set
open scoped Topology ContDiff

noncomputable section

/-- The glued profile satisfies the two radial-graph identities. -/
lemma profileGlue_arc_identities
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        profileGlue R r (R α * Real.cos α) = R α * Real.sin α) ∧
    (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        profileGlue R r (-(r α * Real.cos α)) = r α * Real.sin α) := by
  constructor
  · intro α hα
    have himage := rightArc_fst_image_eq R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have ht_mem : R α * Real.cos α ∈ Set.Icc 0 (R 0) := by
      rw [← himage]
      exact ⟨α, hα, rfl⟩
    have hRmono := rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have hinj := hRmono.injOn
    have hleft := hinj.leftInvOn_invFunOn hα
    have hαeq : rightAlpha R (R α * Real.cos α) = α := by
      simpa [rightAlpha] using hleft
    simp [profileGlue, ht_mem, hαeq]
  · intro α hα
    by_cases hαpi : α = Real.pi / 2
    · subst α
      have hglue := profileGlue_zero_right R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two, hglue, hRr_end]
    · have hαlt : α < Real.pi / 2 := lt_of_le_of_ne hα.2 hαpi
      have hcos_pos : 0 < Real.cos α :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hα.1], hαlt⟩
      have ht_neg : -(r α * Real.cos α) < 0 := by
        nlinarith [hr_pos α hα, hcos_pos]
      have ht_not_right : -(r α * Real.cos α) ∉ Set.Icc 0 (R 0) := by
        intro h; linarith [h.1, ht_neg]
      have himage := leftArc_fst_image_eq r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      have ht_mem : -(r α * Real.cos α) ∈ Set.Icc (-(r 0)) 0 := by
        rw [← himage]
        exact ⟨α, hα, rfl⟩
      have hrmono := leftArc_fst_strictMonoOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      have hinj := hrmono.injOn
      have hleft := hinj.leftInvOn_invFunOn hα
      have hαeq : leftAlpha r (-(r α * Real.cos α)) = α := by
        simpa [leftAlpha] using hleft
      simp [profileGlue, ht_not_right, ht_mem, hαeq]

lemma profile_from_radial_functions_of_contDiff
    (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8) (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2))
    (hseam : 0 ≤ deriv r (Real.pi / 2) / r (Real.pi / 2) +
      deriv R (Real.pi / 2) / R (Real.pi / 2))
    (hf_smooth : ContDiffOn ℝ ∞ (profileGlue R r) (Set.Ioo (-(r 0)) (R 0))) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-(r 0)) (R 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-(r 0)) (R 0)) ∧
      ConcaveOn ℝ (Set.Icc (-(r 0)) (R 0)) f ∧
      f (-(r 0)) = 0 ∧ f (R 0) = 0 ∧
      (∀ t ∈ Set.Ioo (-(r 0)) (R 0), 0 < f t) ∧
      (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        f (R α * Real.cos α) = R α * Real.sin α) ∧
      (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        f (-(r α * Real.cos α)) = r α * Real.sin α) := by
  refine ⟨profileGlue R r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact profileGlue_support_subset R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end
  · exact hf_smooth
  · exact profileGlue_concaveOn_corrected R r hη hηsmall hδ hR_cont hr_cont hR_nhds hr_nhds
      hR_pos hr_pos hR_lower hr_lower hR_deriv_bound hr_deriv_bound hR_second_bound
      hr_second_bound hRr_end hseam
  · have hα := leftAlpha_neg_zero r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
    have hnot : -(r 0) ∉ Set.Icc 0 (R 0) := by
      intro h
      have hr0pos : 0 < r 0 := left_zero_pos r hr_pos
      linarith [h.1, hr0pos]
    simp [profileGlue, hnot, hα]
  · have hβ := rightAlpha_end R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have hmem : R 0 ∈ Set.Icc 0 (R 0) := ⟨le_of_lt (right_zero_pos R hR_pos), le_rfl⟩
    simp [profileGlue, hmem, hβ]
  · exact profileGlue_pos R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end
  · exact (profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).1
  · exact (profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).2

/-- The glued profile is the radial graph of the two radial functions. -/
lemma isRadialProfile_profileGlue
    (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8) (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_nhds : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    (hr_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv r) α| ≤ η)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2))
    (hseam : 0 ≤ deriv r (Real.pi / 2) / r (Real.pi / 2) +
      deriv R (Real.pi / 2) / R (Real.pi / 2))
    (hf_smooth : ContDiffOn ℝ ∞ (profileGlue R r) (Set.Ioo (-(r 0)) (R 0))) :
    IsRadialProfile R r (profileGlue R r) := by
  exact ⟨profileGlue_support_subset R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end,
    (profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).1,
    (profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).2⟩

end

end Commons.Geometry.Ulam
