import Mathlib
import Submission.Work.Geometry.Ulam.right_profile_concave
import Submission.Work.Geometry.Ulam.left_profile_concave

namespace Commons.Geometry.Ulam

open Set
open scoped Topology ContDiff

noncomputable section

lemma leftAlpha_neg_zero
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    leftAlpha r (-(r 0)) = 0 := by
  have hmem : -(r 0) ∈ Set.Icc (-(r 0)) 0 :=
    ⟨le_rfl, neg_nonpos.mpr (le_of_lt (left_zero_pos r hr_pos))⟩
  have hspec := leftAlpha_spec r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound hmem
  have hinj := leftArc_fst_strictMonoOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  apply hinj.injOn hspec.1 h0mem
  change -(r (leftAlpha r (-(r 0))) * Real.cos (leftAlpha r (-(r 0)))) =
    -(r 0 * Real.cos 0)
  rw [hspec.2]
  simp

lemma rightAlpha_end
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    rightAlpha R (R 0) = 0 := by
  have hmem : R 0 ∈ Set.Icc 0 (R 0) :=
    ⟨le_of_lt (right_zero_pos R hR_pos), le_rfl⟩
  have hspec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hmem
  have hinj := rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  apply hinj.injOn hspec.1 h0mem
  change R (rightAlpha R (R 0)) * Real.cos (rightAlpha R (R 0)) = R 0 * Real.cos 0
  rw [hspec.2]
  simp

lemma profileGlue_eq_leftProfile_Icc
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2))
    {t : ℝ} (ht : t ∈ Set.Icc (-(r 0)) 0) :
    profileGlue R r t = leftProfile r t := by
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · by_cases hlow : t = -(r 0)
    · subst t
      have hα := leftAlpha_neg_zero r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      have hβ := rightAlpha_end r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      have hnot : -(r 0) ∉ Set.Icc 0 (R 0) := by
        intro h
        have hr0pos : 0 < r 0 := left_zero_pos r hr_pos
        linarith [h.1, hr0pos]
      have hmem : -(r 0) ∈ Set.Icc (-(r 0)) 0 :=
        ⟨le_rfl, neg_nonpos.mpr (le_of_lt (left_zero_pos r hr_pos))⟩
      simp [profileGlue, leftProfile, rightProfile, hnot, hmem, hα, hβ]
    · have htIoo : t ∈ Set.Ioo (-(r 0)) 0 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hlow), htneg⟩
      exact profileGlue_eq_leftProfile R r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound htIoo
  · subst t
    have hglue : profileGlue R r 0 = R (Real.pi / 2) :=
      profileGlue_zero_right R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have hleft : leftProfile r 0 = r (Real.pi / 2) := by
      have h := rightAlpha_zero r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
      simp [leftProfile, rightProfile, h]
    rw [hglue, hleft, hRr_end]
  · linarith [ht.2, htpos]

lemma profileGlue_eq_rightProfile_Icc
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (R 0)) :
    profileGlue R r t = rightProfile R t := by
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · linarith [ht.1, htneg]
  · subst t
    have hglue : profileGlue R r 0 = R (Real.pi / 2) :=
      profileGlue_zero_right R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    have hright : rightProfile R 0 = R (Real.pi / 2) := by
      have h := rightAlpha_zero R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      simp [rightProfile, h]
    rw [hglue, hright]
  · rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact profileGlue_eq_rightProfile R r ⟨htpos, hlt⟩
    · subst t
      have hβ := rightAlpha_end R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      have hmem : R 0 ∈ Set.Icc 0 (R 0) :=
        ⟨le_of_lt (right_zero_pos R hR_pos), le_rfl⟩
      simp [profileGlue, rightProfile, hmem, hβ]

lemma profileGlue_continuousOn
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
    ContinuousOn (profileGlue R r) (Set.Icc (-(r 0)) (R 0)) := by
  have hleft_cont : ContinuousOn (profileGlue R r) (Set.Icc (-(r 0)) 0) := by
    have hneg : ContinuousOn (fun t : ℝ => -t) (Set.Icc (-(r 0)) 0) := continuous_neg.continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc (-(r 0)) 0) (Set.Icc 0 (r 0)) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
    have hleft_base : ContinuousOn (leftProfile r) (Set.Icc (-(r 0)) 0) := by
      have h := (rightProfile_continuousOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound).comp hneg hmaps
      change ContinuousOn (fun t : ℝ => rightProfile r (-t)) (Set.Icc (-(r 0)) 0) at h
      exact h
    exact hleft_base.congr (by
      intro t ht
      exact profileGlue_eq_leftProfile_Icc R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
        hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end ht)
  have hright_cont : ContinuousOn (profileGlue R r) (Set.Icc 0 (R 0)) := by
    have hright_base : ContinuousOn (rightProfile R) (Set.Icc 0 (R 0)) :=
      rightProfile_continuousOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    exact hright_base.congr (by
      intro t ht
      exact profileGlue_eq_rightProfile_Icc R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht)
  have hunion := ContinuousOn.union_of_isClosed hleft_cont hright_cont isClosed_Icc isClosed_Icc
  have hset : Set.Icc (-(r 0)) 0 ∪ Set.Icc 0 (R 0) = Set.Icc (-(r 0)) (R 0) := by
    ext t
    constructor
    · intro h
      rcases h with h | h
      · exact ⟨h.1, le_trans h.2 (le_of_lt (right_zero_pos R hR_pos))⟩
      · exact ⟨le_trans (neg_nonpos.mpr (le_of_lt (left_zero_pos r hr_pos))) h.1, h.2⟩
    · intro h
      by_cases ht : t ≤ 0
      · left; exact ⟨h.1, ht⟩
      · right; exact ⟨le_of_lt (lt_of_not_ge ht), h.2⟩
  rwa [hset] at hunion

end

end Commons.Geometry.Ulam
