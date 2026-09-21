import Mathlib
import Submission.Work.Geometry.Ulam.radial_profile_reconstruction
import Submission.Work.Geometry.Ulam.continuous_invFunOn

namespace Commons.Geometry.Ulam

open Set
open scoped Topology ContDiff

noncomputable section

/-- The numerator in the second-derivative formula is positive under the
`C²`-closeness hypotheses. -/
lemma rightProfile_deriv2_num_pos
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 < R α ^ 2 - R α * deriv (deriv R) α + 2 * deriv R α ^ 2 := by
  have hRlow : 1 - η ≤ R α := hR_lower α hα
  have hRpos : 0 < R α := by nlinarith [hRlow, hηsmall]
  have hR''le : deriv (deriv R) α ≤ η := (abs_le.mp (hR_second_bound α hα)).2
  have hR'2_nonneg : 0 ≤ deriv R α ^ 2 := sq_nonneg _
  have hmain : 0 < R α * (R α - η) := by
    have h1 : 0 < R α := hRpos
    have h2 : 0 < R α - η := by nlinarith [hRlow, hηsmall]
    exact mul_pos h1 h2
  nlinarith [hR''le, hR'2_nonneg, hmain]

/-- The denominator in the second-derivative formula is negative at interior
points. -/
lemma rightProfile_deriv2_den_neg
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (R 0)) :
    (deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
        R (rightAlpha R t) * Real.sin (rightAlpha R t)) < 0 := by
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [α, Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [α, Real.cos_pi_div_two]
    linarith [ht.1]
  exact rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    ⟨hα_pos, hα_lt_pi_div_two⟩

/-- The second derivative of the right-branch profile is strictly negative on
the interior of its interval. -/
lemma rightProfile_deriv2_neg
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η) :
    ∀ t ∈ Set.Ioo 0 (R 0), deriv^[2] (rightProfile R) t < 0 := by
  intro t ht
  rw [show deriv^[2] (rightProfile R) t = deriv (deriv (rightProfile R)) t by rfl]
  rw [rightProfile_deriv2 R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound t ht]
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hnum : 0 < R α ^ 2 - R α * deriv (deriv R) α + 2 * deriv R α ^ 2 :=
    rightProfile_deriv2_num_pos R hη hηsmall hR_lower hR_second_bound hα_mem
  have hden : deriv R α * Real.cos α - R α * Real.sin α < 0 := by
    simpa [α] using rightProfile_deriv2_den_neg R hη hηsmall hR_cont hR_pos hR_lower
      hR_deriv_bound ht
  have hden3 : (deriv R α * Real.cos α - R α * Real.sin α) ^ 3 < 0 := by
    rw [pow_three]
    exact mul_neg_of_neg_of_pos hden (mul_pos_of_neg_of_neg hden hden)
  exact div_neg_of_pos_of_neg hnum hden3

end

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- The right-branch profile is strictly concave on `[0,R 0]` once its
continuity is known; the analytic content is the strict negativity of the
second derivative proved above. -/
lemma rightProfile_strictConcaveOn_of_continuous
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η)
    (hcont : ContinuousOn (rightProfile R) (Set.Icc 0 (R 0))) :
    StrictConcaveOn ℝ (Set.Icc 0 (R 0)) (rightProfile R) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont ?_
  intro t ht
  rw [interior_Icc] at ht
  exact rightProfile_deriv2_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    hR_second_bound t ht

end Commons.Geometry.Ulam


namespace Commons.Geometry.Ulam

/-- The right inverse branch is continuous on the whole interval `[0,R 0]`,
by the compact/Hausdorff inverse-continuity lemma applied to the right arc. -/
lemma rightAlpha_continuousOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ContinuousOn (rightAlpha R) (Set.Icc 0 (R 0)) := by
  have h := continuousOn_invFunOn_of_strictAntiOn_of_continuousOn
    (f := fun α => R α * Real.cos α) (a := 0) (b := Real.pi / 2)
    (by positivity)
    (hR_cont.continuousOn.mul Real.continuous_cos.continuousOn)
    (rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound)
  rw [rightArc_fst_image_eq R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound] at h
  change ContinuousOn (Function.invFunOn (fun α => R α * Real.cos α) (Set.Icc 0 (Real.pi / 2)))
    (Set.Icc 0 (R 0))
  exact h

/-- The right-branch profile is continuous on `[0,R 0]`. -/
lemma rightProfile_continuousOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ContinuousOn (rightProfile R) (Set.Icc 0 (R 0)) := by
  have hα := rightAlpha_continuousOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have hR_cont' : ContinuousOn R (Set.Icc 0 (Real.pi / 2)) := hR_cont.continuousOn
  have hsin : ContinuousOn (fun α : ℝ => Real.sin α) (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn
  have hmaps : Set.MapsTo (rightAlpha R) (Set.Icc 0 (R 0)) (Set.Icc 0 (Real.pi / 2)) := by
    intro t ht
    exact (rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht).1
  have hcomp := (hR_cont'.mul hsin).comp hα hmaps
  change ContinuousOn (fun x => R (rightAlpha R x) * Real.sin (rightAlpha R x)) (Set.Icc 0 (R 0))
  exact hcomp

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- Unconditional right-branch strict concavity. -/
lemma rightProfile_strictConcaveOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η) :
    StrictConcaveOn ℝ (Set.Icc 0 (R 0)) (rightProfile R) :=
  rightProfile_strictConcaveOn_of_continuous R hη hηsmall hR_cont hR_pos hR_lower
    hR_deriv_bound hR_second_bound
    (rightProfile_continuousOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound)

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

/-- The right branch as a concave function on its half-interval. -/
lemma rightProfile_concaveOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hR_second_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv R) α| ≤ η) :
    ConcaveOn ℝ (Set.Icc 0 (R 0)) (rightProfile R) :=
  (rightProfile_strictConcaveOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    hR_second_bound).concaveOn

end Commons.Geometry.Ulam
