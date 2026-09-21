import Submission.Work.OddRadon.RadialDefs
import Submission.Work.OddRadon.strictConcaveOn_profileGlue
import Submission.Work.Geometry.Ulam.profile_from_radial_functions

/-!
# The reconstructed profile is `C^∞`, strictly concave, positive inside, zero at the ends

`exists_profile_of_radial_data_strict` is `exists_profile_of_radial_data` with the concavity
upgraded to strict concavity (via `strictConcaveOn_profileGlue`), with the witness
`f = Commons.Geometry.Ulam.profileGlue R r` made explicit.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The profile reconstruction, with strict concavity.**  Under the same `C²`-closeness
hypotheses as `exists_profile_of_radial_data`, `profileGlue R r` is a profile with support in
`[-r 0, R 0]`, of class `C^∞` on the open interval, *strictly concave* there, positive there,
vanishing at the two ends, and it is the radial graph of `(R, r)`. -/
theorem exists_profile_of_radial_data_strict (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η)
    (hηsmall : η < 1 / 8) (hδ : 0 < δ)
    (hR_cont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r (Set.Icc 0 (Real.pi / 2)))
    (hR_nhds : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
    (hr_nhds : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 + δ)))
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
    (hf_smooth : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (Commons.Geometry.Ulam.profileGlue R r) (Set.Ioo (-(r 0)) (R 0))) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-(r 0)) (R 0) ∧
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) f (Set.Ioo (-(r 0)) (R 0)) ∧
      StrictConcaveOn ℝ (Set.Ioo (-(r 0)) (R 0)) f ∧
      f (-(r 0)) = 0 ∧ f (R 0) = 0 ∧
      (∀ t ∈ Set.Ioo (-(r 0)) (R 0), 0 < f t) ∧
      IsRadialGraph R r f := by
  have hnot : -(r 0) ∉ Set.Icc 0 (R 0) := by
    intro h
    have hr0 : 0 < r 0 := Commons.Geometry.Ulam.left_zero_pos r hr_pos
    linarith [h.1, hr0]
  have hmem : R 0 ∈ Set.Icc 0 (R 0) :=
    ⟨le_of_lt (Commons.Geometry.Ulam.right_zero_pos R hR_pos), le_rfl⟩
  refine ⟨Commons.Geometry.Ulam.profileGlue R r, ?_, hf_smooth,
    strictConcaveOn_profileGlue R r hη hηsmall hR_cont hr_cont hR_pos hr_pos hR_lower hr_lower
      hR_deriv_bound hr_deriv_bound hR_second_bound hr_second_bound hf_smooth, ?_, ?_, ?_, ?_⟩
  · exact Commons.Geometry.Ulam.profileGlue_support_subset R r hη hηsmall hR_cont hr_cont
      hR_pos hr_pos hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end
  · have hα := Commons.Geometry.Ulam.leftAlpha_neg_zero r hη hηsmall hr_cont hr_pos hr_lower
      hr_deriv_bound
    have hmem2 : -(r 0) ∈ Set.Icc (-(r 0)) (0 : ℝ) :=
      ⟨le_rfl, by linarith [Commons.Geometry.Ulam.left_zero_pos r hr_pos]⟩
    simp [Commons.Geometry.Ulam.profileGlue, hnot, hmem2, hα]
  · have hβ := Commons.Geometry.Ulam.rightAlpha_end R hη hηsmall hR_cont hR_pos hR_lower
      hR_deriv_bound
    simp [Commons.Geometry.Ulam.profileGlue, hmem, hβ]
  · exact Commons.Geometry.Ulam.profileGlue_pos R r hη hηsmall hR_cont hr_cont hR_pos hr_pos
      hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end
  · exact ⟨(Commons.Geometry.Ulam.profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont
      hR_pos hr_pos hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).1,
      (Commons.Geometry.Ulam.profileGlue_arc_identities R r hη hηsmall hR_cont hr_cont
      hR_pos hr_pos hR_lower hr_lower hR_deriv_bound hr_deriv_bound hRr_end).2⟩

end Work.OddRadon
