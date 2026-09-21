import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.Geometry.Ulam.profile_from_radial_functions

namespace Work.OddRadon

theorem exists_profile_of_radial_data (R r : ℝ → ℝ) {η δ : ℝ} (hη : 0 < η)
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
      ConcaveOn ℝ (Set.Icc (-(r 0)) (R 0)) f ∧
      f (-(r 0)) = 0 ∧ f (R 0) = 0 ∧
      (∀ t ∈ Set.Ioo (-(r 0)) (R 0), 0 < f t) ∧
      IsRadialGraph R r f := by
  obtain ⟨f, hsupp, hcont, hconc, hleft, hright, hpos, hupper, hlower⟩ :=
    Commons.Geometry.Ulam.profile_from_radial_functions_of_contDiff R r hη hηsmall hδ
      hR_cont hr_cont hR_nhds hr_nhds hR_pos hr_pos hR_lower hr_lower hR_deriv_bound
      hr_deriv_bound hR_second_bound hr_second_bound hRr_end hseam hf_smooth
  exact ⟨f, hsupp, hcont, hconc, hleft, hright, hpos, hupper, hlower⟩

end Work.OddRadon
