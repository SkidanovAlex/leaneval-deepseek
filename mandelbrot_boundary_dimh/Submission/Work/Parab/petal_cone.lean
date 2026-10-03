import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup

/-!
# The flower: elementary cone geometry

Two purely geometric facts behind `ParabData.flower`:

* `petal_cone`: the attracting petal `Petal r M = {z | ‖z‖ < r, Re z < -M‖z‖²}` contains the
  cone `{|arg z| ≥ π/2 + δ}` near `0` (every direction strictly inside the open half-plane
  `Re z < 0` is eventually in the petal);
* `flower_of_cones`: if `Ωp` contains the cone `{|arg z| ≥ π/2 + δ}` near `0` and the repelling
  piece `φ '' QLeft ξ` contains the complementary cone `{|arg z| ≤ π/2 + δ}`, then
  `Ωp ∪ φ '' QLeft ξ ∪ {0}` is a neighbourhood of `0` (the two cones cover the whole plane).
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab

noncomputable section

/-- **The petal contains the dominant cone.**  For every `δ > 0` there is `ρ > 0` such that every
`z` with `0 < ‖z‖ < ρ` and `|arg z| ≥ π/2 + δ` lies in the petal `Petal r M`. -/
theorem petal_cone {r M δ : ℝ} (hr : 0 < r) (hM : 0 < M) (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Real.pi / 2 + δ ≤ |z.arg| →
      z ∈ Work.FatouCoord.Petal r M := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  refine ⟨min r (Real.sin δ / (2 * M)), lt_min hr (by positivity), fun z hz0 hz harg => ?_⟩
  have hzr : ‖z‖ < r := lt_of_lt_of_le hz (min_le_left _ _)
  have hzρ : ‖z‖ < Real.sin δ / (2 * M) := lt_of_lt_of_le hz (min_le_right _ _)
  have hzn : 0 < ‖z‖ := hz0
  have hargpi : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
  -- the real part is bounded by `-‖z‖ sin δ`
  have hcos : Real.cos z.arg ≤ -Real.sin δ := by
    rw [← Real.cos_abs]
    have hcs := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 2 + δ) (y := |z.arg|)
      (by positivity) hargpi harg
    rwa [show Real.cos (Real.pi / 2 + δ) = -Real.sin δ by
      rw [Real.cos_add]; simp] at hcs
  have hre : z.re = ‖z‖ * Real.cos z.arg := by
    have h := Complex.cos_arg (x := z) (norm_pos_iff.mp hzn)
    rw [h]; field_simp
  have h1 : z.re ≤ -‖z‖ * Real.sin δ := by
    rw [hre]
    nlinarith [hcos, hzn.le]
  have h2 : -‖z‖ * Real.sin δ < -M * ‖z‖ ^ 2 := by
    have h3 : M * ‖z‖ * ‖z‖ < M * ‖z‖ * (Real.sin δ / (2 * M)) := by
      exact mul_lt_mul_of_pos_left hzρ (by positivity)
    have h4 : M * ‖z‖ * (Real.sin δ / (2 * M)) = ‖z‖ * Real.sin δ / 2 := by
      field_simp
    nlinarith [h3, h4, hzn.le, hsin]
  rw [Work.FatouCoord.mem_Petal, Complex.normSq_eq_norm_sq]
  exact ⟨hzr, lt_of_le_of_lt h1 h2⟩

/-- **The flower from the two cone inclusions.**  If `Ωp` contains the cone `|arg z| ≥ π/2 + δ`
near `0` and every point of the complementary cone `|arg z| ≤ π/2 + δ` near `0` is the image under
`φ` of a point of `QLeft ξ`, then `Ωp ∪ φ '' QLeft ξ ∪ {0}` is a neighbourhood of `0`. -/
theorem flower_of_cones {Ωp : Set ℂ} {φ : ℂ → ℂ} {ξ δ ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hpetal : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ₁ → Real.pi / 2 + δ ≤ |z.arg| → z ∈ Ωp)
    (hcover : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ₂ → |z.arg| ≤ Real.pi / 2 + δ →
      ∃ w ∈ MandelDim.QLeft ξ, φ w = z) :
    Ωp ∪ φ '' MandelDim.QLeft ξ ∪ {0} ∈ 𝓝 (0 : ℂ) := by
  refine mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) (lt_min hρ₁ hρ₂)) ?_
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
  have hz₁ : ‖z‖ < ρ₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : ‖z‖ < ρ₂ := lt_of_lt_of_le hz (min_le_right _ _)
  rcases eq_or_ne z 0 with h | h
  · subst h
    exact Or.inr rfl
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr h
    by_cases hcase : |z.arg| ≤ Real.pi / 2 + δ
    · obtain ⟨w, hwQ, hwz⟩ := hcover z hz0 hz₂ hcase
      exact Or.inl (Or.inr ⟨w, hwQ, hwz⟩)
    · rw [not_le] at hcase
      exact Or.inl (Or.inl (hpetal z hz0 hz₁ hcase.le))

end

end Work.Parab
