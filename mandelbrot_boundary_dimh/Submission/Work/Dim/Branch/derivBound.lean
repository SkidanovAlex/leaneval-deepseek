import Mathlib
import Submission.Work.Dim.Branch.SchwarzPick

namespace Work.Dim.Branch

open Metric Set

/-- Reduction of `derivBound` to the unit-disk Schwarz–Pick estimate `SchwarzPick`.

Given `φ` holomorphic on `ball p ρ` mapping it into `closedBall p (ρ/2)`, the affine
change of variables `u ↦ p + ρ u` turns it into a map `g` of the unit disk into
`closedBall 0 (1/2)`; scaling by `2` lands in `closedBall 0 1`, to which Schwarz–Pick
applies. -/
theorem derivBound :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ (φ : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ φ (Metric.ball p ρ) →
        Set.MapsTo φ (Metric.ball p ρ) (Metric.closedBall p (ρ / 2)) →
        ∀ z ∈ Metric.closedBall p (ρ / 2), ‖deriv φ z‖ ≤ θ := by
  refine ⟨3 / 4, by norm_num, by norm_num, ?_⟩
  intro φ p ρ hρ hdiff hmap z hz
  set ρc : ℂ := (ρ : ℂ) with hρc_def
  set u₀ : ℂ := (z - p) / ρc with hu₀_def
  have hρc : ρc ≠ 0 := by rw [hρc_def]; exact_mod_cast hρ.ne'
  have norm_ρc : ‖ρc‖ = ρ := by rw [hρc_def]; simp [abs_of_pos hρ]
  have hz' : ‖z - p‖ ≤ ρ / 2 := by
    have := hz; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
  have hu₀ : ‖u₀‖ ≤ 1 / 2 := by
    rw [hu₀_def, norm_div, norm_ρc, div_le_iff₀ hρ]; linarith
  have hu₀_mem : u₀ ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hz_mem : z ∈ Metric.ball p ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  set g : ℂ → ℂ := fun u => (φ (p + ρc * u) - p) / ρc with hg_def
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    have ha : DifferentiableOn ℂ (fun u : ℂ => p + ρc * u) (Metric.ball 0 1) := by fun_prop
    have hma : Set.MapsTo (fun u : ℂ => p + ρc * u) (Metric.ball 0 1) (Metric.ball p ρ) := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_ρc]
      nlinarith [norm_nonneg u]
    have hcomp := hdiff.comp ha hma
    have := hcomp.sub_const p |>.div_const ρc
    simpa [g, Function.comp_def] using this
  have hg_maps : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 (1 / 2)) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have hau : p + ρc * u ∈ Metric.ball p ρ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_ρc]
      have hu1 : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
      nlinarith [norm_nonneg u]
    have hφu : ‖φ (p + ρc * u) - p‖ ≤ ρ / 2 := by
      have := hmap hau; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    rw [hg_def, norm_div, norm_ρc, div_le_iff₀ hρ]; linarith
  set G : ℂ → ℂ := fun u => (2 : ℂ) * g u with hG_def
  have hG_diff : DifferentiableOn ℂ G (Metric.ball 0 1) := by
    have := hg_diff.const_mul (2 : ℂ); simpa [G] using this
  have hG_maps : Set.MapsTo G (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have hgu : ‖g u‖ ≤ 1 / 2 := by
      have := hg_maps hu; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
    rw [hG_def, norm_mul]
    norm_num
    linarith
  have hG_deriv : deriv G u₀ = 2 * deriv g u₀ := by
    have : HasDerivAt g (deriv g u₀) u₀ :=
      (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hu₀_mem)).hasDerivAt
    simpa [G] using (this.const_mul (2 : ℂ)).deriv
  have hgu_deriv : deriv g u₀ = deriv φ z := by
    have hφ : HasDerivAt φ (deriv φ z) z :=
      (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz_mem)).hasDerivAt
    have hzsplit : p + ρc * u₀ = z := by
      rw [hu₀_def, mul_div_cancel₀ (z - p) hρc]; ring
    have hφ' : HasDerivAt φ (deriv φ z) (p + ρc * u₀) := by rw [hzsplit]; exact hφ
    have h1 : HasDerivAt (fun u : ℂ => p + ρc * u) ρc u₀ := by
      simpa using ((hasDerivAt_id u₀).const_mul ρc).const_add p
    have h2 : HasDerivAt (fun u : ℂ => φ (p + ρc * u)) (deriv φ z * ρc) u₀ := hφ'.comp u₀ h1
    have h3 : HasDerivAt g (deriv φ z * ρc / ρc) u₀ := by
      simpa [g] using (h2.sub_const p).div_const ρc
    rw [h3.deriv, mul_div_cancel_right₀ (deriv φ z) hρc]
  have hSP := SchwarzPick G u₀ hG_diff hG_maps hu₀_mem
  have h2 : (2 : ℝ) * ‖deriv g u₀‖ ≤ 1 / (1 - ‖u₀‖ ^ 2) := by
    have hh := hSP; rw [hG_deriv, norm_mul] at hh; simpa using hh
  have hbound : ‖deriv g u₀‖ ≤ 3 / 4 := by
    have hx : (3 : ℝ) / 4 ≤ 1 - ‖u₀‖ ^ 2 := by nlinarith [hu₀, norm_nonneg u₀, sq_nonneg ‖u₀‖]
    have hxpos : (0 : ℝ) < 1 - ‖u₀‖ ^ 2 := by linarith
    have h1 : 1 / (1 - ‖u₀‖ ^ 2) ≤ 3 / 2 := by
      rw [div_le_iff₀ hxpos]; nlinarith
    linarith
  simpa [hgu_deriv] using hbound

end Work.Dim.Branch
