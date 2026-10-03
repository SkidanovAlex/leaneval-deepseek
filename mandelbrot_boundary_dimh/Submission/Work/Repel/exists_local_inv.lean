import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.chain_v9_geom

/-!
# Local inverse of the perturbed Fatou coordinate

`Work.Repel.exists_local_inv`: the perturbed Fatou coordinate `φ_f = P.φ` of `PertData` is
holomorphic on the open set `P.Dφ` and has non-vanishing derivative at every point of the two
small discs `Dsm η`, `Dsm (-η)` (this is the content of the field `φ_star_deriv`: the derivative
of `τ₀ ∘ φ_f` is bounded below by `1/2` there, and `τ₀(z) = -1/z` has non-vanishing derivative
away from `0`).  Hence `φ_f` is a local biholomorphism at every `w ∈ Dsm η ∪ Dsm (-η)`, and the
inverse-function theorem for analytic functions (`AnalyticAt.analyticAt_localInverse`) supplies an
analytic local inverse `W` with `W (φ_f w) = w` and `φ_f (W ζ) = ζ` for `ζ` near `φ_f w`.

The only point requiring care is that `φ_f w ≠ 0` (so that the chain rule applies to `τ₀ ∘ φ_f`):
this follows from `φ_star_close`, `‖τ₀ (φ_f w) - w‖ ≤ |η|/40`, together with the elementary bound
`3η/4 ≤ ‖w‖` for `w ∈ Dsm η ∪ Dsm (-η)`, `η > 0`.
-/

namespace Work.Repel

open MandelDim

/-- Points of `Dsm η ∪ Dsm (-η)` (for `η > 0`) are at distance at least `3η/4` from the origin. -/
lemma norm_ge_of_mem_Dsm_union {η : ℝ} (hη : 0 < η) {w : ℂ}
    (hw : w ∈ Dsm η ∪ Dsm (-η)) : 3 * η / 4 ≤ ‖w‖ := by
  rcases hw with hw | hw
  · have hd : ‖w - Complex.I * η‖ ≤ η / 4 := by
      have hh := (Metric.mem_closedBall.mp hw)
      rwa [dist_eq_norm, abs_of_pos hη] at hh
    have him : w.im - η = (w - Complex.I * η).im := by simp
    have h1 : |w.im - η| ≤ η / 4 := by
      rw [him]; exact le_trans (Complex.abs_im_le_norm _) hd
    have h2 : 3 * η / 4 ≤ w.im := by
      have := (abs_le.mp h1).1
      linarith
    have h3 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [abs_of_nonneg (by linarith : 0 ≤ w.im)] at h3
    linarith
  · have hd : ‖w - Complex.I * (-η)‖ ≤ η / 4 := by
      have hh := (Metric.mem_closedBall.mp hw)
      rw [dist_eq_norm, abs_neg, abs_of_pos hη, Complex.ofReal_neg] at hh
      exact hh
    have him : w.im + η = (w - Complex.I * (-η)).im := by simp
    have h1 : |w.im + η| ≤ η / 4 := by
      rw [him]; exact le_trans (Complex.abs_im_le_norm _) hd
    have h2 : w.im ≤ -3 * η / 4 := by
      have := (abs_le.mp h1).2
      linarith
    have h3 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [abs_of_neg (by linarith : w.im < 0)] at h3
    linarith

/-- The derivative of `φ_f` does not vanish on `Dsm η ∪ Dsm (-η)`. -/
lemma deriv_phi_ne_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ) (hη : 0 < η) {w : ℂ}
    (hw : w ∈ Dsm η ∪ Dsm (-η)) : deriv P.φ w ≠ 0 := by
  have hwnorm : 3 * η / 4 ≤ ‖w‖ := norm_ge_of_mem_Dsm_union hη hw
  have hη40 : η / 40 < 3 * η / 4 := by linarith
  -- `φ_f w ≠ 0`, so that `τ₀` is differentiable at `φ_f w`
  have htau_ne : MandelDim.tau0 (P.φ w) ≠ 0 := by
    intro hzero
    have hclose := P.φ_star_close w hw
    have : ‖w‖ ≤ η / 40 := by
      rw [hzero, zero_sub, norm_neg, abs_of_pos hη] at hclose
      exact hclose
    linarith
  have hφw_ne : P.φ w ≠ 0 := by
    intro h
    exact htau_ne (by simp [MandelDim.tau0, h])
  have hφmem : w ∈ P.Dφ := P.D_sub hw
  have hφd : DifferentiableAt ℂ P.φ w := P.φ_holo.differentiableAt (P.Dφ_open.mem_nhds hφmem)
  have hτd : DifferentiableAt ℂ MandelDim.tau0 (P.φ w) := by
    show DifferentiableAt ℂ (fun z : ℂ => -1 / z) (P.φ w)
    fun_prop (disch := assumption)
  have hcr : deriv (fun u => MandelDim.tau0 (P.φ u)) w
      = deriv MandelDim.tau0 (P.φ w) * deriv P.φ w := by
    have h := deriv_comp (𝕜 := ℂ) w (h₂ := MandelDim.tau0) (h := P.φ) hτd hφd
    rw [Function.comp_def] at h
    exact h
  intro hzero
  have hne : ‖deriv (fun u => MandelDim.tau0 (P.φ u)) w‖ ≠ 0 :=
    ne_of_gt (by linarith [(P.φ_star_deriv w hw).1])
  exact hne (by rw [hcr, hzero, mul_zero, norm_zero])

theorem exists_local_inv {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ) (hη : 0 < η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η)) :
    ∃ W : ℂ → ℂ, W (P.φ w) = w ∧ AnalyticAt ℂ W (P.φ w) ∧
      Filter.Eventually (fun ζ => P.φ (W ζ) = ζ) (nhds (P.φ w)) := by
  have hφmem : w ∈ P.Dφ := P.D_sub hw
  have hφa : AnalyticAt ℂ P.φ w := P.φ_holo.analyticAt (P.Dφ_open.mem_nhds hφmem)
  have hderiv_ne : deriv P.φ w ≠ 0 := deriv_phi_ne_zero P hη hw
  refine ⟨HasStrictDerivAt.localInverse P.φ (deriv P.φ w) w hφa.hasStrictDerivAt hderiv_ne,
    ?_, ?_, ?_⟩
  · exact HasStrictFDerivAt.localInverse_apply_image _
  · exact hφa.analyticAt_localInverse hderiv_ne
  · exact HasStrictDerivAt.eventually_right_inverse _ _

end Work.Repel
