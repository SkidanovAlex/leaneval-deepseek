import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.Setup
import Submission.Work.Pert.deriv_psi0_close

namespace Work.Pert.Ksub2

open Complex

/-- A point whose translate `w + ξ` has negative real part lies in the repelling sector `QLeft ξ`:
`arg (w + ξ)` then differs from the positive real axis, so `|arg (w + ξ)| > π/2 > π/3`.

(The sector only involves the argument of `w + ξ`, and `|arg z| ≤ π/2 ↔ 0 ≤ z.re` is
`Complex.abs_arg_le_pi_div_two_iff`.) -/
private lemma QLeft_of_re_neg {ξ : ℝ} {w : ℂ} (h : (w + (ξ : ℂ)).re < 0) :
    w ∈ MandelDim.QLeft ξ := by
  rw [MandelDim.QLeft, Set.mem_ofPred_eq]
  have hnot : ¬ (|Complex.arg (w + (ξ : ℂ))| ≤ Real.pi / 2) := by
    intro hle
    have := Complex.abs_arg_le_pi_div_two_iff.mp hle
    linarith
  have h2 : Real.pi / 2 < |Complex.arg (w + (ξ : ℂ))| := lt_of_not_ge hnot
  linarith [Real.pi_pos]

/-- **`Work.Pert.Ksub2.anchor_scale_deriv`.**  Shishikura's Appendix A.4 derivative estimate in the
form used by the level-`K` perturbation argument: at scale `M` the whole ball
`ball (-M) (M/4)` — a disc of fixed shape and depth `3M/4..5M/4` on the left of the origin — is
contained in the sector `QLeft ξ₀` together with the discs `ball u (‖u‖/10)` used by the
Cauchy estimate, so the global statement `Work.Pert.deriv_psi0_close` applies verbatim. -/
theorem anchor_scale_deriv {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      ∀ u ∈ Metric.ball ((-M : ℝ) : ℂ) (M / 4),
        ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2 := by
  obtain ⟨R₁, hR₁pos, hR₁⟩ := deriv_psi0_close d
  refine ⟨max (2 * R₁) (8 * d.ξ₀ + 20), ?_, ?_⟩
  · have : (0 : ℝ) < 2 * R₁ := by linarith
    linarith [le_max_left (2 * R₁) (8 * d.ξ₀ + 20)]
  · intro M hM u hu
    have hM1 : 2 * R₁ ≤ M := le_trans (le_max_left _ _) hM
    have hM2 : 8 * d.ξ₀ + 20 ≤ M := le_trans (le_max_right _ _) hM
    have hξpos := d.ξ₀_pos
    have hMpos : 0 < M := by linarith
    -- distance from the centre, in the form `‖u + M‖ < M/4`
    have hdist : ‖u - ((-M : ℝ) : ℂ)‖ < M / 4 := by
      have := Metric.mem_ball.mp hu
      rwa [dist_eq_norm] at this
    have hdist' : ‖u + (M : ℂ)‖ < M / 4 := by
      simpa [Complex.ofReal_neg, sub_neg_eq_add] using hdist
    have hnormM : ‖(M : ℂ)‖ = M := by simp [abs_of_pos hMpos]
    -- real part and norm of `u`
    have hre_u : u.re < -(3 * M / 4) := by
      have h1 : |(u + (M : ℂ)).re| ≤ ‖u + (M : ℂ)‖ := Complex.abs_re_le_norm _
      have h2 : (u + (M : ℂ)).re = u.re + M := by simp
      rw [h2] at h1
      have := le_trans (le_abs_self _) h1
      linarith
    have hnu_low : 3 * M / 4 ≤ ‖u‖ := by
      have h1 : M ≤ ‖u + (M : ℂ)‖ + ‖u‖ := by
        have h := norm_sub_le (u + (M : ℂ)) u
        have h2 : u + (M : ℂ) - u = (M : ℂ) := by ring
        rw [h2] at h
        rwa [hnormM] at h
      linarith
    have hnu_up : ‖u‖ ≤ 5 * M / 4 := by
      have h1 : ‖u‖ ≤ ‖u + (M : ℂ)‖ + M := by
        have h := norm_add_le (u + (M : ℂ)) (-(M : ℂ))
        have h2 : u + (M : ℂ) + -(M : ℂ) = u := by ring
        rw [h2] at h
        rwa [norm_neg, hnormM] at h
      linarith
    -- the discs used by the Cauchy estimate still lie in the sector
    have hQs : ∀ v ∈ Metric.ball u (‖u‖ / 10), v ∈ MandelDim.QLeft d.ξ₀ := by
      intro v hv
      apply QLeft_of_re_neg
      have hvdist : ‖v - u‖ < ‖u‖ / 10 := by
        have := Metric.mem_ball.mp hv
        rwa [dist_eq_norm] at this
      have hvre : v.re < -(5 * M / 8) := by
        have h1 : (v - u).re = v.re - u.re := Complex.sub_re v u
        have h2 : |(v - u).re| ≤ ‖v - u‖ := Complex.abs_re_le_norm _
        have h3 : (v - u).re ≤ ‖v - u‖ := le_trans (le_abs_self _) h2
        linarith
      have hsum : (v + (d.ξ₀ : ℂ)).re = v.re + d.ξ₀ := by simp
      rw [hsum]
      linarith
    have hQu : u ∈ MandelDim.QLeft d.ξ₀ := by
      apply QLeft_of_re_neg
      have hsum : (u + (d.ξ₀ : ℂ)).re = u.re + d.ξ₀ := by simp
      rw [hsum]; linarith
    have hRu : R₁ ≤ ‖u‖ := by linarith
    exact hR₁ u hQu hRu hQs

end Work.Pert.Ksub2
