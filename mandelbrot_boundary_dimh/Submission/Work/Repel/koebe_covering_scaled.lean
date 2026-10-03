import Mathlib
import Submission.Work.Repel.Koebe.koebe_transform
import Submission.Work.Repel.bieberbach_two_aux

/-!
# The sharp Koebe one-quarter theorem, rescaled to a disc

For a holomorphic injection `f` on a disc `ball c R`, the image contains the disc of radius
`R * ‖deriv f c‖ / 4` around `f c`.

This is the sharp Koebe one-quarter theorem, rescaled.  The normalised statement (every value
omitted by a normalised univalent `f` has modulus at least `1/4`) is
`Work.Repel.Koebe.omitted_norm_ge_quarter`, which derives it from Bieberbach's coefficient
inequality `‖f''(0)‖ ≤ 4` (`Work.Repel.Koebe.bieberbach_two`); the latter follows classically from
Grönwall's area theorem.  Here we only rescale: for a holomorphic injection `f` on `ball c R` the
map `ζ ↦ (f (c + R ζ) - f c) / (R * deriv f c)` is normalised univalent on the unit disc.
-/

namespace Work.Repel

open Metric

theorem koebe_covering_scaled {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hinj : Set.InjOn f (Metric.ball c R)) :
    Metric.ball (f c) (R / 4 * ‖deriv f c‖) ⊆ f '' Metric.ball c R := by
  by_cases hd : deriv f c = 0
  · rw [hd, norm_zero, mul_zero]
    intro w hw
    rw [Metric.mem_ball] at hw
    exact absurd hw (not_lt.mpr dist_nonneg)
  · set D : ℂ := (R : ℂ) * deriv f c with hD
    have hDne : D ≠ 0 := by
      rw [hD]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hR)) hd
    set F : ℂ → ℂ := fun ζ => (f (c + (R : ℂ) * ζ) - f c) / D with hF
    -- analyticity of `f` on the open disc (from `DifferentiableOn` on the closed disc)
    have hf_an : ∀ y ∈ Metric.ball c R, AnalyticAt ℂ f y := by
      intro y hy
      exact hf.analyticAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy)
        (fun x hx => Metric.ball_subset_closedBall hx))
    -- the shifted point stays in the disc
    have hmem : ∀ ζ : ℂ, ‖ζ‖ < 1 → c + (R : ℂ) * ζ ∈ Metric.ball c R := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
      nlinarith
    have hanF : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ F ζ := by
      intro ζ hζ
      have hζ' : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hinner : AnalyticAt ℂ (fun ζ : ℂ => c + (R : ℂ) * ζ) ζ := by fun_prop
      have hcomp : AnalyticAt ℂ (fun ζ : ℂ => f (c + (R : ℂ) * ζ)) ζ :=
        AnalyticAt.comp (x := ζ) (f := fun ζ : ℂ => c + (R : ℂ) * ζ) (g := f)
          (hf_an _ (hmem ζ hζ')) hinner
      rw [hF]
      exact (hcomp.sub (analyticAt_const (v := f c))).div_const (c := D)
    have hinjF : Set.InjOn F (Metric.ball (0 : ℂ) 1) := by
      intro ζ₁ hζ₁ ζ₂ hζ₂ heq
      have h1 : ‖ζ₁‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ₁
      have h2 : ‖ζ₂‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ₂
      have hfe : f (c + (R : ℂ) * ζ₁) = f (c + (R : ℂ) * ζ₂) := by
        have h := heq
        rw [hF] at h
        rw [div_left_inj' hDne] at h
        linear_combination h
      have hz := hinj (hmem ζ₁ h1) (hmem ζ₂ h2) hfe
      have h3 : (R : ℂ) * ζ₁ = (R : ℂ) * ζ₂ := by simpa using (add_left_cancel hz)
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hR)) h3
    have hF0 : F 0 = 0 := by rw [hF]; simp
    have hF1 : deriv F 0 = 1 := by
      have h1 : HasDerivAt (fun ζ : ℂ => c + (R : ℂ) * ζ) (R : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)).const_add c
      have h2 : HasDerivAt f (deriv f c) (c + (R : ℂ) * (0 : ℂ)) := by
        rw [mul_zero, add_zero]
        exact (hf_an c (Metric.mem_ball_self hR)).hasStrictDerivAt.hasDerivAt
      have h3 : HasDerivAt (fun ζ : ℂ => f (c + (R : ℂ) * ζ)) (deriv f c * (R : ℂ)) 0 :=
        h2.comp 0 h1
      have h4 : HasDerivAt F ((deriv f c * (R : ℂ)) / D) 0 := (h3.sub_const (f c)).div_const D
      rw [hF]
      rw [h4.deriv, hD]
      field_simp
      exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hR))
    have hquarter : ∀ w ∉ F '' Metric.ball (0 : ℂ) 1, (1 / 4 : ℝ) ≤ ‖w‖ := fun w hw =>
      Koebe.omitted_norm_ge_quarter hanF hinjF hF0 hF1
        (fun g han hinj h0 h1 => bieberbach_two_aux han hinj h0 h1) hw
    -- conclude
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw' : ‖(w - f c) / D‖ < 1 / 4 := by
      rw [norm_div, hD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < R * ‖deriv f c‖)]
      linarith
    by_contra hnot
    have hmemF : (w - f c) / D ∈ F '' Metric.ball (0 : ℂ) 1 := by
      by_contra hcon
      have := hquarter ((w - f c) / D) hcon
      linarith
    obtain ⟨ζ, hζ, hζeq⟩ := hmemF
    have hval : f (c + (R : ℂ) * ζ) = w := by
      have h := hζeq
      rw [hF] at h
      rw [div_left_inj' hDne] at h
      linear_combination h
    exact hnot ⟨c + (R : ℂ) * ζ, hmem ζ (by simpa [Metric.mem_ball, dist_eq_norm] using hζ), hval⟩

end Work.Repel
