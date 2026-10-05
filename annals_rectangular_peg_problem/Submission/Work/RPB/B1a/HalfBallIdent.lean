import Mathlib
import Submission.Work.RPB.B1a.HalfBallDefs
import Submission.Work.RPB.B1a.HalfBallRegion

/-!
# `Work.RPB.B1a`: identification of the half-balls with the sheared half-disk

`halfBallUp g w ρ` and `halfBallDn g w ρ` are the two local sides of the straightening chart of a
loop with `g 0 = 0` and `deriv g 0 = w ≠ 0`.  Writing `h x = I * g x / w` (`hArg g w x`), with real
and imaginary parts `hRe g w`, `hIm g w`, the identity

`‖g x + y (I w)‖ ^ 2 = ‖w‖^2 * ((y - hRe g w x)^2 + (hIm g w x)^2)`

shows that `halfBallUp g w ρ` is exactly the sheared half-disk `shearRegion (hRe g w) (hIm g w) r`
with `r = ρ / ‖w‖`, and that the lower half-ball is the reflection in the first coordinate axis of
the sheared half-disk with `P`, `Q` negated.

Also here: the Lipschitz bound on `deriv g` near `0` that `ContDiff ℝ 2 g` provides.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Complex Set Metric

/-- **A `C^2` function has a Lipschitz derivative near the origin.**  If `g` is `C^2` and
`HasDerivAt g w 0`, then on some closed interval `[-δ, δ]` the derivative of `g` is bounded by
`K * |x|`. -/
theorem exists_deriv_lipschitz_bound (g : ℝ → ℂ) (w : ℂ) (hgd : HasDerivAt g w 0)
    (hg : ContDiff ℝ 2 g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| ≤ δ → ‖deriv g x - w‖ ≤ K * |x| := by
  obtain ⟨K, t, ht, hLip⟩ := (hg.deriv'.contDiffAt (x := 0)).exists_lipschitzOnWith
  obtain ⟨d, hdpos, hdsub⟩ := Metric.mem_nhds_iff.mp ht
  have hw : deriv g 0 = w := hgd.deriv
  refine ⟨(K : ℝ), K.coe_nonneg, d / 2, by positivity, ?_⟩
  intro x hx
  have hxt : x ∈ t := hdsub (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith [abs_nonneg x])
  have h0t : (0 : ℝ) ∈ t := hdsub (by simp [hdpos])
  have h1 := hLip.dist_le_mul x hxt 0 h0t
  rw [hw] at h1
  simpa [dist_eq_norm, Real.dist_eq, sub_zero] using h1

/-- The straightening identity: `g x + y (I w) = I w * (y - h x)` with `h = hArg g w`. -/
lemma hArg_identity (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) (x y : ℝ) :
    g x + (y : ℂ) * (Complex.I * w) = Complex.I * w * ((y : ℂ) - hArg g w x) := by
  have hII : ∀ z : ℂ, Complex.I * (Complex.I * z) = -z := fun z => by
    rw [← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]
  rw [hArg]
  field_simp
  rw [mul_sub, mul_comm (g x) Complex.I, hII]
  ring

/-- **The norm-squared identity.** `‖g x + y (I w)‖ ^ 2 = ‖w‖^2 ( (y - P x)^2 + (Q x)^2 )` where
`P = hRe g w` and `Q = hIm g w`. -/
lemma norm_sq_straighten (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) (x y : ℝ) :
    ‖g x + (y : ℂ) * (Complex.I * w)‖ ^ 2 =
      ‖w‖ ^ 2 * ((y - hRe g w x) ^ 2 + (hIm g w x) ^ 2) := by
  rw [hArg_identity g w hw x y]
  have hIw : ‖Complex.I * w‖ = ‖w‖ := by rw [Complex.norm_mul, Complex.norm_I, one_mul]
  rw [Complex.norm_mul, hIw, mul_pow]
  have hz : ‖(y : ℂ) - hArg g w x‖ ^ 2 = (y - hRe g w x) ^ 2 + (hIm g w x) ^ 2 := by
    simp only [hRe, hIm, hArg, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hz]

/-- **The straightening inequality.**  For `ρ > 0` and `w ≠ 0`,
`‖g x + y (I w)‖ < ρ` is exactly the sheared-disk inequality with `r = ρ / ‖w‖`. -/
lemma straighten_lt_iff (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (x y : ℝ) :
    ‖g x + (y : ℂ) * (Complex.I * w)‖ < ρ ↔
      (y - hRe g w x) ^ 2 + (hIm g w x) ^ 2 < (ρ / ‖w‖) ^ 2 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  constructor
  · intro hc
    have h1 : ‖g x + (y : ℂ) * (Complex.I * w)‖ ^ 2 < ρ ^ 2 :=
      pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
    rw [norm_sq_straighten g w hw x y] at h1
    rw [div_pow, lt_div_iff₀ (by positivity)]
    nlinarith [h1]
  · intro hW
    rw [div_pow] at hW
    have h2 : ‖w‖ ^ 2 * ((y - hRe g w x) ^ 2 + (hIm g w x) ^ 2) < ρ ^ 2 := by
      have h3 := (lt_div_iff₀ (show (0 : ℝ) < ‖w‖ ^ 2 by positivity)).mp hW
      nlinarith [h3]
    rw [← norm_sq_straighten g w hw x y] at h2
    nlinarith [norm_nonneg (g x + (y : ℂ) * (Complex.I * w))]

/-- The second coordinate of the straightening ball does not change under the reflection
`(x, y) ↦ (x, -y)`. -/
lemma norm_swap_snd (p : ℝ × ℝ) : ‖(p.1, -p.2)‖ = ‖p‖ := by
  rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_neg]

/-- Rescaling the ball radius: `2 ρ / ‖w‖ = 2 * (ρ / ‖w‖)`. -/
lemma ball_radius_eq (ρ : ℝ) (w : ℂ) :
    Metric.ball (0 : ℝ × ℝ) (2 * ρ / ‖w‖) = Metric.ball 0 (2 * (ρ / ‖w‖)) := by
  rw [mul_div_assoc]

/-- **The upper half-ball is a sheared half-disk.** -/
theorem halfBallUp_eq_shearRegion (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    halfBallUp g w ρ = shearRegion (hRe g w) (hIm g w) (ρ / ‖w‖) := by
  ext p
  rw [halfBallUp, shearRegion, ball_radius_eq, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_setOf_eq, straighten_lt_iff g w hw hρ p.1 p.2, and_assoc]

/-- **The lower half-ball is a reflected sheared half-disk.**  Reflecting in the first coordinate
axis turns the lower half-ball into the upper one with `P`, `Q` negated. -/
theorem halfBallDn_eq_image_shearRegion (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) :
    halfBallDn g w ρ = (fun p : ℝ × ℝ => (p.1, -p.2)) ''
      shearRegion (fun x => -hRe g w x) (fun x => -hIm g w x) (ρ / ‖w‖) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    rw [halfBallDn, ball_radius_eq, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
    obtain ⟨⟨hy, hc⟩, hb⟩ := hp
    have hS : (p.1, -p.2) ∈ shearRegion (fun x => -hRe g w x) (fun x => -hIm g w x)
        (ρ / ‖w‖) := by
      rw [shearRegion, Set.mem_setOf_eq]
      change 0 < -p.2 ∧ (-p.2 - -hRe g w p.1) ^ 2 + (-hIm g w p.1) ^ 2 < (ρ / ‖w‖) ^ 2 ∧
        (p.1, -p.2) ∈ Metric.ball (0 : ℝ × ℝ) (2 * (ρ / ‖w‖))
      refine ⟨by linarith, ?_, ?_⟩
      · have hW := (straighten_lt_iff g w hw hρ p.1 p.2).mp hc
        have h3 : (-p.2 - -hRe g w p.1) ^ 2 + (-hIm g w p.1) ^ 2 =
            (p.2 - hRe g w p.1) ^ 2 + (hIm g w p.1) ^ 2 := by ring
        rw [h3]
        exact hW
      · rw [Metric.mem_ball, dist_zero_right] at hb ⊢
        rwa [norm_swap_snd]
    rw [Set.mem_image]
    exact ⟨(p.1, -p.2), hS, by simp⟩
  · rintro p ⟨q, hq, hqr⟩
    rw [← hqr]
    rw [shearRegion, Set.mem_setOf_eq] at hq
    change 0 < q.2 ∧ (q.2 - -hRe g w q.1) ^ 2 + (-hIm g w q.1) ^ 2 < (ρ / ‖w‖) ^ 2 ∧
      q ∈ Metric.ball (0 : ℝ × ℝ) (2 * (ρ / ‖w‖)) at hq
    obtain ⟨hqa, hqb, hqc⟩ := hq
    rw [halfBallDn, ball_radius_eq, Set.mem_inter_iff, Set.mem_setOf_eq]
    refine ⟨⟨by linarith, ?_⟩, ?_⟩
    · refine (straighten_lt_iff g w hw hρ q.1 (-q.2)).mpr ?_
      have h3 : (-q.2 - hRe g w q.1) ^ 2 + (hIm g w q.1) ^ 2 =
          (q.2 - -hRe g w q.1) ^ 2 + (-hIm g w q.1) ^ 2 := by ring
      rw [h3]
      exact hqb
    · rw [Metric.mem_ball, dist_zero_right] at hqc ⊢
      rwa [norm_swap_snd]

end Work.RPB.B1a
