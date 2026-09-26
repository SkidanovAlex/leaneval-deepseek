import Mathlib
import Submission.Work.Drive.Final.cornerLevelPiece_pathConnected

namespace Work.Drive.Final

open Set

/-- A small box version of the corner level piece: if `W 0 = 0`, `‖fderiv W‖ ≤ M` on the box and
the second directional derivative of `W` is `≤ c / 2 < 0`, then `W` is strictly decreasing in the
second variable, and positive on the whole spine `y = -d/2` of the box provided `M e < |c| d / 4`.
Hence the part of `{0 < W}` lying in the left half `x < 0` of the box is path connected. -/
theorem cornerLevelPieceDown (W : ℝ × ℝ → ℝ) {e d c M : ℝ}
    (he : 0 < e) (hd : 0 < d) (hc : c < 0) (hM : 0 < M) (hW0 : W 0 = 0)
    (heM : M * e < |c| * d / 4)
    (hdiff : ∀ ξ : ℝ × ℝ, ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d → DifferentiableAt ℝ W ξ)
    (hbound : ∀ ξ : ℝ × ℝ, ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d → ‖fderiv ℝ W ξ‖ ≤ M)
    (hmono : ∀ ξ : ℝ × ℝ, ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d → fderiv ℝ W ξ (0, 1) ≤ c / 2) :
    IsPathConnected {ξ : ℝ × ℝ | ξ ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d ∧ ξ.1 < 0 ∧ 0 < W ξ} := by
  -- Membership in the box, from membership of the two coordinates.
  have hbox : ∀ x y : ℝ, x ∈ Set.Ioo (-e) e → y ∈ Set.Ioo (-d) d →
      ((x, y) : ℝ × ℝ) ∈ Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d := fun x y hx hy => ⟨hx, hy⟩
  have hd2 : (-d / 2 : ℝ) ∈ Set.Ioo (-d) d := ⟨by linarith, by linarith⟩
  have h0e : (0 : ℝ) ∈ Set.Ioo (-e) e := ⟨by linarith, by linarith⟩
  have h0d : (0 : ℝ) ∈ Set.Ioo (-d) d := ⟨by linarith, by linarith⟩
  -- (1) The derivative of a vertical section of `W` is the directional derivative `(0, 1)`.
  have hderiv_eq : ∀ x y : ℝ, x ∈ Set.Ioo (-e) e → y ∈ Set.Ioo (-d) d →
      deriv (fun y' : ℝ => W (x, y')) y = fderiv ℝ W (x, y) (0, 1) := by
    intro x y hx hy
    have hc' : HasDerivAt (fun y' : ℝ => ((x, y') : ℝ × ℝ)) (0, 1) y := by
      simpa using (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    have h := fderiv_comp_deriv (𝕜 := ℝ) (x := y)
      (l := W) (f := fun y' : ℝ => ((x, y') : ℝ × ℝ))
      (hdiff (x, y) (hbox x y hx hy)) hc'.differentiableAt
    simpa [Function.comp_def, hc'.deriv] using h
  -- (2) Vertical monotonicity, with the quantitative slope bound `c / 2`.
  have hvert_le : ∀ (x y₁ y₂ : ℝ), x ∈ Set.Ioo (-e) e → y₁ ∈ Set.Ioo (-d) d →
      y₂ ∈ Set.Ioo (-d) d → y₁ ≤ y₂ → W (x, y₂) - W (x, y₁) ≤ (c / 2) * (y₂ - y₁) := by
    intro x y₁ y₂ hx hy₁ hy₂ hy12
    have hdiffOn : DifferentiableOn ℝ (fun y : ℝ => W (x, y)) (interior (Set.Ioo (-d) d)) := by
      rw [interior_Ioo]
      intro y hy
      have h1 : DifferentiableAt ℝ (fun y' : ℝ => ((x, y') : ℝ × ℝ)) y :=
        (hasFDerivAt_prodMk_right x y).differentiableAt
      exact ((hdiff (x, y) (hbox x y hx hy)).comp y h1).differentiableWithinAt
    have hcont : ContinuousOn (fun y : ℝ => W (x, y)) (Set.Ioo (-d) d) := by
      simpa only [interior_Ioo] using hdiffOn.continuousOn
    have hslope : ∀ y ∈ interior (Set.Ioo (-d) d), deriv (fun y' : ℝ => W (x, y')) y ≤ c / 2 := by
      intro y hy
      rw [interior_Ioo] at hy
      rw [hderiv_eq x y hx hy]
      exact hmono (x, y) (hbox x y hx hy)
    exact (convex_Ioo (-d) d).image_sub_le_mul_sub_of_deriv_le hcont hdiffOn hslope
      y₁ hy₁ y₂ hy₂ hy12
  -- (3) `W` is positive on the horizontal spine `y = -d/2`.
  have hx_est : ∀ x ∈ Set.Ioo (-e) e, |W (x, -d / 2) - W (0, -d / 2)| ≤ M * e := by
    intro x hx
    have hB : Convex ℝ (Set.Ioo (-e) e ×ˢ Set.Ioo (-d) d) :=
      (convex_Ioo (-e) e).prod (convex_Ioo (-d) d)
    have h1 : ‖W (x, -d / 2) - W (0, -d / 2)‖ ≤ M * ‖(x, -d / 2) - (0, -d / 2)‖ :=
      hB.norm_image_sub_le_of_norm_fderiv_le (fun ξ hξ => hdiff ξ hξ)
        (fun ξ hξ => hbound ξ hξ) (hbox 0 (-d / 2) h0e hd2) (hbox x (-d / 2) hx hd2)
    have h2 : ‖((x, -d / 2) - (0, -d / 2) : ℝ × ℝ)‖ = |x| := by
      have h3 : ((x, -d / 2) - (0, -d / 2) : ℝ × ℝ) = (x, 0) := by simp
      rw [h3]
      rw [Prod.norm_def]
      simp
    rw [h2, Real.norm_eq_abs] at h1
    have hxe : |x| ≤ e := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
    calc |W (x, -d / 2) - W (0, -d / 2)| ≤ M * |x| := h1
      _ ≤ M * e := mul_le_mul_of_nonneg_left hxe (le_of_lt hM)
  have h0down : |c| * d / 4 ≤ W (0, -d / 2) - W (0, 0) := by
    have h := hvert_le 0 (-d / 2) 0 h0e hd2 h0d (by linarith)
    have h' : W (0, 0) - W (0, -d / 2) ≤ c * d / 4 := by
      calc W (0, 0) - W (0, -d / 2) ≤ (c / 2) * (0 - (-d / 2)) := h
        _ = c * d / 4 := by ring
    rw [abs_of_neg hc]
    linarith
  have hspine : ∀ x ∈ Set.Ioo (-e) e, 0 < W (x, -d / 2) := by
    intro x hx
    have hb := (abs_le.mp (hx_est x hx)).1
    have h00 : W (0, 0) = 0 := by
      have hh : ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) := rfl
      rw [hh]
      exact hW0
    linarith
  -- (4) Downward monotonicity in the second variable, in the form needed by the consumer.
  have hdown_mono : ∀ x y y' : ℝ, x ∈ Set.Ioo (-e) e → y' ∈ Set.Ioo (-d) y →
      y ∈ Set.Ioo (-d) d → 0 < W (x, y) → 0 < W (x, y') := by
    intro x y y' hx hy' hy hypos
    have hy'd : y' ∈ Set.Ioo (-d) d := ⟨hy'.1, lt_trans hy'.2 hy.2⟩
    have h := hvert_le x y' y hx hy'd hy (le_of_lt hy'.2)
    have hneg : (c / 2) * (y - y') < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith [hy'.2])
    linarith
  exact cornerLevelPiece_pathConnected W he hd hdown_mono hspine

end Work.Drive.Final
