import Mathlib

namespace Work.Drive.PushDisc

open scoped Topology
open Filter

/-- If `f` has a strictly positive derivative at `x₀`, then `f` strictly increases on a
right-neighbourhood of `x₀`. -/
private lemma exists_lt_of_hasDerivAt_pos_right {f : ℝ → ℝ} {x₀ c : ℝ}
    (h : HasDerivAt f c x₀) (hc : 0 < c) :
    ∃ ε > 0, ∀ y, x₀ < y → y < x₀ + ε → f x₀ < f y := by
  have htend : Tendsto (fun t : ℝ => t⁻¹ * (f (x₀ + t) - f x₀)) (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 c) := by
    have h' := h.tendsto_slope_zero_right
    simpa [smul_eq_mul] using h'
  have hev : ∀ᶠ t in 𝓝[Set.Ioi 0] (0:ℝ), c / 2 < t⁻¹ * (f (x₀ + t) - f x₀) :=
    (tendsto_order.1 htend).1 (c / 2) (by linarith)
  obtain ⟨ε, hε, hε'⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hev
  simp only [Set.mem_Ioo] at hε'
  refine ⟨ε, hε, fun y hy1 hy2 => ?_⟩
  have ht1 : 0 < y - x₀ := sub_pos.mpr hy1
  have ht2 : y - x₀ < ε := by linarith
  have h2 := hε' ⟨ht1, ht2⟩
  have hy : x₀ + (y - x₀) = y := by ring
  rw [hy] at h2
  have h3 : 0 < (y - x₀)⁻¹ := inv_pos.mpr ht1
  have h4 : 0 < f y - f x₀ :=
    pos_of_mul_pos_right (by linarith : 0 < (y - x₀)⁻¹ * (f y - f x₀)) (le_of_lt h3)
  linarith

/-- If `f` has a strictly negative derivative at `x₀`, then `f` strictly decreases on a
right-neighbourhood of `x₀`. -/
private lemma exists_gt_of_hasDerivAt_neg_right {f : ℝ → ℝ} {x₀ c : ℝ}
    (h : HasDerivAt f c x₀) (hc : c < 0) :
    ∃ ε > 0, ∀ y, x₀ < y → y < x₀ + ε → f y < f x₀ := by
  obtain ⟨ε, hε, hε'⟩ :=
    exists_lt_of_hasDerivAt_pos_right (f := fun y => -f y) (x₀ := x₀) (c := -c) h.neg (by linarith)
  exact ⟨ε, hε, fun y hy1 hy2 => by simpa using hε' y hy1 hy2⟩

theorem coreHeightNegNear (w : ℝ → ℝ) (a b : ℝ)
    (hm1 : w (-1) = 0) (hm1' : HasDerivAt w a (-1)) (ha : 0 < a)
    (h1 : w 1 = 0) (h1' : HasDerivAt w b 1) (hb : b < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 1 < |x| → |x| < 1 + δ → w x < 0 := by
  -- right of `1`: the derivative is negative there
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := exists_gt_of_hasDerivAt_neg_right h1' hb
  -- left of `-1`: reflect in the origin, where the derivative is `-a < 0`
  have hg : HasDerivAt (fun y : ℝ => w (-y)) (-a) 1 := by
    have hneg : HasDerivAt (fun y : ℝ => -y) (-1) (1 : ℝ) := hasDerivAt_neg 1
    exact (hm1'.comp 1 hneg).congr_deriv (by ring)
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := exists_gt_of_hasDerivAt_neg_right hg (by linarith)
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun x hx1 hx2 => ?_⟩
  rw [lt_abs] at hx1
  rw [abs_lt] at hx2
  rcases hx1 with hx1 | hx1
  · have hh : w x < w 1 := hε₁ x hx1 (by linarith [hx2.2, min_le_left ε₁ ε₂])
    rwa [h1] at hh
  · have hlt : -x < 1 + ε₂ := by linarith [hx2.1, min_le_right ε₁ ε₂]
    have hh := hε₂ (-x) hx1 hlt
    rw [hm1] at hh
    simpa using hh

end Work.Drive.PushDisc
