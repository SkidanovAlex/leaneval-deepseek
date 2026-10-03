import Mathlib
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.Gates

namespace Work.Pert.CoverHigh

open Metric Set Complex

/-!
# PERT · `cover_anchor`

Anchoring the (near-)integer translate of a point `w` inside the waist image `Φ '' (Qm ∩ Qp)`.

The two gates are `1/α`-periodic-ish and `Qm ∩ Qp` is the *waist*, so the image
`Φ '' (Qm ∩ Qp)` is very far from being all of `ℂ`; but it is dense in the horizontal direction in
the following sense: any point whose imaginary part matches the imaginary part of `Φ z₀` up to
`r/4 - 1/2` can be translated by an integer real amount into the quarter-ball covered by
`Φ '' closedBall z₀ r` (`Work.Pert.image_cover_centered`).

Concretely: if `closedBall z₀ ρ ⊆ Qm ∩ Qp`, `Φ` is within `1/2` of the identity on every ball of
radius `≥ R₁` contained in `Qm`, and `R₁ + 2 r + 1 ≤ ρ` (so that the disc of radius `r` sits well
inside `closedBall z₀ ρ`, with `ρ - r ≥ R₁`), then the derivative bound holds on `closedBall z₀ r`,
hence `ball (Φ z₀) (r/4) ⊆ Φ '' closedBall z₀ r`.  Choose the integer
`n = ⌊(Φ z₀).re - w.re + 1/2⌋` (nearest integer to the real displacement); then
`|(w.re + n) - (Φ z₀).re| ≤ 1/2`, while `|w.im - (Φ z₀).im| + 1/2 < r/4` gives
`(r/4)² - |w.im - (Φ z₀).im|² > 1/4`, so `w + n ∈ ball (Φ z₀) (r/4)`.
-/

theorem cover_anchor {Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {R₁ ρ r : ℝ} {z₀ w : ℂ}
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
      ‖deriv Φ z - 1‖ ≤ 1 / 2)
    (hdisc : Metric.closedBall z₀ ρ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hb : R₁ + 2 * r + 1 ≤ ρ)
    (hclose : |w.im - (Φ z₀).im| + 1 / 2 < r / 4) :
    ∃ n : ℤ, w + (n : ℂ) ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := by
  -- `ρ - r ≥ R₁`, so the radius `ρ - r` is a legal test radius for `hder`
  have hR : R₁ ≤ ρ - r := by linarith
  -- the disc of radius `ρ - r` around any point of `closedBall z₀ r` stays in `Qm`
  have hder' : ∀ z ∈ Metric.closedBall z₀ r, ‖deriv Φ z - 1‖ ≤ 1 / 2 := by
    intro z hz
    refine hder z (ρ - r) hR ?_
    intro z' hz'
    rw [Metric.mem_ball] at hz'
    have hzz0 : dist z z₀ ≤ r := by rwa [Metric.mem_closedBall] at hz
    have hdist : dist z' z₀ < ρ := by
      calc dist z' z₀ ≤ dist z' z + dist z z₀ := dist_triangle _ _ _
        _ < (ρ - r) + r := by linarith
        _ = ρ := by ring
    exact (hdisc (by rw [Metric.mem_closedBall]; exact hdist.le)).1
  -- hence `Φ` is differentiable on the disc
  have hdiff : ∀ z ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ z := by
    intro z hz
    refine differentiableAt_of_deriv_ne_zero ?_
    intro h0
    have h := hder' z hz
    rw [h0] at h
    norm_num at h
  -- the quarter-ball covering
  have hcov := Work.Pert.image_cover_centered hr hdiff hder'
  -- choose the nearest integer to the real displacement
  set t : ℝ := (Φ z₀).re - w.re with htdef
  refine ⟨⌊t + 1 / 2⌋, ?_⟩
  have hn_ub : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t ≤ 1 / 2 := by
    have := Int.floor_le (t + 1 / 2)
    linarith
  have hn_lb : -(1 / 2) ≤ ((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t := by
    have := Int.lt_floor_add_one (t + 1 / 2)
    linarith
  have hn_sq : (((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t) ^ 2 ≤ 1 / 4 := by
    have h : |((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t| ≤ 1 / 2 := abs_le.mpr ⟨hn_lb, hn_ub⟩
    calc (((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t) ^ 2
        = |((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t| ^ 2 := (sq_abs _).symm
      _ ≤ (1 / 2) ^ 2 := by gcongr
      _ = 1 / 4 := by norm_num
  -- `(r/4)² - (imaginary gap)² > 1/4`
  have hkey : (r / 4) ^ 2 - (w.im - (Φ z₀).im) ^ 2 > 1 / 4 := by
    have ha : r / 4 - |w.im - (Φ z₀).im| > 1 / 2 := by linarith [hclose]
    have hb' : r / 4 + |w.im - (Φ z₀).im| > 1 / 2 := by
      have := abs_nonneg (w.im - (Φ z₀).im); linarith
    have habs : (w.im - (Φ z₀).im) ^ 2 = |w.im - (Φ z₀).im| ^ 2 := (sq_abs _).symm
    rw [habs]
    nlinarith [ha, hb']
  have hmem_ball : w + ((⌊t + 1 / 2⌋ : ℤ) : ℂ) ∈ Metric.ball (Φ z₀) (r / 4) := by
    rw [Metric.mem_ball, dist_eq_norm]
    set v : ℂ := (w + ((⌊t + 1 / 2⌋ : ℤ) : ℂ)) - Φ z₀ with hvdef
    have hre : v.re = ((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t := by
      rw [hvdef, Complex.sub_re, Complex.add_re, Complex.intCast_re, htdef]; ring
    have him : v.im = w.im - (Φ z₀).im := by
      rw [hvdef, Complex.sub_im, Complex.add_im, Complex.intCast_im]; ring
    have hvsq : ‖v‖ ^ 2 = (((⌊t + 1 / 2⌋ : ℤ) : ℝ) - t) ^ 2 + (w.im - (Φ z₀).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have hlt : ‖v‖ ^ 2 < (r / 4) ^ 2 := by
      rw [hvsq]; linarith [hn_sq, hkey]
    have h1 : (0:ℝ) ≤ ‖v‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ r / 4 := by linarith [hr]
    rw [sq_lt_sq] at hlt
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at hlt
  obtain ⟨ζ, hζmem, hζeq⟩ := hcov hmem_ball
  exact ⟨ζ, hdisc (Metric.closedBall_subset_closedBall hrρ hζmem), hζeq⟩

end Work.Pert.CoverHigh
