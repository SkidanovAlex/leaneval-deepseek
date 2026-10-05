import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.RetractDefs

namespace Work.RPB1a.Caratheodory.Brouwer

/-- If the ray from `p` in direction `d` already reaches the unit sphere at parameter `1`
(i.e. `‖p + d‖ = 1`, as happens when `p + d` is a point of the sphere), then the outer root
`rayT p d` equals `1`; this is what makes the constructed retraction fix the sphere. -/
lemma rayT_eq_one {N : ℕ} (p d : EuclideanSpace ℝ (Fin N)) (hd : d ≠ 0) (hp : ‖p‖ ≤ 1)
    (hx : ‖p + d‖ = 1) : rayT p d = 1 := by
  -- `‖d‖² = 0` would force `d = 0`, contradicting `hd`; used to divide at the end.
  have hbne : ‖d‖ ^ 2 ≠ 0 := by
    have : 0 < ‖d‖ := norm_pos_iff.mpr hd; positivity
  -- Squaring the hypothesis `‖p + d‖ = 1`.
  have hx2 : ‖p + d‖ ^ 2 = 1 := by rw [hx]; norm_num
  -- Expanding `‖p + d‖²` turns the hypothesis into a linear relation on `⟪p, d⟫`.
  have hsq : ‖p‖ ^ 2 + 2 * inner ℝ p d + ‖d‖ ^ 2 = 1 := by
    rw [← norm_add_sq_real]; exact hx2
  -- The discriminant `⟪p,d⟫² + ‖d‖²(1 - ‖p‖²)` is a perfect square at the point where the
  -- ray already meets the sphere.
  have hkey : (inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2)
      = (‖d‖ ^ 2 + inner ℝ p d) ^ 2 := by
    have hs : inner ℝ p d = (1 - ‖p‖ ^ 2 - ‖d‖ ^ 2) / 2 := by linarith
    rw [hs]; ring
  -- In particular `‖d‖² + ⟪p,d⟫ ≥ 0`, so the square root is its own perfect square.
  have hbs : 0 ≤ ‖d‖ ^ 2 + inner ℝ p d := by
    have hs : inner ℝ p d = (1 - ‖p‖ ^ 2 - ‖d‖ ^ 2) / 2 := by linarith
    have ha1 : ‖p‖ ^ 2 ≤ 1 := by nlinarith [hp, norm_nonneg p]
    have hb0 : 0 ≤ ‖d‖ ^ 2 := by positivity
    rw [hs]; nlinarith
  unfold rayT
  rw [hkey, Real.sqrt_sq_eq_abs, abs_of_nonneg hbs]
  rw [show -(inner ℝ p d) + (‖d‖ ^ 2 + inner ℝ p d) = ‖d‖ ^ 2 by ring]
  exact div_self hbne

end Work.RPB1a.Caratheodory.Brouwer
