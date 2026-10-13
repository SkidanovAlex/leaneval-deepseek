import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem profile_abs_lower_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hsmall : Cg ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) :
    p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
      ≤ |Work.ConstructionInstance.profile p g 1 (Real.pi / 4)| := by
  -- The point `π/4` lies in the angular domain.
  have hpi4 : (Real.pi / 4) ∈ Work.Spaces.Iθ :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- Positivity of the normalisation constant `c p`.
  have hcpos : 0 < Work.Spaces.c p := by
    have := (Work.Spaces.c_bounds p hp hp1).1; linarith
  -- Nonnegativity of `Gam p (π/4)`.
  have hGam0 : 0 ≤ Work.Spaces.Gam p (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_nonneg (by
      have hs : 0 ≤ Real.sin (Real.pi / 4) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      positivity) _
  -- The right-hand side constant `A = p·Gam p (π/4)/(4 c p)` is nonnegative.
  have hA0 : 0 ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p) :=
    div_nonneg (mul_nonneg hp.le hGam0) (by positivity)
  -- The profile value at `z = 1` is exactly twice `A` (since `2·1/(1+1)² = 1/2`).
  have hF : Work.Construction.Fstar p 1 (Real.pi / 4)
      = 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) := by
    have hcne : Work.Spaces.c p ≠ 0 := ne_of_gt hcpos
    rw [Work.Construction.Fstar, Work.FM.Fstar]
    norm_num
    field_simp
    ring
  -- Unfold the (odd) profile at the nonnegative angle `π/4`.
  have hprof : profile p g 1 (Real.pi / 4)
      = Work.Construction.Fstar p 1 (Real.pi / 4) + g 1 (Real.pi / 4) := by
    rw [profile_of_nonneg (by positivity)]
  -- The bound on `g` transported to the point `(1, π/4)`.
  have hg : |g 1 (Real.pi / 4)| ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p) :=
    le_trans (hgbdd 1 (Real.pi / 4) (by norm_num) hpi4) hsmall
  rw [hprof, hF]
  -- Reverse triangle inequality: `|2A + g| ≥ |2A| - |g| = 2A - |g| ≥ A`.
  have key : |2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4)|
      ≥ 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        - |g 1 (Real.pi / 4)| := by
    have h := abs_add_le (2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4)) (-(g 1 (Real.pi / 4)))
    rw [abs_neg] at h
    have heq : 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4) + -(g 1 (Real.pi / 4))
        = 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) := by ring
    rw [heq, abs_of_nonneg (by linarith)] at h
    linarith
  linarith [key, hg, hA0]

end Work.ConstructionInstance
