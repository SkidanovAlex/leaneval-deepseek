/-
# The CONSTRUCTION area: the angular derivative of `Γ` and the first two terms of `N₀`

* `Gamma_deriv_id` (paper line 1400, the computation of Proposition `GammaRegularity`):
  `3 sin(2θ) ∂_θΓ = 2αΓ(cos²θ - 2sin²θ)`;
* `N0_first_two_eq` (tex 1398-1402): with `L₁₂(F_*) = 2α/(1+z)` and the exact form of `Γ`,
  the two `F_*`-quadratic terms of `N₀` collapse to the *quadratic-vanishing* function
  `8α² c2m(θ) z² Γ/(c(1+z)⁴)`, i.e.

  `(3/(2α))sin(2θ)L₁₂(F_*)∂_θF_* - (cos2θ-sin²θ)L₁₂(F_*)z∂_zF_* = 8α² c2m(θ) z² Γ/(c(1+z)⁴)`.

  (This is what makes `I^{N₀}_1 + I^{N₀}_2` bounded in `ℋ⁴` by `Cα²`: both terms vanish
  only *linearly* at `z = 0`, their combination vanishes quadratically.)
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- `3 sin(2θ) ∂_θΓ = 2αΓ(cos²θ - 2sin²θ)` for `θ ∈ [0,π/2]`: the differentiated form of
`Γ = (sinθcos²θ)^{α/3}` (paper line 1400).  At the endpoints both sides vanish (as
`Γ(0) = Γ(π/2) = 0` and `sin(2θ) = 0`), so the closed interval causes no problem. -/
theorem Gamma_deriv_id {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = 2 * α * Work.Spaces.Gam α θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases lt_or_eq_of_le hθ0 with h0 | h0
  · rcases lt_or_eq_of_le hθ1 with h1 | h1
    · -- interior of the interval
      have hsin : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
      have hu : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
      have hsincos : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        have := Real.sin_sq_add_cos_sq θ; linarith
      have hu' : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
          (Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
        (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
      have hGam : HasDerivAt (fun t : ℝ => Work.Spaces.Gam α t)
          ((Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)))
            * (α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)) θ := by
        have h := hu'.rpow_const (p := α / 3) (Or.inl (ne_of_gt hu))
        simpa [Work.Spaces.Gam] using h
      have hpow : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2)
          = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
        have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
              * (Real.sin θ * Real.cos θ ^ 2) ^ (1 : ℝ)
            = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
          rw [← Real.rpow_add hu, show α / 3 - 1 + 1 = α / 3 by ring]
        rwa [Real.rpow_one] at h1
      rw [hGam.deriv, s2, Real.sin_two_mul, Work.Spaces.Gam, ← hpow]
      ring_nf
      try nlinarith [Real.sin_sq_add_cos_sq θ]
    · -- θ = π/2
      subst h1
      have hL : s2 (Real.pi / 2) = 0 := by
        rw [s2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hR : Work.Spaces.Gam α (Real.pi / 2) = 0 := by
        rw [Work.Spaces.Gam, Real.sin_pi_div_two, Real.cos_pi_div_two, one_mul]
        rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
        exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 3))
      rw [hL, hR]
      ring
  · -- θ = 0
    subst h0
    have hL : s2 0 = 0 := by rw [s2, mul_zero, Real.sin_zero]
    have hR : Work.Spaces.Gam α 0 = 0 := by
      rw [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, one_pow, mul_one,
        Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < α / 3))]
    rw [hL, hR]
    ring

/-- The two `F_*`-quadratic terms of `\eqref{N0}` collapse (tex 1398-1402). -/
theorem N0_first_two_eq {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hΓ : 3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = 2 * α * Work.Spaces.Gam α θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :
    (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
  have hz' : (-1 : ℝ) < z := by linarith
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have ha : α ≠ 0 := ne_of_gt hα
  have h1 : (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      = (2 * α * z / (Work.Spaces.c α * (1 + z) ^ 3))
        * (3 * s2 θ * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ) := by
    rw [pth_Fstar_eq hα, L12_Fstar_eq hα hα1 hz, Work.FM.Fstar]
    field_simp
    try ring
  have h2 : c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 4 * α ^ 2 * c2m θ * z * (1 - z) * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
    rw [Dz_Fstar_eq hα hz', L12_Fstar_eq hα hα1 hz]
    field_simp
    try ring
  rw [h1, h2, hΓ]
  rw [c2m, Real.cos_two_mul]
  field_simp
  linear_combination (norm := ring_nf)
    (-4 * z * Work.Spaces.Gam α θ * (1 + z)) * Real.sin_sq_add_cos_sq θ

/-- `N0_first_two_eq` with the Γ-derivative identity supplied by `Gamma_deriv_id`. -/
theorem N0_first_two_eq' {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
      - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
      = 8 * α ^ 2 * c2m θ * z ^ 2 * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) :=
  N0_first_two_eq hα hα1 hz hθ (Gamma_deriv_id hα hθ)

end Work.Construction
