import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# The normalised gradient field lowers the level at unit speed

For a smooth function `g` on `ℝ³` and a diffeomorphism `ψ`, the pull-back
`G = pullback ψ g = g ∘ param ψ` of `g` to the parameter plane of the surface
`F = ψ(standard torus)` has, at every parameter `p` where its derivative does not vanish, a
derivative with the following property: the *normalised gradient field* of the chapter,

`normalisedGradField ψ g p = -((∂₁G)² + (∂₂G)²)⁻¹ • (∂₁G, ∂₂G)`

is a descent direction of unit speed, i.e. `dG_p(normalisedGradField ψ g p) = -1`.

Here `∂₁G = partialD₁ ψ g p` and `∂₂G = partialD₂ ψ g p` are the two coordinate derivatives of `G`,
i.e. the values of the (linear) derivative of `G` at `p` on the coordinate directions `(1,0)` and
`(0,1)` of the parameter plane.  The derivative `L = fderiv ℝ G p` is a continuous linear functional
on `ℝ × ℝ`, so `L (x,y) = x * ∂₁G + y * ∂₂G` for all `(x,y)`; consequently, when `L ≠ 0` the
number `(∂₁G)² + (∂₂G)²` is nonzero and the computation below is a two-line calculation.

This is the analytic fact making `normalisedGradField` a flow field which decreases the level of
`G` at speed one; it is consumed by the construction of the normalised gradient flow in the
parameter plane.
-/

namespace Work.Smooth.Morse.Flow

open LeanEval.KnotTheory.PardonDistortion

/-- A continuous linear functional on the parameter plane is determined by its two coordinate
derivatives: `L (x,y) = x * L(1,0) + y * L(0,1)`. -/
theorem continuousLinearMap_pair_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have hv : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp

/-- **The normalised descent direction of a nonzero continuous linear functional.**  For a nonzero
`L : ℝ × ℝ →L[ℝ] ℝ` the vector `-((L(1,0))² + (L(0,1))²)⁻¹ • (L(1,0), L(0,1))` is a unit-speed
descent direction of `L`. -/
theorem continuousLinearMap_apply_normalised (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    L (-((((L (1, 0)) ^ 2 + (L (0, 1)) ^ 2)⁻¹)) • (L (1, 0), L (0, 1))) = -1 := by
  -- a nonzero functional has a nonzero coordinate derivative
  have hne : L (1, 0) ≠ 0 ∨ L (0, 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (by
      apply ContinuousLinearMap.ext
      rintro ⟨x, y⟩
      rw [continuousLinearMap_pair_apply, hc.1, hc.2]
      simp)
  -- hence the squared norm of the gradient data does not vanish
  have hcc : (L (1, 0)) ^ 2 + (L (0, 1)) ^ 2 ≠ 0 := by
    rintro h0
    have h1 : (L (1, 0)) ^ 2 = 0 := by nlinarith [sq_nonneg (L (0, 1))]
    have h2 : (L (0, 1)) ^ 2 = 0 := by nlinarith [sq_nonneg (L (1, 0))]
    rcases hne with h | h
    · exact h (sq_eq_zero_iff.mp h1)
    · exact h (sq_eq_zero_iff.mp h2)
  rw [map_smul]
  have hpair : L (L (1, 0), L (0, 1)) =
      L (1, 0) * L (1, 0) + L (0, 1) * L (0, 1) :=
    continuousLinearMap_pair_apply L _ _
  rw [hpair]
  rw [show L (1, 0) * L (1, 0) + L (0, 1) * L (0, 1)
      = (L (1, 0)) ^ 2 + (L (0, 1)) ^ 2 by ring]
  rw [smul_eq_mul, neg_mul, inv_mul_cancel₀ hcc]

theorem fderiv_pullback_normalisedGradField (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} {p : ℝ × ℝ} (hp : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0) : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (Work.Smooth.Morse.normalisedGradField ψ g p) = -1 := by
  exact continuousLinearMap_apply_normalised (fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p) hp

end Work.Smooth.Morse.Flow
