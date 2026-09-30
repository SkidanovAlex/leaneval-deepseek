import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The affine formula for the upper half space position of a Klein point seen from `w`

`uhsPositionAt w P` is the position of the hyperboloid point `P` in the upper half space chart
centred at the ideal point `w` on the sphere at infinity: it is the orthogonal projection of the
first four coordinates of `P` onto `w^⊥ ⊆ ℝ⁴`, divided by `P₄ - ⟪w, P₀₁₂₃⟫`.

For the special case `P = hypOfKlein y` of a Klein point `y ∈ ball`, and for `w` a unit vector, the
denominator is `P₄ - ⟪w, P₀₁₂₃⟫ = s·δ` with `s = (√(1-‖y‖²))⁻¹` and `δ = 1 - ⟪w,y⟫`, while the
numerator is `s · (y - (1-δ)·w)`.  The two factors of `s` cancel and leave the affine expression
`δ⁻¹ • (y - (1-δ) • w)`, which is the formula used in the Klein-model description of the
horospherical hemisphere.
-/

noncomputable section

namespace Work.HypModel

open scoped InnerProductSpace

/-- `proj4` is homogeneous: the projection to the first four coordinates of a scalar multiple of a
vector of `ℝ⁵` is the scalar multiple of the projection. -/
theorem proj4_smul (c : ℝ) (x : V5) : proj4 (c • x) = c • proj4 x := by
  ext i
  fin_cases i <;> simp [proj4]

theorem hemisphere_klein_affine_explicit (w : E4) (hw : ‖w‖ = 1) {δ : ℝ} (hδ : δ ≠ 0)
    {y : E4} (hyb : y ∈ ball) (hy : euclid w y = 1 - δ) :
    uhsPositionAt w (hypOfKlein y) = δ⁻¹ • (y - (1 - δ) • w) := by
  have _ := hw
  have _ := hδ
  -- `s` is the Klein lift factor; it is nonzero because `y` lies in the open unit ball.
  set s : ℝ := (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ with hs
  have hs_ne : s ≠ 0 := by
    rw [hs]
    apply inv_ne_zero
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have h1 : ‖y‖ < 1 := hyb
    nlinarith [norm_nonneg y]
  -- `hypOfKlein y = s • ray y`.
  have hP : hypOfKlein y = s • ray y := by rw [hypOfKlein, hs]
  -- The first four coordinates of `hypOfKlein y` are `s • y`.
  have hproj : proj4 (hypOfKlein y) = s • y := by
    rw [hP, proj4_smul, proj4_ray]
  -- The fourth coordinate is `s`.
  have hfour : hypOfKlein y 4 = s := by
    rw [hP]; simp
  -- The inner product `⟪w, proj4 (hypOfKlein y)⟫` is `s·(1-δ)`.
  have hinner : ⟪w, proj4 (hypOfKlein y)⟫_ℝ = s * (1 - δ) := by
    rw [hproj, real_inner_smul_right]
    have : ⟪w, y⟫_ℝ = 1 - δ := hy
    rw [this]
  rw [uhsPositionAt, hfour, hinner, hproj]
  -- Denominator: `s - s·(1-δ) = s·δ`; numerator: `s•y - (s·(1-δ))•w = s•(y-(1-δ)•w)`.
  have hden : s - s * (1 - δ) = s * δ := by ring
  rw [hden]
  have hnum : s • y - (s * (1 - δ)) • w = s • (y - (1 - δ) • w) := by
    rw [mul_smul, smul_sub]
  rw [hnum]
  -- The two factors of `s` cancel: `(s·δ)⁻¹ • (s • v) = δ⁻¹ • v`.
  have hcoef : (s * δ)⁻¹ * s = δ⁻¹ := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
  rw [smul_smul, hcoef]

end Work.HypModel
