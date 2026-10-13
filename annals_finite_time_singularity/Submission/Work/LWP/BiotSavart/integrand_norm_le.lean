/-
# `Work.LWP.BiotSavart.integrand_norm_le` — the pointwise Biot–Savart kernel bound

For a vorticity `ω` bounded by `M`, and for points `x` with `‖x‖ ≥ 2R` and `y` with `‖y‖ ≤ R`,
the Newtonian-potential Biot–Savart integrand

  `(‖x - y‖³)⁻¹ • (ω y × (x - y))`

is bounded by `4 M / ‖x‖²`.  This is the elementary kernel estimate
`‖K(x,y)‖ ≤ M · 4/‖x‖²` (with `‖K(x,y)‖ ≤ ‖ω y‖/‖x-y‖²` and `‖x - y‖ ≥ ‖x‖/2`) used by
`Work.LWP.BiotSavart.farField_decay` to obtain the decay `‖biotSavart ω x‖ ≲ M R³/‖x‖²`.

The constant `4` is sharp: it is attained when `‖y‖ = R = ‖x‖/2` and `y` is antipodal to `x`.
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.cube_inv_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.LWP.BiotSavart

/-- The Euclidean (`L²`) norm of the cross product of two vectors of `ℝ³` is at most the product
of their norms.  `crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`; the coercion
`R3 → (Fin 3 → ℝ)` is `WithLp.ofLp` and `WithLp.toLp 2` puts the `L²` norm back on the codomain,
so this is `‖u × v‖ = ‖u‖‖v‖ sin θ ≤ ‖u‖‖v‖`. -/
theorem norm_toLp_crossProduct_le (u v : R3) :
    ‖WithLp.toLp 2 (crossProduct u v)‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖WithLp.toLp 2 (crossProduct u v)‖
      = ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) :=
    InnerProductGeometry.norm_ofLp_crossProduct u v
  calc ‖WithLp.toLp 2 (crossProduct u v)‖
      = ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) := h
    _ ≤ ‖u‖ * ‖v‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖u‖ * ‖v‖ := by ring

/-- **Pointwise bound on the Biot–Savart integrand.**  If `‖x‖ ≥ 2R` and `‖y‖ ≤ R` then
`‖x - y‖ ≥ ‖x‖/2`, so the kernel `(‖x - y‖³)⁻¹ • (ω y × (x - y))` is bounded by
`‖ω y‖ · 4/‖x‖² ≤ 4 M/‖x‖²`. -/
theorem integrand_norm_le {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) {x y : R3} (hx : 2 * R ≤ ‖x‖) (hy : ‖y‖ ≤ R) :
    ‖WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))‖
      ≤ 4 / ‖x‖ ^ 2 * M := by
  have hX : 0 ≤ ‖x‖ := norm_nonneg x
  have ha : 0 ≤ ‖x - y‖ := norm_nonneg _
  -- `‖y‖ ≤ R ≤ ‖x‖/2`
  have hy2 : ‖y‖ ≤ ‖x‖ / 2 := by linarith
  -- `‖x‖/2 ≤ ‖x - y‖`, hence `‖x‖ ≤ 2‖x - y‖`
  have h1 : ‖x‖ ≤ 2 * ‖x - y‖ := by
    have h := norm_sub_norm_le x y
    linarith
  -- `‖x - y‖ ≤ ‖x‖ + ‖y‖ ≤ 3‖x‖/2`
  have h2 : ‖x - y‖ ≤ 3 * ‖x‖ / 2 := by
    have h := norm_sub_le x y
    linarith
  have hcore : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ ≤ 4 * (‖x‖ ^ 2)⁻¹ :=
    cube_inv_mul_le hX ha h1 h2
  have hcp : ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ ≤ M * ‖x - y‖ :=
    le_trans (norm_toLp_crossProduct_le (ω y) (x - y))
      (mul_le_mul_of_nonneg_right (hω y) ha)
  calc ‖WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))‖
      = (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ := by
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    _ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcp (inv_nonneg.mpr (by positivity))
    _ = M * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) := by ring
    _ ≤ M * (4 * (‖x‖ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hcore hM
    _ = 4 / ‖x‖ ^ 2 * M := by ring

end Work.LWP.BiotSavart
