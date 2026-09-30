import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein model metric is the pullback of the Lorentz form along `hypOfKlein`

For a point `y` of the open unit ball (the Klein model of hyperbolic 4-space), the Fréchet
derivative of the Klein lift `hypOfKlein y = (y,1)/√(1−‖y‖²)` is

`v ↦ s³⟪y,v⟫ • ray y + s • emb v`,   where `s = (√(1−‖y‖²))⁻¹` and `emb v = (v,0)`,

because the lift is the product of the scalar function `s` and the affine map `y ↦ (y,1)`: the
derivative of `s` is `s³⟪y,·⟫` and the derivative of `y ↦ ray y` is `emb`.

Since `⟨ray y, ray y⟩ = ‖y‖² − 1`, `⟨emb v, emb w⟩ = ⟪v,w⟫` and `⟨emb v, ray y⟩ = ⟪y,v⟫`, the
pullback of the Lorentz form is

`⟨s³⟪y,v⟫•ray y + s•emb v, s³⟪y,w⟫•ray y + s•emb w⟩ = s²⟪v,w⟫ + s⁴⟪y,v⟫⟪y,w⟫`,

which is `kleinMetric y v w` because `s² = (1 − ‖y‖²)⁻¹`.

## Main result

* `Work.HypModel.lorentz_hypOfKlein` : `kleinMetric` is the pullback of the Lorentz form along the
  Klein lift `hypOfKlein`.  This is the Klein analogue of the Lorentzian isometry statement for the
  upper half space chart, and the input to `mobiusKlein_isometry`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-! ### The tangent inclusion `E4 ↪ V5`

Throughout, `emb` is the linear inclusion of the Klein coordinates `E4 = ℝ⁴` into the ambient
Lorentz space `V5 = ℝ^{1,4}` as the first four coordinates, with last coordinate `0`.  Its image is
the space-like part of `ℝ^{1,4}`, and it is the derivative of the affine map `y ↦ ray y`. -/

/-- The inclusion `E4 ↪ V5`, `v ↦ (v,0)`. -/
private def emb : E4 →L[ℝ] V5 :=
  LinearMap.toContinuousLinearMap
    { toFun v := ![v 0, v 1, v 2, v 3, 0]
      map_add' v w := by ext i; fin_cases i <;> simp
      map_smul' c v := by ext i; fin_cases i <;> simp }

@[simp] private theorem emb_apply_zero (v : E4) : emb v 0 = v 0 := rfl
@[simp] private theorem emb_apply_one (v : E4) : emb v 1 = v 1 := rfl
@[simp] private theorem emb_apply_two (v : E4) : emb v 2 = v 2 := rfl
@[simp] private theorem emb_apply_three (v : E4) : emb v 3 = v 3 := rfl
@[simp] private theorem emb_apply_four (v : E4) : emb v 4 = 0 := rfl

private theorem proj4_emb (v : E4) : proj4 (emb v) = v := by
  ext i; fin_cases i <;> simp [proj4, emb]

/-- The Lorentz pairing of `emb v` and `emb w` is the Euclidean inner product `⟪v,w⟫`. -/
private theorem lorentz_emb_emb (v w : E4) : lorentz (emb v) (emb w) = ⟪v, w⟫_ℝ := by
  rw [lorentz_eq_dotProduct_proj4, proj4_emb, proj4_emb, inner_eq_dotProduct]
  simp

/-- `⟨emb v, ray y⟩ = ⟪y,v⟫`: the space-like part of `ray y` is `y` and the last coordinate of
`emb v` vanishes. -/
private theorem lorentz_emb_ray (v y : E4) : lorentz (emb v) (ray y) = ⟪y, v⟫_ℝ := by
  rw [lorentz_eq_dotProduct_proj4, proj4_emb, proj4_ray, inner_eq_dotProduct]
  simp [dotProduct_comm]

/-- `⟨ray y, emb w⟩ = ⟪y,w⟫`. -/
private theorem lorentz_ray_emb (y w : E4) : lorentz (ray y) (emb w) = ⟪y, w⟫_ℝ := by
  rw [lorentz_eq_dotProduct_proj4, proj4_ray, proj4_emb, inner_eq_dotProduct]
  simp

/-- `ray` is the affine map `y ↦ emb y + (0,0,0,0,1)`, so its derivative is `emb`. -/
private theorem emb_add_timeVec (y : E4) : emb y + timeVec = ray y := by
  ext i; fin_cases i <;> simp [emb, timeVec, ray]

private theorem hasFDerivAt_ray (y : E4) : HasFDerivAt (fun x : E4 => ray x) emb y := by
  have h : HasFDerivAt (fun x : E4 => emb x + timeVec) emb y := emb.hasFDerivAt.add_const timeVec
  simpa only [emb_add_timeVec] using h

/-! ### The normalising factor of the Klein lift and its derivative -/

/-- The normalising factor `s(y) = (√(1−‖y‖²))⁻¹` of the Klein lift. -/
private def cKlein (y : E4) : ℝ := (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹

private theorem one_sub_norm_sq_pos_of_ball {y : E4} (hy : y ∈ ball) : 0 < 1 - ‖y‖ ^ 2 := by
  simp [ball] at hy
  nlinarith [norm_nonneg y]

/-- `s(y)² = (1−‖y‖²)⁻¹` on the ball. -/
private theorem cKlein_sq {y : E4} (hy : y ∈ ball) : (cKlein y) ^ 2 = (1 - ‖y‖ ^ 2)⁻¹ := by
  rw [cKlein, inv_pow, Real.sq_sqrt (le_of_lt (one_sub_norm_sq_pos_of_ball hy))]

/-- `s(y)²(1−‖y‖²) = 1` on the ball. -/
private theorem cKlein_sq_mul {y : E4} (hy : y ∈ ball) : (cKlein y) ^ 2 * (1 - ‖y‖ ^ 2) = 1 := by
  rw [cKlein_sq hy]
  exact inv_mul_cancel₀ (ne_of_gt (one_sub_norm_sq_pos_of_ball hy))

/-- The derivative of `y ↦ √(1−‖y‖²)`: it is `−(√(1−‖y‖²))⁻¹ • innerSL ℝ y`, i.e.
`v ↦ −⟪y,v⟫/√(1−‖y‖²)`. -/
private theorem hasFDerivAt_sqrt_one_sub_norm_sq {y : E4} (hy : y ∈ ball) :
    HasFDerivAt (fun x : E4 => Real.sqrt (1 - ‖x‖ ^ 2))
      ((-(Real.sqrt (1 - ‖y‖ ^ 2))⁻¹) • innerSL ℝ y) y := by
  have hu : 1 - ‖y‖ ^ 2 ≠ 0 := ne_of_gt (one_sub_norm_sq_pos_of_ball hy)
  have hbase : HasFDerivAt (fun x : E4 => 1 - ‖x‖ ^ 2) (-(2 • innerSL ℝ y)) y := by
    have h' : HasFDerivAt (fun x : E4 => ‖x‖ ^ 2) (2 • innerSL ℝ y) y := by
      simpa using (hasFDerivAt_id (E := E4) y).norm_sq
    exact h'.const_sub (1 : ℝ)
  have h := (Real.hasDerivAt_sqrt hu).comp_hasFDerivAt y hbase
  simp only [Function.comp_def] at h
  have hclm : ((1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • (-(2 • innerSL ℝ y)))
      = (-(Real.sqrt (1 - ‖y‖ ^ 2))⁻¹) • innerSL ℝ y := by
    ext v
    simp only [_root_.smul_apply, _root_.neg_apply, innerSL_apply_apply, smul_eq_mul]
    field_simp
    ring
  rwa [hclm] at h

/-- The derivative of the normalising factor `s(y) = (√(1−‖y‖²))⁻¹` is `s(y)³ • innerSL ℝ y`,
i.e. `v ↦ s(y)³⟪y,v⟫`. -/
private theorem hasFDerivAt_cKlein {y : E4} (hy : y ∈ ball) :
    HasFDerivAt cKlein ((cKlein y) ^ 3 • innerSL ℝ y) y := by
  have hpos := one_sub_norm_sq_pos_of_ball hy
  have hsne : Real.sqrt (1 - ‖y‖ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have h := (hasDerivAt_inv hsne).comp_hasFDerivAt y (hasFDerivAt_sqrt_one_sub_norm_sq hy)
  simp only [Function.comp_def] at h
  have hclm : (-(Real.sqrt (1 - ‖y‖ ^ 2) ^ 2)⁻¹) •
        ((-(Real.sqrt (1 - ‖y‖ ^ 2))⁻¹) • innerSL ℝ y)
      = (cKlein y) ^ 3 • innerSL ℝ y := by
    ext v
    simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, cKlein, inv_pow]
    field_simp
  rw [show (fun x : E4 => (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹) = cKlein from rfl, hclm] at h
  exact h

/-! ### The derivative of the Klein lift -/

/-- The explicit derivative of the Klein lift at `y`:
`v ↦ s(y) • emb v + (s(y)³⟪y,v⟫) • ray y` with `s = cKlein`. -/
private def dHypOfKlein (y : E4) : E4 →L[ℝ] V5 :=
  cKlein y • emb + ((cKlein y) ^ 3 • innerSL ℝ y).smulRight (ray y)

private theorem dHypOfKlein_apply (y v : E4) :
    dHypOfKlein y v = cKlein y • emb v + ((cKlein y) ^ 3 * ⟪y, v⟫_ℝ) • ray y := by
  simp [dHypOfKlein, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- **`hypOfKlein` is differentiable on the ball**, with the explicit derivative `dHypOfKlein y`:
the product rule applied to `hypOfKlein y = cKlein y • ray y`, using the derivative `emb` of the
affine map `ray` and the derivative `s³ • innerSL ℝ y` of the scalar factor `s`. -/
private theorem hasFDerivAt_hypOfKlein {y : E4} (hy : y ∈ ball) :
    HasFDerivAt hypOfKlein (dHypOfKlein y) y := by
  have h := (hasFDerivAt_cKlein hy).smul (hasFDerivAt_ray y)
  have hfun : hypOfKlein = fun x : E4 => cKlein x • ray x := by
    funext x; simp [hypOfKlein, cKlein]
  rw [hfun]
  simpa [dHypOfKlein] using h

/-! ### The pullback of the Lorentz form -/

/-- **The Lorentz form on the derivative of the Klein lift is the Klein metric.**  Expanding
`lorentz (dHypOfKlein y v) (dHypOfKlein y w)` bilinearly gives
`s²⟪v,w⟫ + 2s⁴⟪y,v⟫⟪y,w⟫ + s⁶⟪y,v⟫⟪y,w⟫(‖y‖²−1) = s²⟪v,w⟫ + s⁴⟪y,v⟫⟪y,w⟫`,
where the cancellation uses `s²(1−‖y‖²) = 1`. -/
private theorem lorentz_dHypOfKlein {y : E4} (hy : y ∈ ball) (v w : E4) :
    lorentz (dHypOfKlein y v) (dHypOfKlein y w)
      = cKlein y ^ 2 * ⟪v, w⟫_ℝ + cKlein y ^ 4 * (⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ) := by
  have hc2m := cKlein_sq_mul hy
  rw [dHypOfKlein_apply, dHypOfKlein_apply]
  simp only [lorentz_add_left, lorentz_add_right, lorentz_smul_left, lorentz_smul_right,
    lorentz_emb_emb, lorentz_emb_ray, lorentz_ray_emb, lorentz_ray_self]
  linear_combination (-(cKlein y ^ 4 * (⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ))) * hc2m

/-- `kleinMetric` in terms of the normalising factor `s = cKlein y`: on the ball,
`kleinMetric y v w = s²⟪v,w⟫ + s⁴⟪y,v⟫⟪y,w⟫`. -/
private theorem kleinMetric_eq {y : E4} (hy : y ∈ ball) (v w : E4) :
    kleinMetric y v w = cKlein y ^ 2 * ⟪v, w⟫_ℝ + cKlein y ^ 4 * (⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ) := by
  rw [kleinMetric, ← cKlein_sq hy]
  ring

/-- **The Klein model metric `kleinMetric` is the pullback of the Lorentz form along the Klein
lift `hypOfKlein`.**  For every `y` in the open unit ball and all tangent vectors `v, w`,
`⟨d(hypOfKlein) y v, d(hypOfKlein) y w⟩ = kleinMetric y v w`. -/
theorem lorentz_hypOfKlein {y : E4} (hy : y ∈ ball) (v w : E4) :
    lorentz (fderiv ℝ hypOfKlein y v) (fderiv ℝ hypOfKlein y w) = kleinMetric y v w := by
  rw [(hasFDerivAt_hypOfKlein hy).fderiv, kleinMetric_eq hy]
  exact lorentz_dHypOfKlein hy v w

end Work.HypModel
