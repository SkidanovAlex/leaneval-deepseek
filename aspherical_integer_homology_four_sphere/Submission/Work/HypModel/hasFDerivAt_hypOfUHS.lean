import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `hypOfUHS` is differentiable, with derivative `dHypOfUHS`

The upper half space model of hyperbolic 4-space is the map
`hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))` from `E4 = ℝ⁴` to the
ambient Lorentz space `V5 = ℝ^{1,4}`.  This file shows that it is (Fréchet) differentiable
wherever `q 3 ≠ 0`, with the derivative `dHypOfUHS q` recorded in the definition file
`Work.HypModel.Basic`.

The proof is coordinatewise: the first three coordinates are quotients `qᵢ/q₃`, and the last two
are `(‖q‖²±1)/(2q₃)`; each is differentiated with the product rule, and the five coordinate
derivatives are glued with `hasFDerivAt_pi'`.
-/

noncomputable section

open scoped Matrix InnerProductSpace

namespace Work.HypModel

/-- The `i`-th coordinate projection of `E4`, as a continuous linear map. -/
def coord (i : Fin 4) : E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

@[simp] theorem coord_apply (i : Fin 4) (q : E4) : coord i q = q i :=
  PiLp.proj_apply 2 (fun _ : Fin 4 => ℝ) i q

/-- The coordinate functions of `E4` are differentiable. -/
theorem hasFDerivAt_coord (i : Fin 4) (q : E4) :
    HasFDerivAt (fun x : E4 => x i) (coord i) q := by
  have h : (fun x : E4 => x i) = fun x : E4 => coord i x := by funext x; rw [coord_apply]
  rw [h]; exact (coord i).hasFDerivAt

/-- The reciprocal of a coordinate: `x ↦ (x i)⁻¹`. -/
theorem hasFDerivAt_inv_coord (i : Fin 4) (q : E4) (hq : q i ≠ 0) :
    HasFDerivAt (fun x : E4 => (x i)⁻¹) (-(((q i ^ 2)⁻¹) • coord i)) q := by
  have h := (hasDerivAt_inv hq).comp_hasFDerivAt q (hasFDerivAt_coord i q)
  simpa [Function.comp_def] using h

/-- The quotient `x ↦ x a / x 3` (with `x 3 ≠ 0`). -/
theorem hasFDerivAt_div_coord (a : Fin 4) (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => x a / x 3)
      ((q 3 ^ 2)⁻¹ • ((q 3) • coord a - (q a) • coord 3)) q := by
  have hnum : HasFDerivAt (fun x : E4 => x a) (coord a) q := hasFDerivAt_coord a q
  have hmul := hnum.mul (hasFDerivAt_inv_coord 3 q hq)
  have hfun : (fun x : E4 => x a / x 3) = fun x : E4 => x a * (x 3)⁻¹ := by
    funext x; rw [div_eq_mul_inv]
  rw [hfun]
  convert hmul using 1
  ext v
  simp only [add_apply, smul_apply, sub_apply, neg_apply, smul_eq_mul, coord_apply]
  field_simp
  ring

/-- The fourth and fifth coordinates of `hypOfUHS`: `x ↦ (‖x‖² + c)/(2 x 3)`. -/
theorem hasFDerivAt_norm_add_div (c : ℝ) (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => (‖x‖ ^ 2 + c) / (2 * x 3))
      ((2 * q 3 ^ 2)⁻¹ • ((2 * q 3) • innerSL ℝ q - (‖q‖ ^ 2 + c) • coord 3)) q := by
  have h0 : HasFDerivAt (fun x : E4 => ‖x‖ ^ 2 + c) (2 • innerSL ℝ q) q := by
    simpa using ((hasFDerivAt_id (E := E4) q).norm_sq).add_const c
  have hA : HasFDerivAt (fun x : E4 => (2:ℝ)⁻¹ * (‖x‖ ^ 2 + c))
      ((2:ℝ)⁻¹ • (2 • innerSL ℝ q)) q := h0.const_smul (2:ℝ)⁻¹
  have hmul := hA.mul (hasFDerivAt_inv_coord 3 q hq)
  have hfun : (fun x : E4 => (‖x‖ ^ 2 + c) / (2 * x 3))
      = (fun x : E4 => (2:ℝ)⁻¹ * (‖x‖ ^ 2 + c)) * (fun x : E4 => (x 3)⁻¹) := by
    funext x
    simp only [Pi.mul_apply, div_eq_mul_inv, mul_inv]
    ring
  rw [hfun]
  convert hmul using 1
  ext v
  simp only [add_apply, smul_apply, sub_apply, neg_apply, smul_eq_mul, coord_apply,
    innerSL_apply_apply]
  field_simp
  ring

/-- First coordinate of `hypOfUHS`. -/
theorem hasFDerivAt_hypOfUHS_coord0 (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => hypOfUHS x (0 : Fin 5))
      ((ContinuousLinearMap.proj (0 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)) q := by
  have hfun : (fun x : E4 => hypOfUHS x (0 : Fin 5)) = fun x : E4 => x 0 / x 3 := by
    funext x; simp
  have hclm : (ContinuousLinearMap.proj (0 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)
      = (q 3 ^ 2)⁻¹ • ((q 3) • coord 0 - (q 0) • coord 3) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      dHypOfUHS_apply_zero, smul_apply, sub_apply, coord_apply, smul_eq_mul]
    field_simp
  rw [hfun, hclm]
  exact hasFDerivAt_div_coord 0 q hq

/-- Second coordinate of `hypOfUHS`. -/
theorem hasFDerivAt_hypOfUHS_coord1 (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => hypOfUHS x (1 : Fin 5))
      ((ContinuousLinearMap.proj (1 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)) q := by
  have hfun : (fun x : E4 => hypOfUHS x (1 : Fin 5)) = fun x : E4 => x 1 / x 3 := by
    funext x; simp
  have hclm : (ContinuousLinearMap.proj (1 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)
      = (q 3 ^ 2)⁻¹ • ((q 3) • coord 1 - (q 1) • coord 3) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      dHypOfUHS_apply_one, smul_apply, sub_apply, coord_apply, smul_eq_mul]
    field_simp
  rw [hfun, hclm]
  exact hasFDerivAt_div_coord 1 q hq

/-- Third coordinate of `hypOfUHS`. -/
theorem hasFDerivAt_hypOfUHS_coord2 (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => hypOfUHS x (2 : Fin 5))
      ((ContinuousLinearMap.proj (2 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)) q := by
  have hfun : (fun x : E4 => hypOfUHS x (2 : Fin 5)) = fun x : E4 => x 2 / x 3 := by
    funext x; simp
  have hclm : (ContinuousLinearMap.proj (2 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)
      = (q 3 ^ 2)⁻¹ • ((q 3) • coord 2 - (q 2) • coord 3) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      dHypOfUHS_apply_two, smul_apply, sub_apply, coord_apply, smul_eq_mul]
    field_simp
  rw [hfun, hclm]
  exact hasFDerivAt_div_coord 2 q hq

/-- Fourth coordinate of `hypOfUHS`. -/
theorem hasFDerivAt_hypOfUHS_coord3 (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => hypOfUHS x (3 : Fin 5))
      ((ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)) q := by
  have hfun : (fun x : E4 => hypOfUHS x (3 : Fin 5))
      = fun x : E4 => (‖x‖ ^ 2 + (-1)) / (2 * x 3) := by
    funext x
    show hypOfUHS x (3 : Fin 5) = (‖x‖ ^ 2 - 1) / (2 * x 3)
    rw [hypOfUHS_apply_three]
  have hclm : (ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)
      = (2 * q 3 ^ 2)⁻¹ • ((2 * q 3) • innerSL ℝ q - (‖q‖ ^ 2 + (-1)) • coord 3) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      dHypOfUHS_apply_three, smul_apply, sub_apply, coord_apply, smul_eq_mul,
      innerSL_apply_apply]
    field_simp
    ring
  rw [hfun, hclm]
  exact hasFDerivAt_norm_add_div (-1) q hq

/-- Fifth coordinate of `hypOfUHS`. -/
theorem hasFDerivAt_hypOfUHS_coord4 (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun x : E4 => hypOfUHS x (4 : Fin 5))
      ((ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)) q := by
  have hfun : (fun x : E4 => hypOfUHS x (4 : Fin 5))
      = fun x : E4 => (‖x‖ ^ 2 + 1) / (2 * x 3) := by
    funext x; rw [hypOfUHS_apply_four]
  have hclm : (ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ).comp (dHypOfUHS q)
      = (2 * q 3 ^ 2)⁻¹ • ((2 * q 3) • innerSL ℝ q - (‖q‖ ^ 2 + 1) • coord 3) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      dHypOfUHS_apply_four, smul_apply, sub_apply, coord_apply, smul_eq_mul,
      innerSL_apply_apply]
    field_simp
  rw [hfun, hclm]
  exact hasFDerivAt_norm_add_div 1 q hq

/-- **`hypOfUHS` is differentiable at every `q` with `q 3 ≠ 0`**, with the explicit derivative
`dHypOfUHS q` recorded in `Work.HypModel.Basic`. -/
theorem hasFDerivAt_hypOfUHS {q : E4} (hq : q 3 ≠ 0) :
    HasFDerivAt hypOfUHS (dHypOfUHS q) q := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · exact hasFDerivAt_hypOfUHS_coord0 q hq
  · exact hasFDerivAt_hypOfUHS_coord1 q hq
  · exact hasFDerivAt_hypOfUHS_coord2 q hq
  · exact hasFDerivAt_hypOfUHS_coord3 q hq
  · exact hasFDerivAt_hypOfUHS_coord4 q hq

end Work.HypModel
