/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The pole order at infinity: setup

This file collects the elementary computations that the proof of `Work.MotC2.PoleOrder` builds
on.  For a Weierstrass curve `E` over a field `L` we introduce the two polynomials

* `cubicPoly E = X³ + a₂X² + a₄X + a₆` and
* `linPoly E = a₁X + a₃`,

so that the Weierstrass relation in the function field `L(E) = Func E` reads

`y² = c(x) - t(x)·y`  (`x = genX E`, `y = genY E`).

Writing `w = infW E = y/x²` for the uniformizer of the point at infinity and `u = infU E = 1/x`,
the relation gives the identities

* `infW_sq_eq`: `w² = c(x)/x⁴ - t(x)·w/x²`,
* `infW_cube_eq`: `w³ = (c(x) + t(x)²)·w/x⁴ - t(x)·c(x)/x⁶`,
* `genY_mul_infW_sq_eq`: `y·w² = (c(x) + t(x)²)·w/x² - t(x)·c(x)/x⁴`,

and multiplication by `x` gives

* `genX_mul_infW_sq`: `x·w² = 1 + a₂u + a₄u² + a₆u³ - (a₁ + a₃u)·w`,
* `genX_mul_infW_cube`: `x·w³ = (x·w²)·w`,
* `genY_mul_infW_cube`: `y·w³ = (x·w²)²`.

## Tags

elliptic curve, function field, pole order, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

set_option maxHeartbeats 1000000

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- The cubic `X³ + a₂X² + a₄X + a₆` of a Weierstrass curve; its value at `x = genX E` is the
right hand side of the Weierstrass equation. -/
noncomputable def cubicPoly (E : WeierstrassCurve L) : L[X] :=
  X ^(3:ℕ) + C E.a₂ * X ^(2:ℕ) + C E.a₄ * X + C E.a₆

/-- The linear coefficient `a₁X + a₃` of a Weierstrass curve; its value at `x = genX E` is the
coefficient of `y` in the Weierstrass equation. -/
noncomputable def linPoly (E : WeierstrassCurve L) : L[X] :=
  C E.a₁ * X + C E.a₃

lemma aeval_linPoly (E : WeierstrassCurve L) :
    Polynomial.aeval (genX E) (linPoly E) =
      algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃ := by
  simp [linPoly, aeval_def]

lemma aeval_cubicPoly (E : WeierstrassCurve L) :
    Polynomial.aeval (genX E) (cubicPoly E) =
      (genX E) ^(3:ℕ) + algebraMap L (Func E) E.a₂ * (genX E) ^(2:ℕ) +
        algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆ := by
  simp [cubicPoly, aeval_def]

lemma cubicPoly_ne_zero (E : WeierstrassCurve L) : cubicPoly E ≠ 0 := by
  intro h0
  have := congrArg (fun p : L[X] => p.coeff 3) h0
  simpa [cubicPoly] using this

lemma cubicPoly_degree (E : WeierstrassCurve L) : (cubicPoly E).degree = 3 := by
  have h := degree_cubic (R := L) (a := 1) (b := E.a₂) (c := E.a₄) (d := E.a₆) one_ne_zero
  rw [cubicPoly]
  simpa [C_1] using h

lemma linPoly_degree_le (E : WeierstrassCurve L) : (linPoly E).degree ≤ 1 := by
  rw [linPoly]
  refine le_trans (degree_add_le _ _) (max_le ?_ ?_)
  · exact degree_C_mul_X_le _
  · exact le_trans degree_C_le (by norm_num)

/-- The Weierstrass relation in the function field, solved for `y²`. -/
lemma genY_sq_rel (E : WeierstrassCurve L) :
    (genY E) ^(2:ℕ) = Polynomial.aeval (genX E) (cubicPoly E) -
      Polynomial.aeval (genX E) (linPoly E) * genY E := by
  have h := genY_sq_relation E
  rw [aeval_linPoly, aeval_cubicPoly]
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- `w·x² = y`. -/
lemma infW_mul_genX_sq (E : WeierstrassCurve L) : infW E * (genX E) ^(2:ℕ) = genY E := by
  rw [infW, div_mul_cancel₀ _ (pow_ne_zero 2 (genX_ne_zero E))]

/-- The Weierstrass relation in the chart at infinity, multiplied by `x`. -/
lemma genX_mul_infW_sq (E : WeierstrassCurve L) :
    genX E * (infW E) ^(2:ℕ) =
      (1 + algebraMap L (Func E) E.a₂ * infU E + algebraMap L (Func E) E.a₄ * infU E ^(2:ℕ) +
          algebraMap L (Func E) E.a₆ * infU E ^(3:ℕ)) -
        (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * infW E := by
  have h := infW_sq_relation E
  have hx : genX E ≠ 0 := genX_ne_zero E
  rw [infU] at h ⊢
  field_simp at h ⊢
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- `w²` expressed through `x`: the Weierstrass relation divided by `x⁴`. -/
lemma infW_sq_eq (E : WeierstrassCurve L) :
    (infW E) ^(2:ℕ) = Polynomial.aeval (genX E) (cubicPoly E) / (genX E) ^(4:ℕ) -
      Polynomial.aeval (genX E) (linPoly E) * infW E / (genX E) ^(2:ℕ) := by
  have hx : genX E ≠ 0 := genX_ne_zero E
  have h4 : (genX E) ^(4:ℕ) ≠ 0 := pow_ne_zero 4 hx
  have h1 : infW E * (genX E) ^(2:ℕ) = genY E := infW_mul_genX_sq E
  have key : (infW E) ^(2:ℕ) * (genX E) ^(4:ℕ) = Polynomial.aeval (genX E) (cubicPoly E) -
      Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ)) := by
    calc (infW E) ^(2:ℕ) * (genX E) ^(4:ℕ) = (infW E * (genX E) ^(2:ℕ)) ^(2:ℕ) := by ring
      _ = (genY E) ^(2:ℕ) := by rw [h1]
      _ = Polynomial.aeval (genX E) (cubicPoly E) -
          Polynomial.aeval (genX E) (linPoly E) * genY E := genY_sq_rel E
      _ = Polynomial.aeval (genX E) (cubicPoly E) -
          Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ)) := by rw [h1]
  have hq : Polynomial.aeval (genX E) (linPoly E) * infW E / (genX E) ^(2:ℕ) =
      Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ)) / (genX E) ^(4:ℕ) := by
    field_simp
  rw [hq, ← sub_div, eq_div_iff h4]
  exact key

/-- `w²·x⁴ = c(x) - t(x)·w·x²`, the cleared form of `infW_sq_eq`. -/
lemma infW_sq_mul_genX_pow (E : WeierstrassCurve L) :
    (infW E) ^(2:ℕ) * (genX E) ^(4:ℕ) = Polynomial.aeval (genX E) (cubicPoly E) -
      Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ)) := by
  have h := infW_sq_eq E
  have hx : genX E ≠ 0 := genX_ne_zero E
  have : Polynomial.aeval (genX E) (cubicPoly E) -
      Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ)) =
      (Polynomial.aeval (genX E) (cubicPoly E) / (genX E) ^(4:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * infW E / (genX E) ^(2:ℕ)) * (genX E) ^(4:ℕ) := by
    field_simp
  rw [this, ← h]

/-- `w³` expressed through `x`. -/
lemma infW_cube_eq (E : WeierstrassCurve L) :
    (infW E) ^(3:ℕ) =
      (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E / (genX E) ^(4:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
          (genX E) ^(6:ℕ) := by
  have hx : genX E ≠ 0 := genX_ne_zero E
  have h6 : (genX E) ^(6:ℕ) ≠ 0 := pow_ne_zero 6 hx
  have hkey := infW_sq_mul_genX_pow E
  have key : (infW E) ^(3:ℕ) * (genX E) ^(6:ℕ) =
      (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) := by
    calc (infW E) ^(3:ℕ) * (genX E) ^(6:ℕ) =
        ((infW E) ^(2:ℕ) * (genX E) ^(4:ℕ)) * ((infW E) * (genX E) ^(2:ℕ)) := by ring
      _ = (Polynomial.aeval (genX E) (cubicPoly E) -
            Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ))) *
            ((infW E) * (genX E) ^(2:ℕ)) := by rw [hkey]
      _ = Polynomial.aeval (genX E) (cubicPoly E) * (infW E * (genX E) ^(2:ℕ)) -
            Polynomial.aeval (genX E) (linPoly E) * ((infW E) ^(2:ℕ) * (genX E) ^(4:ℕ)) := by ring
      _ = Polynomial.aeval (genX E) (cubicPoly E) * (infW E * (genX E) ^(2:ℕ)) -
            Polynomial.aeval (genX E) (linPoly E) * (Polynomial.aeval (genX E) (cubicPoly E) -
              Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ))) := by rw [hkey]
      _ = (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) := by ring
  rw [show (Polynomial.aeval (genX E) (cubicPoly E) +
        (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) * infW E / (genX E) ^(4:ℕ) =
      ((Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ)) / (genX E) ^(6:ℕ) from by field_simp, ← sub_div, eq_div_iff h6]
  exact key

/-- `y·w²` expressed through `x`. -/
lemma genY_mul_infW_sq_eq (E : WeierstrassCurve L) :
    genY E * (infW E) ^(2:ℕ) =
      (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E / (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
          (genX E) ^(4:ℕ) := by
  have hx : genX E ≠ 0 := genX_ne_zero E
  have h4 : (genX E) ^(4:ℕ) ≠ 0 := pow_ne_zero 4 hx
  have h1 : infW E * (genX E) ^(2:ℕ) = genY E := infW_mul_genX_sq E
  have hkey := infW_sq_mul_genX_pow E
  have key : genY E * (infW E) ^(2:ℕ) * (genX E) ^(4:ℕ) =
      (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) := by
    calc genY E * (infW E) ^(2:ℕ) * (genX E) ^(4:ℕ) =
        ((infW E) * (genX E) ^(2:ℕ)) * ((infW E) ^(2:ℕ) * (genX E) ^(4:ℕ)) := by rw [h1]; ring
      _ = ((infW E) * (genX E) ^(2:ℕ)) *
            (Polynomial.aeval (genX E) (cubicPoly E) -
              Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ))) := by rw [hkey]
      _ = Polynomial.aeval (genX E) (cubicPoly E) * (infW E * (genX E) ^(2:ℕ)) -
            Polynomial.aeval (genX E) (linPoly E) * ((infW E) ^(2:ℕ) * (genX E) ^(4:ℕ)) := by ring
      _ = Polynomial.aeval (genX E) (cubicPoly E) * (infW E * (genX E) ^(2:ℕ)) -
            Polynomial.aeval (genX E) (linPoly E) * (Polynomial.aeval (genX E) (cubicPoly E) -
              Polynomial.aeval (genX E) (linPoly E) * (infW E * (genX E) ^(2:ℕ))) := by rw [hkey]
      _ = (Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) := by ring
  rw [show (Polynomial.aeval (genX E) (cubicPoly E) +
        (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) * infW E / (genX E) ^(2:ℕ) -
        Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
          (genX E) ^(4:ℕ) =
      ((Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^(2:ℕ)) *
          infW E * (genX E) ^(2:ℕ)) / (genX E) ^(4:ℕ) -
        (Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E)) /
          (genX E) ^(4:ℕ) from by field_simp, ← sub_div, eq_div_iff h4]
  exact key

/-- `x·w³ = (x·w²)·w`. -/
lemma genX_mul_infW_cube (E : WeierstrassCurve L) :
    genX E * (infW E) ^(3:ℕ) = (genX E * (infW E) ^(2:ℕ)) * infW E := by
  first | refl_ring1 | ring

/-- `y·w³ = (x·w²)²`. -/
lemma genY_mul_infW_cube (E : WeierstrassCurve L) :
    genY E * (infW E) ^(3:ℕ) = (genX E * (infW E) ^(2:ℕ)) ^(2:ℕ) := by
  have h1 : infW E * (genX E) ^(2:ℕ) = genY E := infW_mul_genX_sq E
  calc genY E * (infW E) ^(3:ℕ) = (infW E * (genX E) ^(2:ℕ)) * (infW E) ^(3:ℕ) := by rw [h1]
    _ = (genX E * (infW E) ^(2:ℕ)) ^(2:ℕ) := by ring

end Work.MotC2
