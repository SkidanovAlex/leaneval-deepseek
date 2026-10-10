-- This file is a *copy* of `Submission/Work/MotK/KleinEq.lean` (whose declarations are renamed with
-- the prefix `e11_` so that the copy can be imported by `Submission/Work/MotK/ExistsKleinData.lean`
-- without an import cycle).  The proofs are unchanged.
/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.MotK.E11Model
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.e11_KleinEq`

The five Pfaffian quadrics `kleinP 1 1` vanish on the explicit Klein coordinates
`kleinCoord (kleinDataCandidate 𝕜) L` of the Tate normal form `E₁₁ : y² - 10xy - 11y = x³ - 11x²`
over any field extension `L/𝕜`.

The Klein coordinates are the rows of the matrix

```
κ₀ =               121 + 55x        +  5x²
κ₁ =      -55x + 11y  -  6x² + xy
κ₂ = -121 - 33x       -  7x² + xy
κ₃ = -121 - 22x       +  3x² - xy
κ₄ =  121 + 66x - 11y +  4x² - xy
```

and each Pfaffian reduces modulo the Weierstrass relation `W = y² - 10xy - 11y - x³ + 11x²` to

```
p₀ = (22x + 121)·W,   p₁ = 11x·W,      p₂ = (-11x - 121)·W,
p₃ = (-11x - 121)·W,  p₄ = 11x·W,
```

which is what the `linear_combination` steps below verify.  The Weierstrass relation itself is
`Work.MotC2.genX_genY_relation`, transported to the `MotV` coordinates (`Work.MotV.genX`,
`Work.MotV.genY`) by the bridge lemmas `e11_MotV_genX_eq_MotC2_genX`, `e11_MotV_genY_eq_MotC2_genY`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK

noncomputable section

/-! ## §1  The `MotV` and `MotC2` function-field coordinates agree -/

lemma e11_MotV_genX_eq_MotC2_genX {L : Type} [Field L] (E : WeierstrassCurve L) :
    Work.MotV.genX E = Work.MotC2.genX E := by
  rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]

lemma e11_MotV_genY_eq_MotC2_genY {L : Type} [Field L] (E : WeierstrassCurve L) :
    Work.MotV.genY E = Work.MotC2.genY E := by
  rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]

/-! ## §2  The function field of the candidate Klein datum -/

/-- The function field of the base change to `L` of the curve of the candidate Klein datum. -/
abbrev e11_keFF (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] : Type :=
  Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)

/-- The function field coordinate `x` of that curve. -/
abbrev e11_keX (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] : e11_keFF 𝕜 L :=
  Work.MotV.genX ((kleinDataCandidate 𝕜).E.baseChange L)

/-- The function field coordinate `y` of that curve. -/
abbrev e11_keY (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] : e11_keFF 𝕜 L :=
  Work.MotV.genY ((kleinDataCandidate 𝕜).E.baseChange L)

lemma e11_kleinDataCandidate_coord_apply (𝕜 : Type) [Field 𝕜] (i j : Fin 5) :
    (kleinDataCandidate 𝕜).coord i j = (kleinCoordInt i j : 𝕜) := rfl

/-- The scalar coefficients of the explicit Klein coordinates, in the function field. -/
lemma e11_ke_coeff_intCast (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] (n : ℤ) :
    algebraMap L (e11_keFF 𝕜 L) (algebraMap 𝕜 L ((n : ℤ) : 𝕜)) = ((n : ℤ) : e11_keFF 𝕜 L) := by
  rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L)]
  exact map_intCast (algebraMap 𝕜 (e11_keFF 𝕜 L)) n

/-! ## §3  The base-changed Weierstrass coefficients of `E₁₁` -/

lemma e11_ke_baseChange_a₁ (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    ((kleinDataCandidate 𝕜).E.baseChange L).a₁ = algebraMap 𝕜 L (-10 : 𝕜) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁]
  rfl

lemma e11_ke_baseChange_a₂ (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    ((kleinDataCandidate 𝕜).E.baseChange L).a₂ = algebraMap 𝕜 L (-11 : 𝕜) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂]
  rfl

lemma e11_ke_baseChange_a₃ (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    ((kleinDataCandidate 𝕜).E.baseChange L).a₃ = algebraMap 𝕜 L (-11 : 𝕜) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃]
  rfl

lemma e11_ke_baseChange_a₄ (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    ((kleinDataCandidate 𝕜).E.baseChange L).a₄ = 0 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄,
    show (kleinDataCandidate 𝕜).E.a₄ = (0 : 𝕜) from rfl, map_zero]

lemma e11_ke_baseChange_a₆ (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    ((kleinDataCandidate 𝕜).E.baseChange L).a₆ = 0 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆,
    show (kleinDataCandidate 𝕜).E.a₆ = (0 : 𝕜) from rfl, map_zero]

/-- The Weierstrass relation of `E₁₁` in the function field of the candidate datum:
`y² - 10·x·y - 11·y - x³ + 11·x² = 0`. -/
lemma e11_ke_relation (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    (e11_keY 𝕜 L) ^ 2 - 10 * e11_keX 𝕜 L * e11_keY 𝕜 L - 11 * e11_keY 𝕜 L - (e11_keX 𝕜 L) ^ 3
      + 11 * (e11_keX 𝕜 L) ^ 2 = 0 := by
  have hrel := Work.MotC2.genX_genY_relation ((kleinDataCandidate 𝕜).E.baseChange L)
  rw [← e11_MotV_genX_eq_MotC2_genX ((kleinDataCandidate 𝕜).E.baseChange L),
    ← e11_MotV_genY_eq_MotC2_genY ((kleinDataCandidate 𝕜).E.baseChange L)] at hrel
  rw [e11_ke_baseChange_a₁ 𝕜 L, e11_ke_baseChange_a₂ 𝕜 L, e11_ke_baseChange_a₃ 𝕜 L,
    e11_ke_baseChange_a₄ 𝕜 L, e11_ke_baseChange_a₆ 𝕜 L] at hrel
  simp only [map_zero] at hrel
  have h10 : algebraMap L (e11_keFF 𝕜 L) (algebraMap 𝕜 L (-10 : 𝕜)) = (-10 : e11_keFF 𝕜 L) := by
    rw [show (-10 : 𝕜) = -((10 : ℕ) : 𝕜) from rfl]
    rw [map_neg, map_neg]
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L), map_natCast]
    first | refl_ring1 | ring
  have h11 : algebraMap L (e11_keFF 𝕜 L) (algebraMap 𝕜 L (-11 : 𝕜)) = (-11 : e11_keFF 𝕜 L) := by
    rw [show (-11 : 𝕜) = -((11 : ℕ) : 𝕜) from rfl]
    rw [map_neg, map_neg]
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L), map_natCast]
    first | refl_ring1 | ring
  rw [h10, h11] at hrel
  linear_combination (norm := first | refl_ring1 | ring1) hrel

/-! ## §4  The five Klein coordinates, explicitly -/

/-- `κ₀ = 121 + 55x + 5x²`. -/
lemma e11_ke_kC_0 (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 =
      121 + 55 * e11_keX 𝕜 L + 5 * (e11_keX 𝕜 L) ^ 2 := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [e11_kleinDataCandidate_coord_apply, kleinCoordInt, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [e11_ke_coeff_intCast]
  first | refl_ring1 | ring

/-- `κ₁ = -55x + 11y - 6x² + xy`. -/
lemma e11_ke_kC_1 (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 1 =
      -55 * e11_keX 𝕜 L + 11 * e11_keY 𝕜 L - 6 * (e11_keX 𝕜 L) ^ 2 + e11_keX 𝕜 L * e11_keY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [e11_kleinDataCandidate_coord_apply, kleinCoordInt, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [e11_ke_coeff_intCast]
  first | refl_ring1 | ring

/-- `κ₂ = -121 - 33x - 7x² + xy`. -/
lemma e11_ke_kC_2 (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 2 =
      -121 - 33 * e11_keX 𝕜 L - 7 * (e11_keX 𝕜 L) ^ 2 + e11_keX 𝕜 L * e11_keY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [e11_kleinDataCandidate_coord_apply, kleinCoordInt, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [e11_ke_coeff_intCast]
  first | refl_ring1 | ring

/-- `κ₃ = -121 - 22x + 3x² - xy`. -/
lemma e11_ke_kC_3 (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 3 =
      -121 - 22 * e11_keX 𝕜 L + 3 * (e11_keX 𝕜 L) ^ 2 - e11_keX 𝕜 L * e11_keY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [e11_kleinDataCandidate_coord_apply, kleinCoordInt, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [e11_ke_coeff_intCast]
  first | refl_ring1 | ring

/-- `κ₄ = 121 + 66x - 11y + 4x² - xy`. -/
lemma e11_ke_kC_4 (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 4 =
      121 + 66 * e11_keX 𝕜 L - 11 * e11_keY 𝕜 L + 4 * (e11_keX 𝕜 L) ^ 2 - e11_keX 𝕜 L * e11_keY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [e11_kleinDataCandidate_coord_apply, kleinCoordInt, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [e11_ke_coeff_intCast]
  first | refl_ring1 | ring

/-! ## §5  The Pfaffian identities -/

/-- The Pfaffian identities in the coordinates of the candidate datum. -/
lemma e11_kleinEq_candidate (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L]
    (k : Fin 5) :
    Work.MotK.kleinP (algebraMap 𝕜 (e11_keFF 𝕜 L) 1) (algebraMap 𝕜 (e11_keFF 𝕜 L) 1)
      (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L) k = 0 := by
  have hW : (e11_keY 𝕜 L) ^ 2 - 10 * e11_keX 𝕜 L * e11_keY 𝕜 L - 11 * e11_keY 𝕜 L - (e11_keX 𝕜 L) ^ 3
      + 11 * (e11_keX 𝕜 L) ^ 2 = 0 := e11_ke_relation 𝕜 L
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, e11_ke_kC_0, e11_ke_kC_1, e11_ke_kC_2,
      e11_ke_kC_3, e11_ke_kC_4, RingHom.map_one]
  · linear_combination (norm := first | refl_ring1 | ring1) (22 * e11_keX 𝕜 L + 121) * hW
  · linear_combination (norm := first | refl_ring1 | ring1) (11 * e11_keX 𝕜 L) * hW
  · linear_combination (norm := first | refl_ring1 | ring1) (-(11 * e11_keX 𝕜 L) - 121) * hW
  · linear_combination (norm := first | refl_ring1 | ring1) (-(11 * e11_keX 𝕜 L) - 121) * hW
  · linear_combination (norm := first | refl_ring1 | ring1) (11 * e11_keX 𝕜 L) * hW

theorem e11_KleinEq (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L]
    (k : Fin 5) :
    Work.MotK.kleinP (algebraMap 𝕜 (WeierstrassCurve.Affine.FunctionField ((Work.MotK.E11 𝕜).baseChange L)) 1)
      (algebraMap 𝕜 (WeierstrassCurve.Affine.FunctionField ((Work.MotK.E11 𝕜).baseChange L)) 1)
      (Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L) k = 0 :=
  e11_kleinEq_candidate 𝕜 L k

end

end Work.MotK
