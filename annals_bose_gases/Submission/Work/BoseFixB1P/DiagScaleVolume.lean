import Mathlib
import Submission.Work.BoseFixB1P.BoxScale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pushforward of Lebesgue measure under a diagonal scaling

`Work.BoseFixB1P.diagScale c` scales the `j`-th coordinate of `ℝ³` by `c_j`.  This module
computes its pushforward of Lebesgue measure,

    `Measure.map (diagScale c) volume = (∏_j ENNReal.ofReal |c_j|⁻¹) • volume`   (`c_j ≠ 0`),

by reducing to the coordinatewise diagonal linear map on `(Fin 3 → ℝ)`
(`Real.map_linearMap_volume_pi_eq_smul_volume_pi` with `Matrix.toLin' (Matrix.diagonal c)`),
transporting along the measure preserving `cgEuc3`.

This is the measure-theoretic input for the rescaling of an axis-parallel box onto the cube
`acube a`, the step that reduces `Work.BoseFixB1P.boxPoincareSharp` to its cube case.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
open Submission.BoseGases

namespace Work.BoseFixB1P

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The pushforward of the product Lebesgue measure** under the coordinatewise diagonal
scaling of `Fin 3 → ℝ`. -/
lemma map_coordDiag_volume {c : Fin 3 → ℝ} (hc : ∀ j, c j ≠ 0) :
    Measure.map (fun x : Fin 3 → ℝ => fun j => c j * x j) (volume : Measure (Fin 3 → ℝ))
      = (∏ j, ENNReal.ofReal |c j|⁻¹) • (volume : Measure (Fin 3 → ℝ)) := by
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) = ∏ j : Fin 3, c j := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal]
  have hne : LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (ι := Fin 3) hne
  have hfun : (Matrix.toLin' (Matrix.diagonal c) : (Fin 3 → ℝ) → (Fin 3 → ℝ))
      = fun x j => c j * x j := by
    funext x j
    simp only [Matrix.diagonal_toLin', LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
  rw [hfun, hdet] at hmap
  rw [hmap, abs_inv, Finset.abs_prod, ← Finset.prod_inv_distrib,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => inv_nonneg.mpr (abs_nonneg _))]

/-- `cgEuc3.symm` pushes the volume of `ℝ³` forward to the volume of `Fin 3 → ℝ`. -/
lemma map_cgEuc3_symm_volume :
    Measure.map (⇑cgEuc3.symm) (volume : Measure E3)
      = (volume : Measure (Fin 3 → ℝ)) := by
  rw [← cgEuc3_mp.map_eq,
    Measure.map_map cgEuc3.symm.measurable cgEuc3.measurable,
    show ⇑cgEuc3.symm ∘ ⇑cgEuc3 = id from funext (fun x => cgEuc3.symm_apply_apply x),
    Measure.map_id]

/-- **The pushforward of Lebesgue measure under a diagonal scaling of `ℝ³`.** -/
lemma map_diagScale_volume {c : Fin 3 → ℝ} (hc : ∀ j, c j ≠ 0) :
    Measure.map (diagScale c) (volume : Measure E3)
      = (∏ j, ENNReal.ofReal |c j|⁻¹) • (volume : Measure E3) := by
  have hmeas_diag : Measurable (fun x : Fin 3 → ℝ => fun j => c j * x j) :=
    Measurable.of_eval (fun j =>
      (measurable_const_mul (c j)).comp (measurable_pi_apply j))
  have hcomp_eq : Measure.map (diagScale c) (volume : Measure E3)
      = Measure.map ((⇑cgEuc3) ∘ ((fun x : Fin 3 → ℝ => fun j => c j * x j) ∘ (⇑cgEuc3.symm)))
          (volume : Measure E3) := rfl
  rw [hcomp_eq, ← Measure.map_map cgEuc3.measurable (hmeas_diag.comp cgEuc3.symm.measurable),
    ← Measure.map_map hmeas_diag cgEuc3.symm.measurable, map_cgEuc3_symm_volume,
    map_coordDiag_volume hc, Measure.map_smul, cgEuc3_mp.map_eq]
  all_goals first | fun_prop | measurability

/-- A diagonal scaling with nonzero factors is injective. -/
lemma injective_diagScale {c : Fin 3 → ℝ} (hc : ∀ j, c j ≠ 0) :
    Function.Injective (diagScale c) := by
  intro x y hxy
  ext j
  have h : c j * x j = c j * y j := by
    have := congrArg (fun z : E3 => z j) hxy
    simpa only [diagScale_apply] using this
  exact mul_left_cancel₀ (hc j) h

end Work.BoseFixB1P
