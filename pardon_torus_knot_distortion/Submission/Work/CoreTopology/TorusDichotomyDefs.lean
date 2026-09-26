import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk

/-!
# Auxiliary definitions for the classification of compressing loops

The standard torus of revolution of `ℝ³` (major radius `2`, minor radius `1`) is the level set
`{1}` of the height function

  `torusHeight P = (r - 2)² + z²`,  where `r = √(x² + y²)`,  `P = (x, y, z)`.

`ℝ³ ∖ F` has the two components `{torusHeight < 1}` (the solid torus inside) and
`{1 < torusHeight}` (the exterior).  A compressing disc lies with its interior in one of
them, and the two coordinates of the torus are read off by the two maps

* `horizVec P = x + y·i` (whose direction is `exp (i θ)`), and
* `meridVec P = (r - 2) + z·i` (which equals `exp (i φ)` on the torus),

so that each of `horizVec` and `meridVec` is a nonvanishing continuous map on the closure of
the corresponding component, with normalised value `exp (i θ)` resp. `exp (i φ)` on `F`.

This file collects the definitions and the elementary continuity facts; the analytic and
geometric lemmas about them are proved in the sibling files.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-! ## The height function and the two projections -/

/-- The squared horizontal radius `x² + y²` of a point of `ℝ³`. -/
def horizRadiusSq (P : R3) : ℝ := P 0 ^ 2 + P 1 ^ 2

/-- The horizontal radius `r = √(x² + y²)` of a point of `ℝ³`. -/
def horizRadius (P : R3) : ℝ := Real.sqrt (horizRadiusSq P)

/-- The height `(r - 2)² + z²`, whose level set `{1}` is the standard torus of revolution. -/
def torusHeight (P : R3) : ℝ := (horizRadius P - 2) ^ 2 + P 2 ^ 2

/-- The horizontal projection `(x, y)` of a point of `ℝ³`, as a complex number. -/
def horizVec (P : R3) : ℂ := ⟨P 0, P 1⟩

/-- The meridian projection `(r - 2, z)` of a point of `ℝ³`, as a complex number. -/
def meridVec (P : R3) : ℂ := ⟨horizRadius P - 2, P 2⟩

@[simp] theorem horizRadiusSq_apply (P : R3) : horizRadiusSq P = P 0 ^ 2 + P 1 ^ 2 := rfl

@[simp] theorem torusHeight_apply (P : R3) :
    torusHeight P = (horizRadius P - 2) ^ 2 + P 2 ^ 2 := rfl

@[simp] theorem horizVec_re (P : R3) : (horizVec P).re = P 0 := rfl

@[simp] theorem horizVec_im (P : R3) : (horizVec P).im = P 1 := rfl

@[simp] theorem meridVec_re (P : R3) : (meridVec P).re = horizRadius P - 2 := rfl

@[simp] theorem meridVec_im (P : R3) : (meridVec P).im = P 2 := rfl

/-- The squared modulus of the horizontal projection is the squared horizontal radius. -/
theorem normSq_horizVec (P : R3) : Complex.normSq (horizVec P) = horizRadiusSq P := by
  rw [Complex.normSq_apply, horizRadiusSq, horizVec_re, horizVec_im]
  ring

/-- The horizontal radius is the modulus of the horizontal projection. -/
theorem norm_horizVec (P : R3) : ‖horizVec P‖ = horizRadius P := by
  rw [horizRadius, show horizRadiusSq P = ‖horizVec P‖ ^ 2 from by
    rw [Complex.sq_norm, normSq_horizVec], Real.sqrt_sq (norm_nonneg _)]

theorem horizRadius_sq (P : R3) : horizRadius P ^ 2 = horizRadiusSq P :=
  Real.sq_sqrt (by rw [horizRadiusSq]; positivity)

theorem horizRadius_nonneg (P : R3) : 0 ≤ horizRadius P := Real.sqrt_nonneg _

/-- The horizontal projection vanishes exactly on the `z`-axis. -/
theorem horizRadius_eq_zero_iff (P : R3) : horizRadius P = 0 ↔ P 0 = 0 ∧ P 1 = 0 := by
  rw [horizRadius, Real.sqrt_eq_zero', horizRadiusSq]
  constructor
  · intro h
    exact ⟨by nlinarith [sq_nonneg (P 0), sq_nonneg (P 1)], by nlinarith [sq_nonneg (P 0), sq_nonneg (P 1)]⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]
    norm_num

theorem horizVec_eq_zero_iff (P : R3) : horizVec P = 0 ↔ horizRadius P = 0 := by
  rw [horizRadius_eq_zero_iff, Complex.ext_iff]
  simp

theorem horizVec_ne_zero_iff (P : R3) : horizVec P ≠ 0 ↔ horizRadius P ≠ 0 :=
  not_iff_not.mpr (horizVec_eq_zero_iff P)

theorem meridVec_eq_zero_iff (P : R3) : meridVec P = 0 ↔ horizRadius P = 2 ∧ P 2 = 0 := by
  rw [Complex.ext_iff]
  simp only [meridVec_re, meridVec_im, Complex.zero_re, Complex.zero_im]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

theorem meridVec_ne_zero_iff (P : R3) : meridVec P ≠ 0 ↔ ¬(horizRadius P = 2 ∧ P 2 = 0) :=
  not_iff_not.mpr (meridVec_eq_zero_iff P)

/-! ## Continuity -/

@[fun_prop] theorem continuous_horizVec : Continuous horizVec := by
  rw [show horizVec = fun P : R3 => (P 0 : ℂ) + (P 1 : ℂ) * Complex.I from
    funext fun P => by apply Complex.ext <;> simp]
  fun_prop

@[fun_prop] theorem continuous_horizRadius : Continuous horizRadius := by
  rw [show horizRadius = fun P : R3 => ‖horizVec P‖ from funext fun P => (norm_horizVec P).symm]
  exact continuous_horizVec.norm

@[fun_prop] theorem continuous_torusHeight : Continuous torusHeight := by
  rw [show torusHeight = fun P : R3 =>
      (horizRadius P - 2) ^ 2 + P 2 ^ 2 from funext fun P => rfl]
  exact ((continuous_horizRadius.sub continuous_const).pow 2).add (by fun_prop)

@[fun_prop] theorem continuous_meridVec : Continuous meridVec := by
  rw [show meridVec = fun P : R3 =>
      ((horizRadius P - 2 : ℝ) : ℂ) + (P 2 : ℂ) * Complex.I from
    funext fun P => by apply Complex.ext <;> simp]
  exact (Complex.continuous_ofReal.comp (continuous_horizRadius.sub continuous_const)).add
    ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun P : R3 => P (2 : Fin 3))).mul
      continuous_const)

/-! ## The normalised horizontal projection -/

/-- The point `w / ‖w‖` of the unit circle attached to a nonzero complex number `w`. -/
def normCircle (w : ℂ) (hw : w ≠ 0) : Circle :=
  ⟨w / (‖w‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [Complex.norm_div]
    simp [norm_ne_zero_iff.mpr hw])⟩

@[simp] theorem normCircle_coe (w : ℂ) (hw : w ≠ 0) :
    (normCircle w hw : ℂ) = w / (‖w‖ : ℂ) := rfl

/-- Normalisation is continuous on the complement of the origin. -/
@[fun_prop] theorem continuous_normCircle {α : Type*} [TopologicalSpace α] (f : α → ℂ) (hf : Continuous f)
    (hne : ∀ x : α, f x ≠ 0) :
    Continuous fun x : α => normCircle (f x) (hne x) := by
  have hcont : Continuous fun x : α => f x / ((‖f x‖ : ℝ) : ℂ) := by
    refine hf.div (Complex.continuous_ofReal.comp hf.norm) ?_
    intro x
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne x))
  have hsub : Continuous fun x : α =>
      (⟨f x / ((‖f x‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
        rw [Complex.norm_div]
        simp [norm_ne_zero_iff.mpr (hne x)])⟩ : Circle) :=
    Continuous.subtype_mk hcont (fun x => mem_sphere_zero_iff_norm.2 (by
      rw [Complex.norm_div]
      simp [norm_ne_zero_iff.mpr (hne x)]))
  exact hsub.congr (fun x => Subtype.ext rfl)

/-- Every point of the unit circle is `circlePoint t` for some `t`. -/
theorem exists_circlePoint_eq (z : ℂ) (hz : ‖z‖ = 1) : ∃ t : ℝ, (circlePoint t : ℂ) = z := by
  obtain ⟨t, ht⟩ := (Complex.norm_eq_one_iff z).mp hz
  exact ⟨t, by rw [circlePoint_coe]; exact ht⟩

end

end Work.CoreTopology
