import Mathlib
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.genFunctionalStable
import Submission.Work.Drive.classTripleRegular

/-!
# Re-basing the class level rows of the ends clause, and the level coordinate

This module records the two structural facts that turn the *existing* one-point producers of the class
level rows (`Work.Drive.exists_hendL012_row_chartPert`, `Work.Drive.exists_classRows345_design`,
`Work.Drive.endTripleReg_blockPlane_of_designMeet3_unrestricted`, `Work.Drive.pairReg_...`) into
*density at every point* statements for the class-row family `Work.Drive.ClassRowFamily`.

## 1. The level coordinate of `chartPert` is invisible to the class maps

`Work.Drive.chartPert t` acts on the capping space by `(level, class) ↦ (levelScale t, classMap t)`, and
`classGen t = (t 1) • genI + (t 2) • genJ + (t 3) • genK` *only sees the coordinates `1,2,3`* (already
observed as `Work.Drive.classEval_smul_e0`).  Hence

* `classGen (a • e₀) = 0`, `classEquiv (a • e₀) = 1`, `classMap (a • e₀) = id`;
* `classMap (t + a • e₀) = classMap t`,

so every `PairReg`/`EndTripleReg` condition of the ends clause — and `Work.Drive.classTripleSet` itself —
is a function of the *class coordinates* `(blk k t) 1, (blk k t) 2, (blk k t) 3` of the design parameter
alone.

## 2. Re-basing: `classEquiv` is additive up to a *second order* term

`classEquiv t = 1 + classGen t` and `classGen` is additive, so for the composite of two perturbations

> `(classEquiv (a + b) : 𝔼³ →L[ℝ] 𝔼³) - classEquiv a * classEquiv b = -(classGen a * classGen b)`,

whose norm is `≤ (classGenC)² ‖a‖ ‖b‖` (`Work.Drive.classEquiv_add_sub_mul_norm_le`).  Consequently
`classMap (a + b)` and `classMap a ∘ classMap b` differ by `O (‖a‖ ‖b‖)`: *re-basing the parameter at an
arbitrary `χ` and letting the perturbation `σ` tend to `0` makes the re-based presentation
`chartPert σ ∘ chartPert χ` converge (as a class map) to `chartPert (χ + σ)`.  This is the mechanism by
which a producer of a class level row *at `σ` near `0`* for the *re-based presentations*
`chartPert χ k ∘ P k` yields the same row for the *design's* presentations at the nearby parameter
`t = χ + σ` — i.e. density of the row set at every base point `χ`, with no new genericity input.
See `CLASSROWS_DENSITY_MECHANISM.md`.
-/

namespace Work.Drive

open scoped Topology
open Set

noncomputable section

/-- **The class map of a chart-perturbed presentation** (a local copy of the lane's lemma, so that this
module needs only the definition file `classTripleRegular`). -/
theorem planeClassMap_chartPert_comp_rb (τ : Eucl 3)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    planeClassMap (fun y => chartPert τ (P y)) = classMap τ ∘ planeClassMap P := by
  funext y
  simp only [Function.comp_apply, planeClassMap, cappingSpaceHomeoProj_chartPert, coordFam_snd]


/-! ## 1. The level coordinate is invisible to the class map -/

/-- **The class generator is additive in its parameter** (it is the linear map `classEval`). -/
lemma classGen_add (a b : Eucl 3) : classGen (a + b) = classGen a + classGen b := by
  ext v
  rw [ContinuousLinearMap.add_apply, classGen_apply, classGen_apply, classGen_apply]
  simp only [PiLp.add_apply, add_smul]
  abel

/-- **The class generator is constant along the first (`level`) coordinate.** -/
lemma classGen_smul_e0 (a : ℝ) : classGen (a • (e0 : Eucl 3)) = 0 := by
  ext v
  rw [← classEval_apply v (a • e0), classEval_smul_e0]
  rfl

/-- The class equivalence of a pure level perturbation is the identity. -/
lemma classEquiv_smul_e0 (a : ℝ) :
    (classEquiv (a • (e0 : Eucl 3)) : Eucl 3 →L[ℝ] Eucl 3) = 1 := by
  rw [show (classEquiv (a • (e0 : Eucl 3)) : Eucl 3 →L[ℝ] Eucl 3)
        = 1 + classGen (a • (e0 : Eucl 3)) from by
      rw [← classEquiv_coe_sub_one (a • (e0 : Eucl 3))]; abel,
    classGen_smul_e0, add_zero]

/-- **The class map ignores the first (`level`) coordinate.** -/
theorem classMap_add_smul_e0 (t : Eucl 3) (a : ℝ) :
    classMap (t + a • (e0 : Eucl 3)) = classMap t := by
  have hpt : ∀ v : Eucl 3, classEquiv (t + a • (e0 : Eucl 3)) v = classEquiv t v := by
    intro v
    rw [classEquiv_apply, classEquiv_apply, classGen_add, classGen_smul_e0]
    simp
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
      rw [classMap_mk, classMap_mk]
      refine (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr ⟨1, ?_⟩
      simpa using (hpt v).symm

/-- **The level-independence of a perturbed presentation's class map.**  Composing a presentation with
`chartPert t` and with `chartPert (t + a • e₀)` gives the same class map (the second only rescales the
levels). -/
theorem planeClassMap_chartPert_add_smul_e0
    (t : Eucl 3) (a : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    planeClassMap (fun y => chartPert (t + a • (e0 : Eucl 3)) (P y))
      = planeClassMap (fun y => chartPert t (P y)) := by
  rw [planeClassMap_chartPert_comp_rb, planeClassMap_chartPert_comp_rb, classMap_add_smul_e0]


/-! ## 2. The re-basing discrepancy -/

/-- **The composite of two class equivalences against the class equivalence of the sum.**  Since
`classEquiv t = 1 + classGen t` and `classGen` is additive, the difference is the *product* of the two
generators (a second order term). -/
theorem classEquiv_add_sub_mul (a b : Eucl 3) :
    (classEquiv (a + b) : Eucl 3 →L[ℝ] Eucl 3)
      - (classEquiv a : Eucl 3 →L[ℝ] Eucl 3) * (classEquiv b : Eucl 3 →L[ℝ] Eucl 3)
      = -(classGen a * classGen b) := by
  have ha : (classEquiv a : Eucl 3 →L[ℝ] Eucl 3) = 1 + classGen a := by
    rw [← classEquiv_coe_sub_one a]; abel
  have hb : (classEquiv b : Eucl 3 →L[ℝ] Eucl 3) = 1 + classGen b := by
    rw [← classEquiv_coe_sub_one b]; abel
  have hab : (classEquiv (a + b) : Eucl 3 →L[ℝ] Eucl 3) = 1 + classGen (a + b) := by
    rw [← classEquiv_coe_sub_one (a + b)]; abel
  rw [ha, hb, hab, classGen_add]
  noncomm_ring

/-- **The norm of the re-basing discrepancy** is `O (‖a‖ ‖b‖)`, with the explicit constant
`(classGenC)²`. -/
theorem classEquiv_add_sub_mul_norm_le (a b : Eucl 3) :
    ‖(classEquiv (a + b) : Eucl 3 →L[ℝ] Eucl 3)
      - (classEquiv a : Eucl 3 →L[ℝ] Eucl 3) * (classEquiv b : Eucl 3 →L[ℝ] Eucl 3)‖
      ≤ classGenC ^ 2 * ‖a‖ * ‖b‖ := by
  rw [classEquiv_add_sub_mul, norm_neg]
  calc ‖classGen a * classGen b‖ ≤ ‖classGen a‖ * ‖classGen b‖ := norm_mul_le _ _
    _ ≤ (classGenC * ‖a‖) * (classGenC * ‖b‖) := by
        exact mul_le_mul (classGen_norm_le a) (classGen_norm_le b) (norm_nonneg _) (by
          have := classGenC_nonneg; positivity)
    _ = classGenC ^ 2 * ‖a‖ * ‖b‖ := by ring

end

end Work.Drive
