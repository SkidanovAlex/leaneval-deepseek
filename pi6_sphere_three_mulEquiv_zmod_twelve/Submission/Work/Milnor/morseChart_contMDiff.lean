import Mathlib
import Submission.Work.Milnor.MorseFun
import Submission.Work.Quaternion.clutch_smooth

set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the two chart expressions of Milnor's Morse function

The two functions `morseChart1`, `morseChart2 : MSpace → ℝ` (see `Submission.Work.Milnor.MorseFun`)
are the coordinate expressions, in the two charts of `Mk k`, of the function exhibiting the two
critical points of Milnor's Morse function.  This file shows that both are `C^∞`.

Everything is proved by composing smooth pieces:

* the projections `p ↦ p.1 : ℝ⁴ × S³ → ℝ⁴` and `p ↦ p.2 : ℝ⁴ × S³ → S³`,
* the inclusion `S³ ↪ ℍ` of the unit sphere into the quaternions (`contMDiff_coe_sphere`),
* `Quaternion.linearIsometryEquivTuple.symm : ℝ⁴ → ℍ` (a linear isometry, hence smooth),
* quaternion multiplication (the `ContMDiffMul` instance of `Work.Quaternion.clutch_smooth`),
* the real part `ℍ → ℝ` (a continuous linear map, hence smooth),
* `x ↦ 1 + ‖x‖²` on `ℝ⁴` (via `contDiff_norm_sq`), and
* `Real.sqrt` on `(0,∞) ⊆ ℝ`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set
open Submission.Milnor

noncomputable section

/-- The real part of a quaternion, as a continuous linear map. -/
def quatReCLM : Quaternion ℝ →L[ℝ] ℝ where
  toFun := fun q => q.re
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := Quaternion.continuous_re

/-- The real part is smooth. -/
lemma contMDiff_quat_re : ContMDiff 𝓘(ℝ, Quaternion ℝ) 𝓘(ℝ, ℝ) ∞ ⇑quatReCLM :=
  quatReCLM.contMDiff

/-- `Quaternion.linearIsometryEquivTuple.symm : ℝ⁴ → ℍ` is smooth. -/
lemma contMDiff_quat_symm_tuple :
    ContMDiff (𝓡 4) 𝓘(ℝ, Quaternion ℝ) ∞
      (Quaternion.linearIsometryEquivTuple.symm : EuclideanSpace ℝ (Fin 4) → Quaternion ℝ) :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff

/-- On the positive reals, `Real.sqrt` is smooth. -/
lemma contMDiffOn_sqrt : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.sqrt (Ioi 0) := by
  rw [contMDiffOn_iff_contDiffOn]
  simpa using (contDiffOn_id (𝕜 := ℝ) (s := Ioi 0)).sqrt (fun x hx => ne_of_gt hx)

/-- The map `p ↦ ‖p.1‖ ^ 2` on `ℝ⁴ × S³` is smooth (`x ↦ ‖x‖²` is smooth even though `x ↦ ‖x‖`
is not). -/
lemma contMDiff_normSq_fst :
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ (fun p : MSpace => ‖p.1‖ ^ 2) := by
  have h : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_norm_sq ℝ
  exact h.comp contMDiff_fst

/-- The denominator `p ↦ Real.sqrt (1 + ‖p.1‖²)` of both chart expressions is smooth. -/
lemma contMDiff_chartDen :
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : MSpace => Real.sqrt (1 + ‖p.1‖ ^ 2)) := by
  have harg : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ (fun p : MSpace => 1 + ‖p.1‖ ^ 2) :=
    contMDiff_const.add contMDiff_normSq_fst
  exact contMDiffOn_sqrt.comp_contMDiff harg fun p => by
    show (0 : ℝ) < 1 + ‖p.1‖ ^ 2
    positivity

/-- The quaternion-valued numerator of `morseChart1` is smooth. -/
lemma contMDiff_chartNum1 :
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => Quaternion.linearIsometryEquivTuple.symm p.1 * (p.2 : Quaternion ℝ)) :=
  (contMDiff_quat_symm_tuple.comp contMDiff_fst).mul
    (contMDiff_coe_sphere.comp contMDiff_snd)

open scoped Manifold ContDiff Topology in
open TopologicalSpace Set in
open Submission.Milnor in
theorem morseChart_contMDiff :
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ morseChart1 ∧
    ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ morseChart2 := by
  have hcoe : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => (p.2 : Quaternion ℝ)) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hden_ne : ∀ p : MSpace, Real.sqrt (1 + ‖p.1‖ ^ 2) ≠ 0 := fun p =>
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hnum1 : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : MSpace =>
        (Quaternion.linearIsometryEquivTuple.symm p.1 * (p.2 : Quaternion ℝ)).re) :=
    contMDiff_quat_re.comp contMDiff_chartNum1
  have hnum2 : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : MSpace => (p.2 : Quaternion ℝ).re) :=
    contMDiff_quat_re.comp hcoe
  refine ⟨?_, ?_⟩
  · refine (hnum1.div₀ contMDiff_chartDen hden_ne).congr fun p => ?_
    rfl
  · refine (hnum2.div₀ contMDiff_chartDen hden_ne).congr fun p => ?_
    rfl

end

end Work.Milnor
