import Mathlib
import Submission.Work.Milnor.MorseFun
import Submission.Work.Milnor.ChartDefs
import Submission.Work.Milnor.eta_facts
import Submission.Work.Milnor.hfun_facts
import Submission.Work.Milnor.stereo_chart_re
import Submission.Work.Milnor.sphere_re_defs
import Submission.Work.Milnor.morseChart_contMDiff

set_option synthInstance.maxHeartbeats 400000

/-!
# `morseChart1` has no critical points

The chart-1 expression of Milnor's Morse function on `Mk (-2)` is

`morseChart1 (x, y) = Re(ĥ x * y) / √(1 + ‖x‖²)`,

with `ĥ = Quaternion.linearIsometryEquivTuple.symm : ℝ⁴ → ℍ`.  This file shows that its
manifold derivative never vanishes.

The derivative splits, through `mfderiv_prod_eq_add_apply`, into a base part

`A = mfderiv (z ↦ morseChart1 (z, y)) x = (Re(ĥ x * y) * ceta x) • innerSL x + eta x • β`

and a fibre part.  The key observation is that the single fixed base direction
`v = ĥ⁻¹(ȳ) = Quaternion.linearIsometryEquivTuple (star y)` already gives a strictly positive
value `A v = (1 + ‖x‖²)^(-3/2) * ((1 + ‖x‖²) - ⟪x,v⟫²) > 0`, because `⟪x,v⟫² ≤ ‖x‖²` while
`Re(ĥ x * y) = ⟪x, v⟫` and `‖v‖ = 1`.  So one never needs to look at the fibre direction, and no
case analysis is required.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set
open Submission.Milnor

namespace Work.Milnor

noncomputable section

/-- The continuous linear functional `z ↦ Re(ĥ z * y)` on `E4 = ℝ⁴`. -/
def beta (y : Quaternion ℝ) : E4 →L[ℝ] ℝ where
  toFun z := (Quaternion.linearIsometryEquivTuple.symm z * y).re
  map_add' z w := by rw [LinearIsometryEquiv.map_add, add_mul, Quaternion.re_add]
  map_smul' c z := by
    rw [LinearIsometryEquiv.map_smul, smul_mul_assoc, Quaternion.re_smul]; rfl
  cont := by
    refine Quaternion.continuous_re.comp ?_
    exact continuous_mul.comp
      (Continuous.prodMk Quaternion.linearIsometryEquivTuple.symm.continuous continuous_const)

lemma beta_apply (y : Quaternion ℝ) (z : E4) :
    beta y z = (Quaternion.linearIsometryEquivTuple.symm z * y).re := by
  simp only [beta, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]

/-- The explicit value of the differential of `z ↦ morseChart1 (z, y)` at `x`. -/
def baseDeriv (x : E4) (y : QS3) : E4 →L[ℝ] ℝ :=
  (((Quaternion.linearIsometryEquivTuple.symm x * (y : Quaternion ℝ)).re) • ceta x • innerSL ℝ x)
    + eta x • beta (y : Quaternion ℝ)

/-- `baseDeriv` is the Fréchet derivative of the base slice of `morseChart1`. -/
lemma hasFDerivAt_chart1_fst (x : E4) (y : QS3) :
    HasFDerivAt (fun z : E4 => morseChart1 (z, y)) (baseDeriv x y) x := by
  unfold baseDeriv
  have hnum : HasFDerivAt
      (fun z : E4 => (Quaternion.linearIsometryEquivTuple.symm z * (y : Quaternion ℝ)).re)
      (beta (y : Quaternion ℝ)) x := by
    simpa only [beta, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using
      ContinuousLinearMap.hasFDerivAt (beta (y : Quaternion ℝ))
  have heta : HasFDerivAt eta (ceta x • innerSL ℝ x) x := hasFDerivAt_eta x
  have hmul := hnum.mul heta
  rw [show (fun z : E4 => morseChart1 (z, y)) =
      (fun z : E4 => (Quaternion.linearIsometryEquivTuple.symm z * (y : Quaternion ℝ)).re
        * eta z) from by
    funext z; rw [morseChart1_eq]; simp [Gfun1, Hfun]]
  exact hmul

/-- Evaluation of `baseDeriv` on a vector. -/
lemma baseDeriv_apply (x : E4) (y : QS3) (v : E4) :
    baseDeriv x y v
      = (Quaternion.linearIsometryEquivTuple.symm x * (y : Quaternion ℝ)).re * ceta x * ⟪x, v⟫
        + eta x * beta (y : Quaternion ℝ) v := by
  simp only [baseDeriv, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem morseChart1_nocrit (p : Submission.Milnor.MSpace) :
    mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      (modelWithCornersSelf ℝ ℝ) Submission.Milnor.morseChart1 p ≠ 0 := by
  obtain ⟨x, y⟩ := p
  intro hzero
  -- The model-with-corners abbreviations used below.
  set v : E4 := Quaternion.linearIsometryEquivTuple (star (y : Quaternion ℝ)) with hv
  have hvcoeff : Quaternion.linearIsometryEquivTuple.symm v = star (y : Quaternion ℝ) := by
    rw [hv]; exact LinearIsometryEquiv.symm_apply_apply _ _
  -- Smoothness.
  have hmd : MDifferentiableAt
      ((modelWithCornersSelf ℝ E4).prod (modelWithCornersSelf ℝ E3))
      (modelWithCornersSelf ℝ ℝ) morseChart1 (x, y) :=
    morseChart_contMDiff.1.mdifferentiableAt (by simp)
  -- The base slice derivative is `baseDeriv`.
  have hAeq : mfderiv (modelWithCornersSelf ℝ E4) (modelWithCornersSelf ℝ ℝ)
      (fun z : E4 => morseChart1 (z, y)) x = baseDeriv x y := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_chart1_fst x y).fderiv
  -- Splitting of the total derivative along the direction `(v, 0)`.
  have hsplit : (mfderiv ((modelWithCornersSelf ℝ E4).prod (modelWithCornersSelf ℝ E3))
      (modelWithCornersSelf ℝ ℝ) Submission.Milnor.morseChart1 (x, y)) (v, (0 : E3))
      = baseDeriv x y v := by
    have h := mfderiv_prod_eq_add_apply (I := modelWithCornersSelf ℝ E4)
      (I' := modelWithCornersSelf ℝ E3) (I'' := modelWithCornersSelf ℝ ℝ)
      (f := morseChart1) (p := (x, y)) (v := (v, (0 : E3))) hmd
    have hB : (mfderiv (modelWithCornersSelf ℝ E3) (modelWithCornersSelf ℝ ℝ)
        (fun z : QS3 => morseChart1 (x, z)) y) (0 : E3) = 0 := map_zero _
    rw [hAeq, hB, add_zero] at h
    exact h
  have hv0 : baseDeriv x y v = 0 := by
    rw [← hsplit, hzero]
    rfl
  -- `⟪x, v⟫` bounds.
  have hv1 : ‖v‖ = 1 := by
    rw [hv, Quaternion.linearIsometryEquivTuple.norm_map, Quaternion.norm_star,
      Submission.Milnor.norm_coe]
  have hp2le : (⟪x, v⟫ : ℝ) ^ 2 ≤ ‖x‖ ^ 2 := by
    have h1 : |(⟪x, v⟫ : ℝ)| ≤ ‖x‖ := by
      simpa [hv1] using abs_real_inner_le_norm x v
    calc (⟪x, v⟫ : ℝ) ^ 2 = |(⟪x, v⟫ : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- `Re(ĥ x * y) = ⟪x, v⟫`.
  have hbp : (Quaternion.linearIsometryEquivTuple.symm x * (y : Quaternion ℝ)).re
      = (⟪x, v⟫ : ℝ) := by
    have h1 : (Quaternion.linearIsometryEquivTuple.symm x * (y : Quaternion ℝ)).re
        = ⟪Quaternion.linearIsometryEquivTuple.symm x, star (y : Quaternion ℝ)⟫ := by
      rw [Quaternion.inner_def, star_star]
    rw [h1, ← hvcoeff]
    exact LinearIsometryEquiv.inner_map_map _ x v
  -- `beta y v = 1`.
  have hbeta1 : beta (y : Quaternion ℝ) v = 1 := by
    rw [beta_apply, hvcoeff]
    have h2 : (star (y : Quaternion ℝ) * (y : Quaternion ℝ)).re
        = ⟪(y : Quaternion ℝ), (y : Quaternion ℝ)⟫ := by
      rw [Quaternion.inner_def]; exact re_mul_comm _ _
    rw [h2, Quaternion.inner_self, Quaternion.normSq_eq_norm_mul_self,
      Submission.Milnor.norm_coe]
    norm_num
  -- Explicit positivity.
  have hU : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hval : baseDeriv x y v
      = (1 + ‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) * ((1 + ‖x‖ ^ 2) - (⟪x, v⟫ : ℝ) ^ 2) := by
    rw [baseDeriv_apply, hbp, hbeta1, ceta, eta_eq_rpow]
    have hbase : (1 + ‖x‖ ^ 2) ^ (-(1 / 2 : ℝ))
        = (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) := by
      have h := Real.rpow_add hU (1 : ℝ) (-(3 / 2 : ℝ))
      rw [Real.rpow_one, show (1 : ℝ) + -(3 / 2) = -(1 / 2) by norm_num] at h
      exact h
    rw [hbase]; ring
  have hfinal : 0 < baseDeriv x y v := by
    rw [hval]
    apply mul_pos
    · exact Real.rpow_pos_of_pos hU _
    · linarith [hp2le]
  exact (ne_of_gt hfinal) hv0

end

end Work.Milnor
