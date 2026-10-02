import Mathlib
import Submission.Work.ThomBordism.Grassmann.CxFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The diagonal gauge of `zStd ⊗_ℝ ℂ ≅ O(1) ⊕ O(-1)`

On top of `Submission/Work/ThomBordism/Grassmann/CxModel.lean` and `.../CxFibre.lean`:

* `whitneySum_diag_coordChange` — the transition function of `O(1) ⊕ O(-1)` at the diagonal index
  pair is `diagP a a⁻¹`;
* `gaugeFun_inv_ratio`, `gaugeFun_ratio_mul` — the coherence of the squared-norm gauge;
* `gaugeDiag_cMat` — the conjugation identity `gaugeDiag i ∘ cMat a = diagP a a⁻¹ ∘ gaugeDiag i'`,
  the heart of the source- and target-independence of the gauge;
* `gaugeDiag_comp_gaugeDiagInv`, `gaugeDiagInv_comp_gaugeDiag` — the two-sided inverse;
* the continuity of `b ↦ gaugeDiag i b`, `b ↦ gaugeDiagInv i b` on the chart `i`.
-/

open Work.TangentClasses Work.Thom

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## 1. The transition function of `O(1) ⊕ O(-1)` on the diagonal -/

theorem whitneySum_diag_coordChange (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i') :
    (Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)).coordChange
        (i', i') (i, i) b
      = diagP (Work.Gen.homCoord 2 i i' b) ((Work.Gen.homCoord 2 i i' b)⁻¹) := by
  rw [Work.Whitney.whitneySum_coordChange, diagP]
  have h1 : (Work.Gen.tautDual 2).coordChange i' i b
      = (Work.Gen.homCoord 2 i i' b) •
          (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) := by
    rw [Work.Gen.tautDual_coordChange]
    rfl
  have h2 : (Work.Gen.tautLine 2).coordChange i' i b
      = ((Work.Gen.homCoord 2 i i' b)⁻¹) •
          (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) := by
    rw [Work.Gen.tautLine_coordChange, Work.Gen.homCoord_eq_inv_of_mem i i' hb hb']
    rfl
  rw [h1, h2]

/-! ## 2. The coherence of the squared-norm gauge -/

lemma gaugeFun_inv_ratio (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i') :
    ((((Work.Gen.gaugeFun 2 i' b : ℝ)) : ℂ))⁻¹
      = ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))⁻¹ *
        (Work.Gen.homCoord 2 i i' b * star (Work.Gen.homCoord 2 i i' b)) := by
  have hgf : Work.Gen.gaugeFun 2 i b
      = ‖Work.Gen.homCoord 2 i i' b‖ ^ 2 * Work.Gen.gaugeFun 2 i' b :=
    Work.Gen.gaugeFun_homCoord_real (n := 2) i i' hb hb'
  have hane : Work.Gen.homCoord 2 i i' b ≠ 0 := Work.Gen.homCoord_ne_zero_of_mem i i' hb hb'
  have h1 : (((Work.Gen.gaugeFun 2 i' b : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Work.Gen.gaugeFun_pos 2 i' b))
  have hg : ((Work.Gen.gaugeFun 2 i b : ℝ) : ℂ)
      = ((‖Work.Gen.homCoord 2 i i' b‖ ^ 2 : ℝ) : ℂ) *
        ((Work.Gen.gaugeFun 2 i' b : ℝ) : ℂ) := by
    rw [hgf]
    push_cast
    ring
  have hcast : ((‖Work.Gen.homCoord 2 i i' b‖ ^ 2 : ℝ) : ℂ)
      = Work.Gen.homCoord 2 i i' b * star (Work.Gen.homCoord 2 i i' b) :=
    Work.Gen.ofReal_norm_sq_eq_mul_star _
  rw [hg, hcast]
  field_simp [h1, star_ne_zero.mpr hane, hane]

lemma gaugeFun_ratio_mul (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i') :
    ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))⁻¹ * star (Work.Gen.homCoord 2 i i' b)
      = (Work.Gen.homCoord 2 i i' b)⁻¹ *
        ((((Work.Gen.gaugeFun 2 i' b : ℝ)) : ℂ))⁻¹ := by
  have hane : Work.Gen.homCoord 2 i i' b ≠ 0 := Work.Gen.homCoord_ne_zero_of_mem i i' hb hb'
  rw [gaugeFun_inv_ratio i i' hb hb']
  field_simp [hane, star_ne_zero.mpr hane]

/-! ## 3. The diagonal gauge identity -/

theorem gaugeDiag_cMat (i i' : Fin 3) {b : Work.Projective.CP 2}
    (hb : b ∈ Work.Projective.chartSet i) (hb' : b ∈ Work.Projective.chartSet i') :
    (gaugeDiag i b).comp (cMat (Work.Gen.homCoord 2 i i' b))
      = (diagP (Work.Gen.homCoord 2 i i' b)
          ((Work.Gen.homCoord 2 i i' b)⁻¹)).comp (gaugeDiag i' b) := by
  rw [gaugeDiag, gaugeDiag, ContinuousLinearMap.comp_assoc, qMatInv_comp_cMat,
    ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, diagP_comp, diagP_comp,
    one_mul, mul_one, gaugeFun_ratio_mul i i' hb hb']

lemma gaugeDiag_comp_gaugeDiagInv (i : Fin 3) (b : Work.Projective.CP 2) :
    (gaugeDiag i b).comp (gaugeDiagInv i b) = 1 := by
  have hne : ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Work.Gen.gaugeFun_pos 2 i b))
  have hq : ∀ z : EuclideanSpace ℂ (Fin 2), qMatInv (qMat z) = z := by
    intro z
    have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      F z) qMatInv_comp_qMat
    simpa using h
  have hd : ∀ z : EuclideanSpace ℂ (Fin 2),
      diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)⁻¹)
        (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)) z) = z := by
    have hcomp : (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)⁻¹)).comp
        (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))) = 1 := by
      rw [diagP_comp, one_mul, inv_mul_cancel₀ hne, diagP_one]
    intro z
    have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      F z) hcomp
    simpa using h
  apply ContinuousLinearMap.ext
  intro v
  show gaugeDiag i b (gaugeDiagInv i b v) = v
  rw [gaugeDiag, gaugeDiagInv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hq, hd]

lemma gaugeDiagInv_comp_gaugeDiag (i : Fin 3) (b : Work.Projective.CP 2) :
    (gaugeDiagInv i b).comp (gaugeDiag i b) = 1 := by
  have hne : ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Work.Gen.gaugeFun_pos 2 i b))
  have hq : ∀ z : EuclideanSpace ℂ (Fin 2), qMat (qMatInv z) = z := by
    intro z
    have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      F z) qMat_comp_qMatInv
    simpa using h
  have hd : ∀ z : EuclideanSpace ℂ (Fin 2),
      diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))
        (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)⁻¹) z) = z := by
    have hcomp : (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))).comp
        (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)⁻¹)) = 1 := by
      rw [diagP_comp, one_mul, mul_inv_cancel₀ hne, diagP_one]
    intro z
    have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      F z) hcomp
    simpa using h
  apply ContinuousLinearMap.ext
  intro v
  show gaugeDiagInv i b (gaugeDiag i b v) = v
  rw [gaugeDiag, gaugeDiagInv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hd, hq]

/-! ## 4. Continuity of the diagonal gauge -/

lemma diagP_one_apply (ν : ℂ) : diagP 1 ν = (1 - ν) • diagP 1 0 + ν • diagP 1 1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (diagP 1 ν v).ofLp (0 : Fin 2) =
      (((1 - ν) • diagP 1 0 + ν • diagP 1 1) v).ofLp 0
    rw [diagP_ofLp_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, diagP_ofLp_zero,
      diagP_ofLp_one, smul_eq_mul]
    ring
  · show (diagP 1 ν v).ofLp (1 : Fin 2) =
      (((1 - ν) • diagP 1 0 + ν • diagP 1 1) v).ofLp 1
    rw [diagP_ofLp_one, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, diagP_ofLp_zero,
      diagP_ofLp_one, smul_eq_mul]
    ring

lemma continuousOn_diagP_one (i : Fin 3) {χ : Work.Projective.CP 2 → ℂ}
    (hχ : ContinuousOn χ (Work.Projective.chartSet i)) :
    ContinuousOn (fun b : Work.Projective.CP 2 => diagP 1 (χ b))
      (Work.Projective.chartSet i) := by
  have hcont : Continuous fun ν : ℂ =>
      (1 - ν) • (diagP 1 0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) +
        ν • (diagP 1 1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hfun : (fun b : Work.Projective.CP 2 => diagP 1 (χ b))
      = (fun ν : ℂ => (1 - ν) • diagP 1 0 + ν • diagP 1 1) ∘ χ := by
    funext b
    exact diagP_one_apply (χ b)
  rw [hfun]
  exact hcont.comp_continuousOn hχ

lemma continuousOn_gaugeDiag (i : Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => gaugeDiag i b)
      (Work.Projective.chartSet i) := by
  have hχ : ContinuousOn (fun b : Work.Projective.CP 2 =>
      ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ))⁻¹) (Work.Projective.chartSet i) :=
    (Work.Gen.continuousOn_gaugeC (n := 2) i).inv₀ (fun b _ => by
      rw [Work.Gen.gaugeC]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Work.Gen.gaugeFun_pos 2 i b)))
  have h1 := continuousOn_diagP_one i hχ
  have hfun : (fun b : Work.Projective.CP 2 => gaugeDiag i b)
      = fun b => (diagP 1 ((((Work.Gen.gaugeFun 2 i b : ℝ)) : ℂ)⁻¹)).comp qMatInv := by
    funext b
    rw [gaugeDiag]
  rw [hfun]
  exact ContinuousOn.clm_comp h1 continuousOn_const

lemma continuousOn_gaugeDiagInv (i : Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 => gaugeDiagInv i b)
      (Work.Projective.chartSet i) := by
  have h1 := continuousOn_diagP_one i (Work.Gen.continuousOn_gaugeC (n := 2) i)
  have hfun : (fun b : Work.Projective.CP 2 => gaugeDiagInv i b)
      = fun b => qMat.comp (diagP 1 (Work.Gen.gaugeC 2 i b)) := by
    funext b
    rw [gaugeDiagInv]
    rfl
  rw [hfun]
  exact ContinuousOn.clm_comp continuousOn_const h1

end

end Work.ThomBordism.Grassmann
