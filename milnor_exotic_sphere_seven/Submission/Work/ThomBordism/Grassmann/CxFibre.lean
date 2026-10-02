import Mathlib
import Submission.Work.ThomBordism.Grassmann.CxModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The fibre-level identities underlying `zStd ⊗_ℝ ℂ ≅ O(1) ⊕ O(-1)`

This module proves, on top of the definitions of
`Submission/Work/ThomBordism/Grassmann/CxModel.lean`, the three identities of the proof of
`Work.ThomBordism.Grassmann.zStd_complexification_iso`:

* `qMatInv_comp_cMat` — the diagonalisation of the model map `cMat a` in the basis `qMat`;
* `gaugeDiag_cMat` — the conjugation of the model map `cMat a` by the diagonal gauge into
  `diagP a a⁻¹`;
* `cxTrans_zStd_coordChange` — the transition function of `complexificationCore zStd` is the
  conjugation of `cMat` by `Gm`, `GmInv`.
-/

open Work.TangentClasses Work.Thom

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## 1. The bridge `cxTrans (expCMul c) = cMat c` -/

lemma cxOfReal_ofLp {k : ℕ} (w : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (cxOfReal w).ofLp i = ((w.ofLp i : ℝ) : ℂ) := rfl

lemma cxTrans_expCMul (c : ℂ) : cxTrans (expCMul c) = cMat c := by
  refine Work.Thom.cxLinearMap_ext_cxOfReal (j := 2) ?_
  intro u
  rw [Work.Thom.cxTrans_cxOfReal, expCMul_apply]
  ext i
  fin_cases i
  · show (cxOfReal (WithLp.toLp 2 ![c.re * u.ofLp 0 - c.im * u.ofLp 1,
        c.im * u.ofLp 0 + c.re * u.ofLp 1])).ofLp (0 : Fin 2) = (cMat c (cxOfReal u)).ofLp 0
    rw [cMat_ofLp_zero, cxOfReal_ofLp, cxOfReal_ofLp, cxOfReal_ofLp]
    push_cast
    ring
  · show (cxOfReal (WithLp.toLp 2 ![c.re * u.ofLp 0 - c.im * u.ofLp 1,
        c.im * u.ofLp 0 + c.re * u.ofLp 1])).ofLp (1 : Fin 2) = (cMat c (cxOfReal u)).ofLp 1
    rw [cMat_ofLp_one, cxOfReal_ofLp, cxOfReal_ofLp, cxOfReal_ofLp]
    push_cast
    ring

/-! ## 2. The coordinate formulae of the Whitney sum splitting -/

lemma finSumFinEquiv_zero : finSumFinEquiv (Sum.inl (0 : Fin 1)) = (0 : Fin (1 + 1)) := rfl

lemma finSumFinEquiv_one : finSumFinEquiv (Sum.inr (0 : Fin 1)) = (1 : Fin (1 + 1)) := rfl

/-- The first coordinate of the concatenation `Work.Whitney.sumFibreC 1 1`. -/
lemma sumFibreC_fst_coord (x y : EuclideanSpace ℂ (Fin 1)) :
    ((Work.Whitney.sumFibreC 1 1) (x, y)).ofLp 0 = x.ofLp 0 := by
  have h := Work.Thom.finAddEquivProd_symm_apply_inl (𝕜 := ℂ) (n := 1) (m := 1) x y (0 : Fin 1)
  simpa [Work.Whitney.sumFibreC, finSumFinEquiv_zero] using h

/-- The second coordinate of the concatenation `Work.Whitney.sumFibreC 1 1`. -/
lemma sumFibreC_snd_coord (x y : EuclideanSpace ℂ (Fin 1)) :
    ((Work.Whitney.sumFibreC 1 1) (x, y)).ofLp 1 = y.ofLp 0 := by
  have h := Work.Thom.finAddEquivProd_symm_apply_inr (𝕜 := ℂ) (n := 1) (m := 1) x y (0 : Fin 1)
  simpa [Work.Whitney.sumFibreC, finSumFinEquiv_one] using h

/-- The first half of the splitting `Work.Whitney.sumFibreC 1 1`. -/
lemma sumFibreC_symm_fst (v : EuclideanSpace ℂ (Fin 2)) :
    (((Work.Whitney.sumFibreC 1 1).symm v).1).ofLp 0 = v.ofLp 0 := by
  have h := Work.Thom.finAddEquivProd_fst (𝕜 := ℂ) (n := 1) (m := 1) v (0 : Fin 1)
  simpa [Work.Whitney.sumFibreC, finSumFinEquiv_zero] using h

/-- The second half of the splitting `Work.Whitney.sumFibreC 1 1`. -/
lemma sumFibreC_symm_snd (v : EuclideanSpace ℂ (Fin 2)) :
    (((Work.Whitney.sumFibreC 1 1).symm v).2).ofLp 0 = v.ofLp 1 := by
  have h := Work.Thom.finAddEquivProd_snd (𝕜 := ℂ) (n := 1) (m := 1) v (0 : Fin 1)
  simpa [Work.Whitney.sumFibreC, finSumFinEquiv_one] using h

/-- `diagP` is the diagonal scaling in the coordinates of `ℂ²`. -/
lemma diagP_eq_diag2 (μ ν : ℂ) : diagP μ ν = diag2 μ ν := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (diagP μ ν v).ofLp (0 : Fin 2) = (diag2 μ ν v).ofLp 0
    rw [diag2_ofLp_zero, diagP]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, sumFibreC_fst_coord,
      sumFibreC_symm_fst, smul_eq_mul]
    rfl
  · show (diagP μ ν v).ofLp (1 : Fin 2) = (diag2 μ ν v).ofLp 1
    rw [diag2_ofLp_one, diagP]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, sumFibreC_snd_coord,
      sumFibreC_symm_snd, smul_eq_mul]
    rfl

lemma diagP_ofLp_zero (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (diagP μ ν v).ofLp 0 = μ * v.ofLp 0 := by
  rw [diagP_eq_diag2, diag2_ofLp_zero]

lemma diagP_ofLp_one (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (diagP μ ν v).ofLp 1 = ν * v.ofLp 1 := by
  rw [diagP_eq_diag2, diag2_ofLp_one]

/-! ## 3. The algebra of `diagP` and `qMat` -/

lemma diagP_comp (μ ν μ' ν' : ℂ) :
    (diagP μ ν).comp (diagP μ' ν') = diagP (μ * μ') (ν * ν') := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show ((diagP μ ν) ((diagP μ' ν') v)).ofLp (0 : Fin 2) = (diagP (μ * μ') (ν * ν') v).ofLp 0
    rw [diagP_ofLp_zero, diagP_ofLp_zero, diagP_ofLp_zero]
    ring
  · show ((diagP μ ν) ((diagP μ' ν') v)).ofLp (1 : Fin 2) = (diagP (μ * μ') (ν * ν') v).ofLp 1
    rw [diagP_ofLp_one, diagP_ofLp_one, diagP_ofLp_one]
    ring

lemma diagP_one : diagP 1 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (diagP 1 1 v).ofLp (0 : Fin 2) = v.ofLp 0
    rw [diagP_ofLp_zero]
    simp
  · show (diagP 1 1 v).ofLp (1 : Fin 2) = v.ofLp 1
    rw [diagP_ofLp_one]
    simp

lemma qMatInv_comp_qMat : qMatInv.comp qMat = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (qMatInv (qMat v)).ofLp (0 : Fin 2) = v.ofLp 0
    rw [qMatInv_ofLp_zero, qMat_ofLp_zero, qMat_ofLp_one]
    ring_nf
    rw [Complex.I_sq]
    ring
  · show (qMatInv (qMat v)).ofLp (1 : Fin 2) = v.ofLp 1
    rw [qMatInv_ofLp_one, qMat_ofLp_zero, qMat_ofLp_one]
    ring_nf
    rw [Complex.I_sq]
    ring

lemma qMat_comp_qMatInv : qMat.comp qMatInv = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (qMat (qMatInv v)).ofLp (0 : Fin 2) = v.ofLp 0
    rw [qMat_ofLp_zero, qMatInv_ofLp_zero, qMatInv_ofLp_one]
    ring_nf
  · show (qMat (qMatInv v)).ofLp (1 : Fin 2) = v.ofLp 1
    rw [qMat_ofLp_one, qMatInv_ofLp_zero, qMatInv_ofLp_one]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- **Diagonalisation of the model map `cMat a`** in the basis `qMat` of eigenvectors
`(1, ∓i)`: `qMatInv ∘ cMat a = diagP a (star a) ∘ qMatInv`. -/
theorem qMatInv_comp_cMat (a : ℂ) :
    qMatInv.comp (cMat a) = (diagP a (star a)).comp qMatInv := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (qMatInv (cMat a v)).ofLp (0 : Fin 2) =
      ((diagP a (star a)) (qMatInv v)).ofLp 0
    rw [qMatInv_ofLp_zero, cMat_ofLp_zero, cMat_ofLp_one, diagP_ofLp_zero, qMatInv_ofLp_zero]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  · show (qMatInv (cMat a v)).ofLp (1 : Fin 2) =
      ((diagP a (star a)) (qMatInv v)).ofLp 1
    rw [qMatInv_ofLp_one, cMat_ofLp_zero, cMat_ofLp_one, diagP_ofLp_one, qMatInv_ofLp_one]
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im] <;>
      ring


/-! ## 4. The inverse identities of `Gm`, `GmInv` and the functoriality identity -/

lemma Gm_comp_GmInv : Gm.comp GmInv = 1 := by
  rw [Gm, GmInv, ← Work.Thom.cxTrans_comp]
  have h : ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
      (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))).comp
      ((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [h, Work.Thom.cxTrans_one]

lemma GmInv_comp_Gm : GmInv.comp Gm = 1 := by
  rw [Gm, GmInv, ← Work.Thom.cxTrans_comp]
  have h : ((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
      (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))).comp
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [h, Work.Thom.cxTrans_one]

/-- The transition functions of `zStd` are the realifications of the complex multiplications by the
homogeneous coordinate ratios. -/
lemma zStd_coordChange_eq (i j : Fin 3) (b : Work.Projective.CP 2) :
    zStd.coordChange i j b =
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        ((cmulLM (Work.Gen.homCoord 2 j i b)).comp
          (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))) := by
  rw [show zStd.coordChange i j b =
      (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        (((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b).comp
          (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))) from
    RealBundle.mapFibre_coordChange equivC1R2 (Work.Thom.realification (Work.Gen.tautDual 2)) i j b]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, Work.Thom.realification_coordChange,
    Work.Gen.tautDual_coordChange]
  rfl

/-- **The transition function of `complexificationCore zStd` is the conjugation of `cMat`**:
`cxTrans (zStd.coordChange i j b) = Gm ∘ cMat (homCoord 2 j i b) ∘ GmInv`. -/
theorem cxTrans_zStd_coordChange (i j : Fin 3) (b : Work.Projective.CP 2) :
    Work.Thom.cxTrans (zStd.coordChange i j b)
      = Gm.comp ((cMat (Work.Gen.homCoord 2 j i b)).comp GmInv) := by
  have hcomp : ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
      ((cmulLM (Work.Gen.homCoord 2 j i b)).comp
        (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))) =
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
          (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))).comp
        ((((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
          ((cmulLM (Work.Gen.homCoord 2 j i b)).comp
            (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))))).comp
          ((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
            (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [zStd_coordChange_eq, hcomp, Work.Thom.cxTrans_comp, Work.Thom.cxTrans_comp]
  have hB : Work.Thom.cxTrans
      (((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        ((cmulLM (Work.Gen.homCoord 2 j i b)).comp
          (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))))
      = cMat (Work.Gen.homCoord 2 j i b) := cxTrans_expCMul _
  rw [hB]
  rfl

end

end Work.ThomBordism.Grassmann
