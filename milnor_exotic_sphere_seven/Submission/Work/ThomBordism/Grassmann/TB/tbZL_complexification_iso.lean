import Mathlib
import Submission.Work.ThomBordism.Grassmann.TB.tbGaugeTrans
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.ConjLine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-!
# Complexification of the block bundle `tbZL`

`tbZL = RealBundle.mapFibre expC (realification (tautLine 4))` is the realification of the
tautological line bundle of `ℂP⁴` (with the fibre identified with `ℝ²` through `expC`).  This file
proves that its complexification is the rank-`2` complex bundle `O(-1) ⊕ \overline{O(-1)}`:

`complexificationCore tbZL ≅ whitneySum (tautLine 4) (conjLine 4)`.

## The proof

Because `tbZL` is defined through the *explicit* identification `expC`, its transition function is
`tbZL.coordChange i j x = expCMul (homCoord 4 i j x)` (`TB.tbGaugeTrans.tbgZL_coordChange`), so the
complexification's transition function is

  `(complexificationCore tbZL).coordChange i j x = cxTrans (expCMul (homCoord 4 i j x))
    = cMat (homCoord 4 i j x)`   (`cxTrans_expCMul`),

the explicit real `2 × 2` matrix `[[Re, -Im],[Im, Re]]`.  The target `O(-1) ⊕ \overline{O(-1)}` has
the diagonal transition `diagP a (star a)`, and `qMatInv ∘ cMat a = diagP a (star a) ∘ qMatInv`
(`qMatInv_comp_cMat`) — the diagonalisation in the eigenbasis `(1, ∓i)`.  Hence the *constant* gauge

  `Φ i t x = (O(-1) ⊕ \overline{O(-1)}).coordChange (i, i) t x ∘ qMatInv`,
  `Φinv i t x = qMat ∘ (O(-1) ⊕ \overline{O(-1)}).coordChange t (i, i) x`

satisfies the eight hypotheses of `Work.Thom.nonempty_bundleIso_of_gauge`: the target- and
source-independence are the cocycle of the target bundle together with the diagonalisation, and the
two-sided inverse is `qMat ∘ qMatInv = 1`, `qMatInv ∘ qMat = 1`.
-/

namespace Work.ThomBordism.Grassmann.TB

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## 1. The target bundle `O(-1) ⊕ \overline{O(-1)}` -/

/-- The target bundle `O(-1) ⊕ \overline{O(-1)}` over `ℂP⁴`. -/
abbrev tbTX : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 5 × Fin 5) :=
  Work.Whitney.whitneySum (Work.Gen.tautLine 4) (Work.Gen.conjLine 4)

theorem tbTX_baseSet (t : Fin 5 × Fin 5) :
    tbTX.baseSet t = Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2 := by
  rw [tbTX, Work.Whitney.whitneySum_baseSet, Work.Gen.tautLine_baseSet,
    Work.Gen.conjLine_baseSet]

/-- **The transition function of `tbTX`** is the diagonal of the two line-bundle transitions. -/
theorem tbTX_coordChange (t t' : Fin 5 × Fin 5) (x : CP 4) :
    tbTX.coordChange t t' x
      = diagP (Work.Gen.homCoord 4 t.1 t'.1 x) (star (Work.Gen.homCoord 4 t.2 t'.2 x)) := by
  rw [tbTX, Work.Whitney.whitneySum_coordChange, Work.Gen.tautLine_coordChange,
    Work.Gen.conjLine_coordChange, diagP]
  simp only [ContinuousLinearMap.one_def]

/-! ## 2. The complexification of `tbZL` and its transition function -/

theorem complexificationCore_tbZL_baseSet (i : Fin 5) :
    (Work.Thom.complexificationCore tbZL).baseSet i = Work.Projective.chartSet i := by
  rw [Work.Thom.complexificationCore_baseSet, tbZL, RealBundle.mapFibre_baseSet,
    Work.Thom.realification_baseSet, Work.Gen.tautLine_baseSet]

/-- **The transition function of `complexificationCore tbZL`** is the explicit real `2 × 2` matrix
`cMat (homCoord 4 i j x)`. -/
theorem complexificationCore_tbZL_coordChange (i j : Fin 5) (x : CP 4) :
    (Work.Thom.complexificationCore tbZL).coordChange i j x
      = cMat (Work.Gen.homCoord 4 i j x) := by
  rw [show (Work.Thom.complexificationCore tbZL).coordChange i j x
      = Work.Thom.cxTrans (tbZL.coordChange i j x) from rfl,
    Work.ThomBordism.Grassmann.TBG.tbgZL_coordChange i j x, cxTrans_expCMul]

/-! ## 3. The pointwise algebra of `qMat`, `qMatInv`, `cMat`, `diagP` -/

lemma qMat_qMatInv_apply (z : EuclideanSpace ℂ (Fin 2)) : qMat (qMatInv z) = z := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F z)
    qMat_comp_qMatInv
  simpa using h

lemma qMatInv_qMat_apply (z : EuclideanSpace ℂ (Fin 2)) : qMatInv (qMat z) = z := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F z)
    qMatInv_comp_qMat
  simpa using h

lemma qMatInv_cMat_apply (a : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    qMatInv (cMat a v) = diagP a (star a) (qMatInv v) := by
  have h := congrArg (fun F : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) => F v)
    (qMatInv_comp_cMat a)
  simpa using h

lemma cMat_qMat_apply (a : ℂ) (w : EuclideanSpace ℂ (Fin 2)) :
    cMat a (qMat w) = qMat (diagP a (star a) w) := by
  have h := qMatInv_cMat_apply a (qMat w)
  rw [qMatInv_qMat_apply] at h
  have h2 := congrArg qMat h
  rwa [qMat_qMatInv_apply] at h2

/-! ## 4. The gauge family -/

/-- The forward gauge: the target transition followed by the diagonalisation. -/
def tbPhi0 (i : Fin 5) (t : Fin 5 × Fin 5) (x : CP 4) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (tbTX.coordChange (i, i) t x).comp qMatInv

/-- The inverse gauge. -/
def tbPhi0Inv (i : Fin 5) (t : Fin 5 × Fin 5) (x : CP 4) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  qMat.comp (tbTX.coordChange t (i, i) x)

lemma tbPhi0_apply (i : Fin 5) (t : Fin 5 × Fin 5) (x : CP 4)
    (v : EuclideanSpace ℂ (Fin 2)) :
    tbPhi0 i t x v = tbTX.coordChange (i, i) t x (qMatInv v) := rfl

lemma tbPhi0Inv_apply (i : Fin 5) (t : Fin 5 × Fin 5) (x : CP 4)
    (v : EuclideanSpace ℂ (Fin 2)) :
    tbPhi0Inv i t x v = qMat (tbTX.coordChange t (i, i) x v) := rfl

/-! ## 5. Membership bookkeeping -/

lemma mem_chartSet_of_mem_baseSet {i : Fin 5} {b : CP 4}
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i) :
    b ∈ Work.Projective.chartSet i := by
  rwa [complexificationCore_tbZL_baseSet] at hb

lemma mem_tbTX_baseSet_diag {i : Fin 5} {b : CP 4}
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i) :
    b ∈ tbTX.baseSet (i, i) := by
  have hbi : b ∈ Work.Projective.chartSet i := mem_chartSet_of_mem_baseSet hb
  rw [tbTX_baseSet]
  exact ⟨hbi, hbi⟩

/-! ## 6. Continuity of the gauge families -/

theorem tbPhi0_hcont (i : Fin 5) (t : Fin 5 × Fin 5) :
    ContinuousOn (fun b : CP 4 => tbPhi0 i t b)
      ((Work.Thom.complexificationCore tbZL).baseSet i ∩ tbTX.baseSet t) := by
  have hA : ContinuousOn (fun b : CP 4 => tbTX.coordChange (i, i) t b)
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) := by
    have h := tbTX.continuousOn_coordChange (i, i) t
    rw [tbTX_baseSet (i, i), tbTX_baseSet t] at h
    refine h.mono ?_
    intro b hb
    exact ⟨⟨hb.1, hb.1⟩, hb.2⟩
  have hmain : ContinuousOn
      (fun b : CP 4 => (tbTX.coordChange (i, i) t b).comp qMatInv)
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) :=
    ContinuousOn.clm_comp hA continuousOn_const
  have hfun : (fun b : CP 4 => tbPhi0 i t b)
      = fun b => (tbTX.coordChange (i, i) t b).comp qMatInv := by
    funext b; rw [tbPhi0]
  rw [hfun]
  refine hmain.mono ?_
  intro b hb
  rw [complexificationCore_tbZL_baseSet, tbTX_baseSet] at hb
  exact hb

theorem tbPhi0Inv_hcont (i : Fin 5) (t : Fin 5 × Fin 5) :
    ContinuousOn (fun b : CP 4 => tbPhi0Inv i t b)
      ((Work.Thom.complexificationCore tbZL).baseSet i ∩ tbTX.baseSet t) := by
  have hA : ContinuousOn (fun b : CP 4 => tbTX.coordChange t (i, i) b)
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) := by
    have h := tbTX.continuousOn_coordChange t (i, i)
    rw [tbTX_baseSet t, tbTX_baseSet (i, i)] at h
    refine h.mono ?_
    intro b hb
    exact ⟨hb.2, ⟨hb.1, hb.1⟩⟩
  have hmain : ContinuousOn
      (fun b : CP 4 => qMat.comp (tbTX.coordChange t (i, i) b))
      (Work.Projective.chartSet i ∩
        (Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2)) :=
    ContinuousOn.clm_comp continuousOn_const hA
  have hfun : (fun b : CP 4 => tbPhi0Inv i t b)
      = fun b => qMat.comp (tbTX.coordChange t (i, i) b) := by
    funext b; rw [tbPhi0Inv]
  rw [hfun]
  refine hmain.mono ?_
  intro b hb
  rw [complexificationCore_tbZL_baseSet, tbTX_baseSet] at hb
  exact hb

/-! ## 7. The eight conditions -/

theorem tbPhi0_htgt (i : Fin 5) (t t' : Fin 5 × Fin 5) (b : CP 4)
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i) (ht : b ∈ tbTX.baseSet t)
    (ht' : b ∈ tbTX.baseSet t') :
    (tbTX.coordChange t t' b).comp (tbPhi0 i t b) = tbPhi0 i t' b := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb
  have hmem : b ∈ tbTX.baseSet (i, i) ∩ tbTX.baseSet t ∩ tbTX.baseSet t' := ⟨⟨htii, ht⟩, ht'⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, tbPhi0_apply, tbPhi0_apply]
  exact tbTX.coordChange_comp (i, i) t t' b hmem (qMatInv x)

theorem tbPhi0_hsrc (i : Fin 5) (t : Fin 5 × Fin 5) (i' : Fin 5) (b : CP 4)
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i)
    (hb' : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i') (ht : b ∈ tbTX.baseSet t) :
    (tbPhi0 i t b).comp ((Work.Thom.complexificationCore tbZL).coordChange i' i b)
      = tbPhi0 i' t b := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb
  have hti'i' : b ∈ tbTX.baseSet (i', i') := mem_tbTX_baseSet_diag hb'
  have hmem : b ∈ tbTX.baseSet (i', i') ∩ tbTX.baseSet (i, i) ∩ tbTX.baseSet t :=
    ⟨⟨hti'i', htii⟩, ht⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, tbPhi0_apply, tbPhi0_apply,
    complexificationCore_tbZL_coordChange i' i b, qMatInv_cMat_apply,
    ← tbTX_coordChange (i', i') (i, i) b]
  exact tbTX.coordChange_comp (i', i') (i, i) t b hmem (qMatInv x)

theorem tbPhi0_htgtinv (i : Fin 5) (t t' : Fin 5 × Fin 5) (b : CP 4)
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i) (ht : b ∈ tbTX.baseSet t)
    (ht' : b ∈ tbTX.baseSet t') :
    (tbPhi0Inv i t b).comp (tbTX.coordChange t' t b) = tbPhi0Inv i t' b := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb
  have hmem : b ∈ tbTX.baseSet t' ∩ tbTX.baseSet t ∩ tbTX.baseSet (i, i) := ⟨⟨ht', ht⟩, htii⟩
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearMap.comp_apply, tbPhi0Inv_apply, tbPhi0Inv_apply,
    tbTX.coordChange_comp t' t (i, i) b hmem y]

theorem tbPhi0_hsrcinv (i : Fin 5) (t : Fin 5 × Fin 5) (i' : Fin 5) (b : CP 4)
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i)
    (hb' : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i') (ht : b ∈ tbTX.baseSet t) :
    ((Work.Thom.complexificationCore tbZL).coordChange i i' b).comp (tbPhi0Inv i t b)
      = tbPhi0Inv i' t b := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb
  have hmem : b ∈ tbTX.baseSet t ∩ tbTX.baseSet (i, i) ∩ tbTX.baseSet (i', i') :=
    ⟨⟨ht, htii⟩, mem_tbTX_baseSet_diag hb'⟩
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearMap.comp_apply, tbPhi0Inv_apply, tbPhi0Inv_apply,
    complexificationCore_tbZL_coordChange i i' b, cMat_qMat_apply,
    ← tbTX_coordChange (i, i) (i', i') b,
    tbTX.coordChange_comp t (i, i) (i', i') b hmem y]

theorem tbPhi0_hleft (i : Fin 5) (t : Fin 5 × Fin 5) (b : CP 4)
    (x : EuclideanSpace ℂ (Fin 2))
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i ∩ tbTX.baseSet t) :
    tbPhi0Inv i t b (tbPhi0 i t b x) = x := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb.1
  have hmem : b ∈ tbTX.baseSet (i, i) ∩ tbTX.baseSet t ∩ tbTX.baseSet (i, i) :=
    ⟨⟨htii, hb.2⟩, htii⟩
  rw [tbPhi0Inv_apply, tbPhi0_apply,
    tbTX.coordChange_comp (i, i) t (i, i) b hmem (qMatInv x),
    tbTX.coordChange_self (i, i) b htii (qMatInv x)]
  exact qMat_qMatInv_apply x

theorem tbPhi0_hright (i : Fin 5) (t : Fin 5 × Fin 5) (b : CP 4)
    (y : EuclideanSpace ℂ (Fin 2))
    (hb : b ∈ (Work.Thom.complexificationCore tbZL).baseSet i ∩ tbTX.baseSet t) :
    tbPhi0 i t b (tbPhi0Inv i t b y) = y := by
  have htii : b ∈ tbTX.baseSet (i, i) := mem_tbTX_baseSet_diag hb.1
  have hmem : b ∈ tbTX.baseSet t ∩ tbTX.baseSet (i, i) ∩ tbTX.baseSet t :=
    ⟨⟨hb.2, htii⟩, hb.2⟩
  rw [tbPhi0_apply, tbPhi0Inv_apply, qMatInv_qMat_apply,
    tbTX.coordChange_comp t (i, i) t b hmem y,
    tbTX.coordChange_self t b hb.2 y]

/-! ## 8. The isomorphism -/

theorem tbZL_complexification_iso :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore Work.ThomBordism.Grassmann.tbZL)
      (Work.Whitney.whitneySum (Work.Gen.tautLine 4) (Work.Gen.conjLine 4))) :=
  Work.Thom.nonempty_bundleIso_of_gauge
    (Work.Thom.complexificationCore Work.ThomBordism.Grassmann.tbZL) tbTX
    tbPhi0 tbPhi0Inv tbPhi0_hcont tbPhi0Inv_hcont tbPhi0_htgt tbPhi0_hsrc tbPhi0_htgtinv
    tbPhi0_hsrcinv tbPhi0_hleft tbPhi0_hright

end

end Work.ThomBordism.Grassmann.TB
