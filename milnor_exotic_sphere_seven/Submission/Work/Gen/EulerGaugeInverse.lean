import Mathlib
import Submission.Work.Gen.EulerGaugeIdentity
import Submission.Work.Gen.EulerBlockInverse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The inverse gauge of the Euler sequence

Two-sided inverse identities for the gauge `Work.Gen.gaugeCLM` / `Work.Gen.gaugeInvCLM`, and the
cocycle (gauge-change) identities in the exact form consumed by
`Work.Thom.nonempty_bundleIso_of_gauge`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The cocycle of the transition functions of `Tgt`, as an identity of continuous linear maps. -/
theorem Tgt_cc_comp (i j k : TgtIdx) {b : CP 4}
    (hb : b ∈ Tgt.baseSet i ∩ Tgt.baseSet j ∩ Tgt.baseSet k) :
    (Tgt.coordChange j k b).comp (Tgt.coordChange i j b) = Tgt.coordChange i k b := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  exact Tgt.coordChange_comp i j k b hb v

/-- The cocycle of the transition functions of `Src`, as an identity of continuous linear maps. -/
theorem Src_cc_comp (i j k : Fin 5 × Fin 1) {b : CP 4}
    (hb : b ∈ Src.baseSet i ∩ Src.baseSet j ∩ Src.baseSet k) :
    (Src.coordChange j k b).comp (Src.coordChange i j b) = Src.coordChange i k b := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  exact Src.coordChange_comp i j k b hb v

/-- The self-transition of `Tgt` is the identity. -/
theorem Tgt_cc_self (i : TgtIdx) {b : CP 4} (hb : b ∈ Tgt.baseSet i) :
    Tgt.coordChange i i b = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact Tgt.coordChange_self i b hb v

/-- The transition functions of `Src` do not depend on the (`Fin 1`) index of the trivial summand. -/
theorem Src_coordChange_fst (p q : Fin 5) (β β' : Fin 1) (b : CP 4) :
    Src.coordChange (p, β) (q, β') b = Src.coordChange (p, 0) (q, 0) b := by
  rw [Src_coordChange, Src_coordChange]

/-- The self-transition of `Src` is the identity. -/
theorem Src_cc_self (i : Fin 5 × Fin 1) {b : CP 4} (hb : b ∈ Src.baseSet i) :
    Src.coordChange i i b = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact Src.coordChange_self i b hb v

variable {p q : Fin 5} {b : CP 4}

theorem mem_baseSet_diag (p : Fin 5) {b : CP 4} (hb : b ∈ chartSet p) :
    b ∈ Tgt.baseSet (diagIdx p) := by
  rw [eulerTarget_baseSet_diagIdx]; exact hb

theorem mem_baseSet_src (p : Fin 5) (β : Fin 1) {b : CP 4} (hb : b ∈ chartSet p) :
    b ∈ Src.baseSet (p, β) := by
  rw [Src, Work.Whitney.whitneySum_baseSet]
  exact ⟨by rwa [stdTangentC_baseSet], Set.mem_univ _⟩

/-- **The inverse-transpose form of the gauge identity.** -/
theorem gaugeCore_inv (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p ∩ chartSet q) :
    (Src.coordChange (p, 0) (q, 0) b).comp (MInvCLM p b)
      = (MInvCLM q b).comp (Tgt.coordChange (diagIdx p) (diagIdx q) b) := by
  apply ContinuousLinearMap.ext
  intro v
  have hm : ∀ z, MInvCLM q b (MCLM q b z) = z := by
    intro z
    have hh := congrArg (fun (f : EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10)) =>
      f z) (MInvCLM_MCLM q b)
    simpa using hh
  have hm' : ∀ z, MCLM p b (MInvCLM p b z) = z := by
    intro z
    have hh := congrArg (fun (f : EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10)) =>
      f z) (MCLM_MInvCLM p b)
    simpa using hh
  have h := congrArg (fun (f : EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10)) =>
      MInvCLM q b (f (MInvCLM p b v))) (gaugeCore p q hb)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hm, hm'] at h
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- Pointwise form of an identity of continuous linear maps. -/
theorem apply_congr {α β : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α]
    [NormedAddCommGroup β] [NormedSpace ℂ β]
    {f g : α →L[ℂ] β} (h : f = g) (v : α) : f v = g v := congrArg (fun k => k v) h

/-- The gauge of the bundle map is a left inverse of the gauge of the inverse bundle map. -/
theorem gaugeInvCLM_gaugeCLM (p : Fin 5) (t : TgtIdx) {b : CP 4}
    (hb : b ∈ chartSet p) (ht : b ∈ Tgt.baseSet t) :
    (gaugeInvCLM p t b).comp (gaugeCLM p t b) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  have hdp : b ∈ Tgt.baseSet (diagIdx p) := mem_baseSet_diag p hb
  have hccv : ∀ w, Tgt.coordChange t (diagIdx p) b (Tgt.coordChange (diagIdx p) t b w) = w := by
    intro w
    have h := Tgt.coordChange_comp (diagIdx p) t (diagIdx p) b ⟨⟨hdp, ht⟩, hdp⟩ w
    rwa [Tgt.coordChange_self (diagIdx p) b hdp] at h
  have hm : ∀ w, MInvCLM p b (MCLM p b w) = w := fun w =>
    apply_congr (MInvCLM_MCLM p b) w
  show gaugeInvCLM p t b (gaugeCLM p t b v) = v
  rw [gaugeInvCLM, gaugeCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hccv, hm]

/-- The gauge of the inverse bundle map is a left inverse of the gauge of the bundle map. -/
theorem gaugeCLM_gaugeInvCLM (p : Fin 5) (t : TgtIdx) {b : CP 4}
    (hb : b ∈ chartSet p) (ht : b ∈ Tgt.baseSet t) :
    (gaugeCLM p t b).comp (gaugeInvCLM p t b) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  have hdp : b ∈ Tgt.baseSet (diagIdx p) := mem_baseSet_diag p hb
  have hccv : ∀ w, Tgt.coordChange (diagIdx p) t b (Tgt.coordChange t (diagIdx p) b w) = w := by
    intro w
    have h := Tgt.coordChange_comp t (diagIdx p) t b ⟨⟨ht, hdp⟩, ht⟩ w
    rwa [Tgt.coordChange_self t b ht] at h
  have hm : ∀ w, MCLM p b (MInvCLM p b w) = w := fun w =>
    apply_congr (MCLM_MInvCLM p b) w
  show gaugeCLM p t b (gaugeInvCLM p t b v) = v
  rw [gaugeInvCLM, gaugeCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hm, hccv]

/-- **The target cocycle of the gauge.** -/
theorem gauge_htgt (i : Fin 5 × Fin 1) (t t' : TgtIdx) (b : CP 4)
    (hi : b ∈ Src.baseSet i) (ht : b ∈ Tgt.baseSet t) (ht' : b ∈ Tgt.baseSet t') :
    (Tgt.coordChange t t' b).comp (gaugeCLM i.1 t b) = gaugeCLM i.1 t' b := by
  have hp : b ∈ chartSet i.1 := by
    have h := hi.1
    rwa [stdTangentC_baseSet] at h
  have hdp : b ∈ Tgt.baseSet (diagIdx i.1) := mem_baseSet_diag i.1 hp
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, gaugeCLM, gaugeCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Tgt.coordChange_comp (diagIdx i.1) t t' b ⟨⟨hdp, ht⟩, ht'⟩]

/-- **The source cocycle of the gauge.** -/
theorem gauge_hsrc (i : Fin 5 × Fin 1) (t : TgtIdx) (i' : Fin 5 × Fin 1) (b : CP 4)
    (hi : b ∈ Src.baseSet i) (hi' : b ∈ Src.baseSet i') (ht : b ∈ Tgt.baseSet t) :
    (gaugeCLM i.1 t b).comp (Src.coordChange i' i b) = gaugeCLM i'.1 t b := by
  have hp : b ∈ chartSet i.1 := by
    have h := hi.1
    rwa [stdTangentC_baseSet] at h
  have hq : b ∈ chartSet i'.1 := by
    have h := hi'.1
    rwa [stdTangentC_baseSet] at h
  have hdp : b ∈ Tgt.baseSet (diagIdx i.1) := mem_baseSet_diag i.1 hp
  have hdq : b ∈ Tgt.baseSet (diagIdx i'.1) := mem_baseSet_diag i'.1 hq
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, gaugeCLM, gaugeCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show Src.coordChange i' i b = Src.coordChange (i'.1, 0) (i.1, 0) b from
    Src_coordChange_fst i'.1 i.1 i'.2 i.2 b]
  have hcv : ∀ w, MCLM i.1 b (Src.coordChange (i'.1, 0) (i.1, 0) b w)
      = Tgt.coordChange (diagIdx i'.1) (diagIdx i.1) b (MCLM i'.1 b w) := fun w =>
    apply_congr (gaugeCore i'.1 i.1 ⟨hq, hp⟩) w
  rw [hcv]
  rw [Tgt.coordChange_comp (diagIdx i'.1) (diagIdx i.1) t b ⟨⟨hdq, hdp⟩, ht⟩]

/-- **The target cocycle of the inverse gauge.** -/
theorem gauge_htgtinv (i : Fin 5 × Fin 1) (t t' : TgtIdx) (b : CP 4)
    (hi : b ∈ Src.baseSet i) (ht : b ∈ Tgt.baseSet t) (ht' : b ∈ Tgt.baseSet t') :
    (gaugeInvCLM i.1 t b).comp (Tgt.coordChange t' t b) = gaugeInvCLM i.1 t' b := by
  have hp : b ∈ chartSet i.1 := by
    have h := hi.1
    rwa [stdTangentC_baseSet] at h
  have hdp : b ∈ Tgt.baseSet (diagIdx i.1) := mem_baseSet_diag i.1 hp
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, gaugeInvCLM, gaugeInvCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Tgt.coordChange_comp t' t (diagIdx i.1) b ⟨⟨ht', ht⟩, hdp⟩]

/-- **The source cocycle of the inverse gauge.** -/
theorem gauge_hsrcinv (i : Fin 5 × Fin 1) (t : TgtIdx) (i' : Fin 5 × Fin 1) (b : CP 4)
    (hi : b ∈ Src.baseSet i) (hi' : b ∈ Src.baseSet i') (ht : b ∈ Tgt.baseSet t) :
    (Src.coordChange i i' b).comp (gaugeInvCLM i.1 t b) = gaugeInvCLM i'.1 t b := by
  have hp : b ∈ chartSet i.1 := by
    have h := hi.1
    rwa [stdTangentC_baseSet] at h
  have hq : b ∈ chartSet i'.1 := by
    have h := hi'.1
    rwa [stdTangentC_baseSet] at h
  have hdp : b ∈ Tgt.baseSet (diagIdx i.1) := mem_baseSet_diag i.1 hp
  have hdq : b ∈ Tgt.baseSet (diagIdx i'.1) := mem_baseSet_diag i'.1 hq
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, gaugeInvCLM, gaugeInvCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show Src.coordChange i i' b = Src.coordChange (i.1, 0) (i'.1, 0) b from
    Src_coordChange_fst i.1 i'.1 i.2 i'.2 b]
  have hcv : ∀ w, Src.coordChange (i.1, 0) (i'.1, 0) b (MInvCLM i.1 b w)
      = MInvCLM i'.1 b (Tgt.coordChange (diagIdx i.1) (diagIdx i'.1) b w) := fun w =>
    apply_congr (gaugeCore_inv i.1 i'.1 ⟨hp, hq⟩) w
  rw [hcv]
  rw [Tgt.coordChange_comp t (diagIdx i.1) (diagIdx i'.1) b ⟨⟨ht, hdp⟩, hdq⟩]

end

end Work.Gen
