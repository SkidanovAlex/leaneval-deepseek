import Mathlib
import Submission.Work.Agree.gaugeDefs
import Submission.Work.Agree.fderiv_invBase_gauge
import Submission.Work.Agree.gauge_continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 800000

/-!
# `GeometryB`: the properties of the gauge

The algebra and continuity statements needed to feed `Work.Thom.nonempty_bundleIso_of_gauge`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses
open Submission.Glue

noncomputable section

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "HH" => Quaternion ℝ

/-! ## The algebraic identities -/

lemma gaugeJ_gaugeJ (v : E4) : gaugeJ (gaugeJ v) = v := by
  simp only [gaugeJ, ContinuousLinearMap.comp_apply, conjQ_apply, toQ_ofQ, star_star, ofQ_toQ]

lemma gaugeC_comp_gaugeCinv (b : Vk) : (gaugeC b).comp (gaugeCinv b) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  show gaugeC b (gaugeCinv b w) = w
  rw [gaugeC_apply, gaugeCinv_apply]
  have hu : gaugeU b ≠ 0 := gaugeU_ne_zero b
  rw [show gaugeU b ^ (2 : ℤ) = gaugeU b ^ 2 from by rw [zpow_ofNat],
      show gaugeU b ^ (-2 : ℤ) = (gaugeU b ^ 2)⁻¹ from by rw [zpow_neg, zpow_ofNat],
      show gaugeU b ^ (-1 : ℤ) = (gaugeU b)⁻¹ from by rw [zpow_neg, zpow_one]]
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hu, mul_one, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 hu), one_mul]

lemma gaugeCinv_comp_gaugeC (b : Vk) : (gaugeCinv b).comp (gaugeC b) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  show gaugeCinv b (gaugeC b w) = w
  rw [gaugeC_apply, gaugeCinv_apply]
  have hu : gaugeU b ≠ 0 := gaugeU_ne_zero b
  rw [show gaugeU b ^ (2 : ℤ) = gaugeU b ^ 2 from by rw [zpow_ofNat],
      show gaugeU b ^ (-2 : ℤ) = (gaugeU b ^ 2)⁻¹ from by rw [zpow_neg, zpow_ofNat],
      show gaugeU b ^ (-1 : ℤ) = (gaugeU b)⁻¹ from by rw [zpow_neg, zpow_one]]
  rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hu, mul_one, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hu), one_mul]

lemma gaugeH0_comp_gaugeH0inv (b : Vk) : (gaugeH0 b).comp (gaugeH0inv b) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  show gaugeH0 b (gaugeH0inv b (δ, ε)) = (δ, ε)
  simp only [gaugeH0, gaugeH0inv, gaugeBlk_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    gaugeJ_gaugeJ, smul_smul]
  refine Prod.ext ?_ ?_
  · first
    | rw [mul_inv_cancel₀ (etaCut_ne_zero _), one_smul]
    | rw [inv_mul_cancel₀ (etaCut_ne_zero _), one_smul]
  · rw [neg_mul, neg_smul, ← add_assoc, ← sub_eq_add_neg, ← sub_smul,
      show (etaCut ‖gaugeX b‖)⁻¹ * aCut ‖gaugeX b‖ - aCut ‖gaugeX b‖ * (etaCut ‖gaugeX b‖)⁻¹
        = 0 by ring, zero_smul, zero_add]

lemma gaugeH0inv_comp_gaugeH0 (b : Vk) : (gaugeH0inv b).comp (gaugeH0 b) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  show gaugeH0inv b (gaugeH0 b (δ, ε)) = (δ, ε)
  simp only [gaugeH0, gaugeH0inv, gaugeBlk_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    gaugeJ_gaugeJ, smul_smul]
  refine Prod.ext ?_ ?_
  · first
    | rw [mul_inv_cancel₀ (etaCut_ne_zero _), one_smul]
    | rw [inv_mul_cancel₀ (etaCut_ne_zero _), one_smul]
  · rw [← add_assoc,
      show etaCut ‖gaugeX b‖ * (-aCut ‖gaugeX b‖ * (etaCut ‖gaugeX b‖)⁻¹)
        = -aCut ‖gaugeX b‖ by
        rw [neg_mul, mul_neg, ← mul_assoc, mul_comm (etaCut ‖gaugeX b‖) (aCut ‖gaugeX b‖),
          mul_assoc, mul_inv_cancel₀ (etaCut_ne_zero _), mul_one],
      neg_smul, neg_add_cancel, zero_add]
/-! ## Bookkeeping: the overlap and the hemispheres -/

/-- The class of `Sum.inl p` meets the class of `Sum.inr q` only if `p.1 ≠ 0`. -/
lemma gaugeX_ne_zero_of_mem {b : Vk} (hb : b ∈ gaugeUX ∩ gaugeUY) : gaugeX b ≠ 0 := by
  obtain ⟨p, rfl⟩ := hb.1
  obtain ⟨q, hq⟩ := hb.2
  have hrel : (Submission.Milnor.vData (-2)).rel (Sum.inl p) (Sum.inr q) :=
    @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
      (Submission.Milnor.vData (-2)).setoid (Sum.inl p) (Sum.inr q) hq.symm
  obtain ⟨hp, -⟩ := hrel
  have hp1 : p.1 ≠ 0 := hp
  rw [gaugeX_iotaX]
  exact hp1

lemma gaugeUX_subset_targetCore_ff : gaugeUX ⊆ targetCore.baseSet (false, false) := by
  rintro b ⟨p, rfl⟩
  rw [targetCore_baseSet]
  simp only [targetC, Work.Thom.bundleComap_baseSet, RealBundle.sum_baseSet,
    clutchBundle_baseSet, Set.mem_preimage, Set.mem_inter_iff, Bool.false_eq_true, reduceIte]
  constructor <;>
  · rw [discProj_apply, Work.Milnor.vBaseMap_ιX]
    exact fun h => Option.some_ne_none p.1 h

lemma gaugeUY_subset_targetCore_tt : gaugeUY ⊆ targetCore.baseSet (true, true) := by
  rintro b ⟨p, rfl⟩
  rw [targetCore_baseSet]
  simp only [targetC, Work.Thom.bundleComap_baseSet, RealBundle.sum_baseSet,
    clutchBundle_baseSet, Set.mem_preimage, Set.mem_inter_iff, Bool.true_eq_false, reduceIte]
  constructor <;>
  · rw [discProj_apply, Work.Milnor.vBaseMap_ιY]
    show Submission.Milnor.baseChart2 p.1 ≠ ((0 : E4) : Submission.Milnor.S4)
    rcases eq_or_ne p.1 0 with h | h
    · rw [h, Submission.Milnor.baseChart2_zero]
      exact (Option.some_ne_none 0).symm
    · rw [Submission.Milnor.baseChart2, if_neg h]
      exact fun hc => absurd (Option.some.inj hc) (Submission.Milnor.invBase_ne_zero h)

lemma gaugeYNorm_eq_inv_norm {b : Vk} (hb : b ∈ gaugeUX ∩ gaugeUY) :
    gaugeYNorm b = (‖gaugeX b‖)⁻¹ := by
  obtain ⟨p, rfl⟩ := hb.1
  obtain ⟨q, hq⟩ := hb.2
  have hrel : (Submission.Milnor.vData (-2)).rel (Sum.inl p) (Sum.inr q) :=
    @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
      (Submission.Milnor.vData (-2)).setoid (Sum.inl p) (Sum.inr q) hq.symm
  obtain ⟨hp, -⟩ := hrel
  have hp1 : p.1 ≠ 0 := hp
  rw [gaugeYNorm_iotaX p hp1, gaugeX_iotaX]

lemma gauge_bookkeeping :
    (∀ b : Vk, b ∈ gaugeUX ∩ gaugeUY → gaugeX b ≠ 0) ∧
    gaugeUX ⊆ targetCore.baseSet (false, false) ∧
    gaugeUY ⊆ targetCore.baseSet (true, true) ∧
    (∀ b ∈ gaugeUX ∩ gaugeUY, gaugeYNorm b = (‖gaugeX b‖)⁻¹) :=
  ⟨fun b hb => gaugeX_ne_zero_of_mem hb, gaugeUX_subset_targetCore_ff,
    gaugeUY_subset_targetCore_tt, fun b hb => gaugeYNorm_eq_inv_norm hb⟩
/-! ## The block forms of the two transition functions -/

-- pointwise helper for `prodMap`
lemma prodMap_apply' (f g : E4 →L[ℝ] E4) (x y : E4) :
    f.prodMap g (x, y) = (f x, g y) := rfl

/-- The fibre transport of a block-diagonal map. -/
lemma fibEquiv_prodMap (f g : E4 →L[ℝ] E4) :
    (fibEquiv : (E4 × E4) →L[ℝ] Submission.Milnor.MSpace8).comp
        (((f.prodMap g) : (E4 × E4) →L[ℝ] (E4 × E4)).comp
          (fibEquiv.symm : Submission.Milnor.MSpace8 →L[ℝ] (E4 × E4)))
      = gaugeBlk f 0 (toQ.comp (g.comp ofQ)) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  simp only [ContinuousLinearMap.comp_apply, fibEquiv_coe_symm_apply, prodMap_apply',
    fibEquiv_coe_apply, gaugeBlk_apply, ContinuousLinearMap.zero_apply, zero_add, toQ_ofQ]

lemma gaugeU_eq_uDir (b : Vk) (hb : b ∈ gaugeUX) :
    gaugeU b = uDir (discProj b) := by
  obtain ⟨p, rfl⟩ := hb
  rw [gaugeU_iotaX, uDir_discProj_iotaX]

/-- **The target transition in block form.** -/
lemma targetCore_blk (b : Vk) (hb : b ∈ gaugeUX) :
    targetCore.coordChange (false, false) (true, true) b
      = gaugeBlk (qTwist (1 : ℤ) 1 (gaugeU b)) 0 (gaugeC b) := by
  rw [targetCore_coordChange, targetC_coordChange_ff_tt, ← gaugeU_eq_uDir b hb]
  exact fibEquiv_prodMap _ _

/-- **The source transition in block form.** -/
lemma fderiv_vMap_eq_blk (b : Vk) (hx : gaugeX b ≠ 0) :
    fderiv ℝ (Submission.Milnor.vMap (-2)) ((Submission.Milnor.vData (-2)).chartOfX 0 b)
      = gaugeBlk (fderiv ℝ Submission.Milnor.invBase (gaugeX b)) (gaugeBOff b) (gaugeC b) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  rw [gaugeBlk_apply, gaugeBOff_apply, gaugeC_apply_pow,
    fderiv_vMap_apply _ hx (δ, 0), fderiv_vMap_apply _ hx (δ, ε)]
  refine Prod.ext rfl ?_
  simp only [gaugeU, gaugeX, mul_zero, zero_mul, add_zero, zero_add]

lemma vkTangent_blk
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) (hx : gaugeX b ≠ 0) :
    (vkTangent h).coordChange 0 1 b
      = gaugeBlk (fderiv ℝ Submission.Milnor.invBase (gaugeX b)) (gaugeBOff b) (gaugeC b) := by
  rw [vkTangent_coordChange_zero_one h
    ⟨by rw [vkTangent_baseSet_zero h]; exact hb.1,
     by rw [vkTangent_baseSet_one h]; exact hb.2⟩]
  exact fderiv_vMap_eq_blk b hx

/-- **The key identity**: on the overlap, where `‖xOf‖ ≥ 3/2`, the gauge `H₀` inverts the
discrepancy between the two transitions. -/
lemma gaugeKey
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) (ht : 3 / 2 ≤ ‖gaugeX b‖)
    (hα : (vkTangent h).coordChange 0 1 b
      = gaugeBlk (fderiv ℝ Submission.Milnor.invBase (gaugeX b)) (gaugeBOff b) (gaugeC b))
    (hD : targetCore.coordChange (false, false) (true, true) b
      = gaugeBlk (qTwist (1 : ℤ) 1 (gaugeU b)) 0 (gaugeC b))
    (hI : fderiv ℝ Submission.Milnor.invBase (gaugeX b)
      = -((‖gaugeX b‖ ^ 2)⁻¹) • ((qTwist (1 : ℤ) 1 (gaugeU b)).comp gaugeJ))
    (hCinv : (gaugeC b).comp (gaugeCinv b) = 1) :
    (vkTangent h).coordChange 0 1 b
      = (targetCore.coordChange (false, false) (true, true) b).comp (gaugeH0 b) := by
  have h1 : (1 : ℝ) ≤ ‖gaugeX b‖ := by linarith
  have ha : aCut ‖gaugeX b‖ = 1 := aCut_of_ge ht
  have heta : etaCut ‖gaugeX b‖ = -(‖gaugeX b‖ ^ 2)⁻¹ := etaCut_of_ge_one h1
  have ha' : ∀ x : HH, (aCut ‖gaugeX b‖) • x = x := by
    intro x; rw [ha, one_smul]
  have heta' : ∀ y : E4, (etaCut ‖gaugeX b‖) • y = -(‖gaugeX b‖ ^ 2)⁻¹ • y := by
    intro y; rw [heta]
  have hCinv' : ∀ x : HH, gaugeC b (gaugeCinv b x) = x := fun x =>
    congrArg (fun f : HH →L[ℝ] HH => f x) hCinv
  rw [hα, hD]
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨δ, ε⟩ := v
  simp only [ContinuousLinearMap.comp_apply, gaugeH0, gaugeXOff, gaugeBlk_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    heta', ha', map_add, hCinv', zero_add]
  refine Prod.ext ?_ ?_
  · rw [hI]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  · rfl
/-! ## The second chart: the gauge `H₁` -/

/-- A point of `gaugeUY` with nonzero Y-chart coordinate lies in the overlap. -/
lemma gaugeUX_of_mem_gaugeUY (b : Vk) (hb : b ∈ gaugeUY) (h0 : gaugeYNorm b ≠ 0) :
    b ∈ gaugeUX := by
  obtain ⟨q, rfl⟩ := hb
  have hq : q.1 ≠ 0 := by
    intro hq0
    exact h0 (by simp only [gaugeYNorm, gaugeXY, chartOfY_iotaY, hq0, norm_zero])
  refine ⟨Submission.Milnor.vMapInv (-2) q, ?_⟩
  exact Quotient.sound ⟨Submission.Milnor.invBase_ne_zero hq,
    (Work.Milnor.vMap_inv (-2) hq).2⟩

lemma three_halves_le_of_gaugeYNorm_le {b : Vk} (hb : b ∈ gaugeUX ∩ gaugeUY)
    (h : gaugeYNorm b ≤ 2 / 3) : 3 / 2 ≤ ‖gaugeX b‖ := by
  rw [gaugeYNorm_eq_inv_norm hb] at h
  have hp : 0 < ‖gaugeX b‖ := norm_pos_iff.mpr (gaugeX_ne_zero_of_mem hb)
  have h3 : (‖gaugeX b‖)⁻¹ * ‖gaugeX b‖ ≤ (2 / 3) * ‖gaugeX b‖ :=
    mul_le_mul_of_nonneg_right h (le_of_lt hp)
  rw [inv_mul_cancel₀ (ne_of_gt hp)] at h3
  linarith

/-- The key identity for all overlap points (the hypothesis of `gaugeKey` is discharged by the
definition of `gaugeH0`, which realises `Eψ = E` and `Uψ = U` for `‖gaugeX ·‖ ≥ 3/2`). -/
lemma gaugeKey_all
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) (ht : 3 / 2 ≤ ‖gaugeX b‖) :
    (vkTangent h).coordChange 0 1 b
      = (targetCore.coordChange (false, false) (true, true) b).comp (gaugeH0 b) :=
  gaugeKey h b hb ht (vkTangent_blk h b hb (gaugeX_ne_zero_of_mem hb))
    (targetCore_blk b hb.1) (fderiv_invBase_gauge (gaugeX b) (gaugeX_ne_zero_of_mem hb))
    (gaugeC_comp_gaugeCinv b)

/-- **The gauge `H₁` is the transition discrepancy on the overlap.** -/
lemma gaugeH1_eq
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) :
    gaugeH1 h b = (targetCore.coordChange (false, false) (true, true) b).comp
      ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b)) := by
  rw [gaugeH1, if_neg]
  intro h0
  have h1 := gaugeYNorm_eq_inv_norm hb
  rw [h0] at h1
  exact gaugeX_ne_zero_of_mem hb (norm_eq_zero.mp (inv_eq_zero.mp h1.symm))

lemma gaugeH1inv_eq
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) :
    gaugeH1inv h b = ((vkTangent h).coordChange 0 1 b).comp
      ((gaugeH0inv b).comp (targetCore.coordChange (true, true) (false, false) b)) := by
  rw [gaugeH1inv, if_neg]
  intro h0
  have h1 := gaugeYNorm_eq_inv_norm hb
  rw [h0] at h1
  exact gaugeX_ne_zero_of_mem hb (norm_eq_zero.mp (inv_eq_zero.mp h1.symm))

/-- The expression of `gaugeH1` in terms of `gaugeKey` is the identity on `{gaugeYNorm ≤ 2/3}`. -/
lemma gaugeH1_expr_eq_one
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) (h23 : gaugeYNorm b ≤ 2 / 3) :
    (targetCore.coordChange (false, false) (true, true) b).comp
      ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b)) = 1 := by
  have hkey := gaugeKey_all h b hb (three_halves_le_of_gaugeYNorm_le hb h23)
  rw [show ((targetCore.coordChange (false, false) (true, true) b).comp
        ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b)))
      = ((targetCore.coordChange (false, false) (true, true) b).comp (gaugeH0 b)).comp
          ((vkTangent h).coordChange 1 0 b) from (ContinuousLinearMap.comp_assoc _ _ _).symm]
  rw [← hkey]
  have h1 : b ∈ (vkTangent h).baseSet 1 := by
    rw [vkTangent_baseSet_one h]; exact hb.2
  have h0 : b ∈ (vkTangent h).baseSet 0 := by
    rw [vkTangent_baseSet_zero h]; exact hb.1
  have hmem : b ∈ (vkTangent h).baseSet 1 ∩ (vkTangent h).baseSet 0 ∩ (vkTangent h).baseSet 1 :=
    ⟨⟨h1, h0⟩, h1⟩
  rw [(vkTangent h).coordChange_linear_comp 1 0 1 b hmem]
  apply ContinuousLinearMap.ext
  intro v
  exact (vkTangent h).coordChange_self 1 b h1 v

/-! ## The inverse of `H₁` and its continuity -/

lemma continuousAt_chartOfY (b : Vk) (hb : b ∈ gaugeUY) :
    ContinuousAt (fun b : Vk => (Submission.Milnor.vData (-2)).chartOfY 0 b) b :=
  (((Submission.Milnor.vData (-2)).chartOfY 0).continuousOn.continuousAt
    (((Submission.Milnor.vData (-2)).chartOfY 0).open_source.mem_nhds
      (by rw [chartOfY_source]; exact hb)))

lemma continuousAt_gaugeYNorm (b : Vk) (hb : b ∈ gaugeUY) : ContinuousAt gaugeYNorm b :=
  ((continuousAt_chartOfY b hb).fst).norm

/-- The six CLM identities used for the inverse laws of `H₁`. -/
lemma gauge_cc_identities
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) :
    (((vkTangent h).coordChange 1 0 b).comp ((vkTangent h).coordChange 0 1 b) = 1) ∧
    (((vkTangent h).coordChange 0 1 b).comp ((vkTangent h).coordChange 1 0 b) = 1) ∧
    ((targetCore.coordChange (true, true) (false, false) b).comp
        (targetCore.coordChange (false, false) (true, true) b) = 1) ∧
    ((targetCore.coordChange (false, false) (true, true) b).comp
        (targetCore.coordChange (true, true) (false, false) b) = 1) := by
  have h0 : b ∈ (vkTangent h).baseSet 0 := by rw [vkTangent_baseSet_zero h]; exact hb.1
  have h1 : b ∈ (vkTangent h).baseSet 1 := by rw [vkTangent_baseSet_one h]; exact hb.2
  have hff : b ∈ targetCore.baseSet (false, false) := gaugeUX_subset_targetCore_ff hb.1
  have htt : b ∈ targetCore.baseSet (true, true) := gaugeUY_subset_targetCore_tt hb.2
  have e1 : (vkTangent h).coordChange 0 0 b = 1 := by
    apply ContinuousLinearMap.ext; intro v
    exact (vkTangent h).coordChange_self 0 b h0 v
  have e2 : (vkTangent h).coordChange 1 1 b = 1 := by
    apply ContinuousLinearMap.ext; intro v
    exact (vkTangent h).coordChange_self 1 b h1 v
  have e3 : targetCore.coordChange (false, false) (false, false) b = 1 := by
    apply ContinuousLinearMap.ext; intro v
    exact targetCore.coordChange_self (false, false) b hff v
  have e4 : targetCore.coordChange (true, true) (true, true) b = 1 := by
    apply ContinuousLinearMap.ext; intro v
    exact targetCore.coordChange_self (true, true) b htt v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(vkTangent h).coordChange_linear_comp 0 1 0 b ⟨⟨h0, h1⟩, h0⟩, e1]
  · rw [(vkTangent h).coordChange_linear_comp 1 0 1 b ⟨⟨h1, h0⟩, h1⟩, e2]
  · rw [targetCore.coordChange_linear_comp (false, false) (true, true) (false, false) b
        ⟨⟨hff, htt⟩, hff⟩, e3]
  · rw [targetCore.coordChange_linear_comp (true, true) (false, false) (true, true) b
        ⟨⟨htt, hff⟩, htt⟩, e4]

lemma gaugeH1_comp_gaugeH1inv
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUY) : (gaugeH1 h b).comp (gaugeH1inv h b) = 1 := by
  by_cases h0 : gaugeYNorm b = 0
  · rw [gaugeH1, gaugeH1inv, if_pos h0, if_pos h0]
    apply ContinuousLinearMap.ext; intro v
    rfl
  · have hbX : b ∈ gaugeUX := gaugeUX_of_mem_gaugeUY b hb h0
    have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hbX, hb⟩
    obtain ⟨h1, h2, h3, h4⟩ := gauge_cc_identities h b hb'
    have hH : (gaugeH0 b).comp (gaugeH0inv b) = 1 := gaugeH0_comp_gaugeH0inv b
    rw [gaugeH1_eq h b hb', gaugeH1inv, if_neg h0]
    have p1 : ∀ y, (vkTangent h).coordChange 1 0 b ((vkTangent h).coordChange 0 1 b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) h1
    have pH : ∀ y, gaugeH0 b (gaugeH0inv b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) hH
    have p4 : ∀ y, targetCore.coordChange (false, false) (true, true) b
        (targetCore.coordChange (true, true) (false, false) b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) h4
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, p1, pH, p4, ContinuousLinearMap.one_apply]

lemma gaugeH1inv_comp_gaugeH1
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUY) : (gaugeH1inv h b).comp (gaugeH1 h b) = 1 := by
  by_cases h0 : gaugeYNorm b = 0
  · rw [gaugeH1, gaugeH1inv, if_pos h0, if_pos h0]
    apply ContinuousLinearMap.ext; intro v
    rfl
  · have hbX : b ∈ gaugeUX := gaugeUX_of_mem_gaugeUY b hb h0
    have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hbX, hb⟩
    obtain ⟨h1, h2, h3, h4⟩ := gauge_cc_identities h b hb'
    have hH : (gaugeH0inv b).comp (gaugeH0 b) = 1 := gaugeH0inv_comp_gaugeH0 b
    rw [gaugeH1_eq h b hb', gaugeH1inv, if_neg h0]
    have p2 : ∀ y, (vkTangent h).coordChange 0 1 b ((vkTangent h).coordChange 1 0 b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) h2
    have pH : ∀ y, gaugeH0inv b (gaugeH0 b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) hH
    have p3 : ∀ y, targetCore.coordChange (true, true) (false, false) b
        (targetCore.coordChange (false, false) (true, true) b y) = y :=
      fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) h3
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, p2, pH, p3, ContinuousLinearMap.one_apply]

/-! ## Continuity of `H₁` and `H₁⁻¹` -/

lemma gaugeH1inv_expr_eq_one
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUX ∩ gaugeUY) (h23 : gaugeYNorm b ≤ 2 / 3) :
    ((vkTangent h).coordChange 0 1 b).comp
      ((gaugeH0inv b).comp (targetCore.coordChange (true, true) (false, false) b)) = 1 := by
  have hkey := gaugeKey_all h b hb (three_halves_le_of_gaugeYNorm_le hb h23)
  obtain ⟨-, -, -, h4⟩ := gauge_cc_identities h b hb
  have pk : ∀ y, (vkTangent h).coordChange 0 1 b y
      = (targetCore.coordChange (false, false) (true, true) b) (gaugeH0 b y) :=
    fun y => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) hkey
  have pH : ∀ y, gaugeH0 b (gaugeH0inv b y) = y := fun y => congrArg
    (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y)
    (gaugeH0_comp_gaugeH0inv b)
  have p4 : ∀ y, targetCore.coordChange (false, false) (true, true) b
      (targetCore.coordChange (true, true) (false, false) b y) = y := fun y => congrArg
    (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f y) h4
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, pk, pH, p4, ContinuousLinearMap.one_apply]

lemma continuousWithinAt_gaugeH1
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUY) : ContinuousWithinAt (gaugeH1 h) gaugeUY b := by
  by_cases h0 : gaugeYNorm b = 0
  · have hmem : {b' : Vk | gaugeYNorm b' < 2 / 3} ∈ 𝓝 b :=
      (continuousAt_gaugeYNorm b hb).eventually
        (isOpen_Iio.mem_nhds (by rw [h0]; norm_num))
    have hev : (gaugeH1 h) =ᶠ[𝓝[gaugeUY] b]
        (fun _ => (1 : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8)) := by
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with b' hb' hbY
      rw [gaugeH1]
      split_ifs with h1
      · rfl
      · exact gaugeH1_expr_eq_one h b' ⟨gaugeUX_of_mem_gaugeUY b' hbY h1, hbY⟩ (le_of_lt hb')
    have hval : gaugeH1 h b = 1 := by rw [gaugeH1, if_pos h0]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev hval
  · have hbX : b ∈ gaugeUX := gaugeUX_of_mem_gaugeUY b hb h0
    have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hbX, hb⟩
    have hβc : ContinuousAt
        (fun y => (vkTangent h).coordChange 1 0 y) b :=
      ((vkTangent h).continuousOn_coordChange 1 0).continuousAt
        (Filter.inter_mem
          (((vkTangent h).isOpen_baseSet 1).mem_nhds (by rw [vkTangent_baseSet_one h]; exact hb))
          (((vkTangent h).isOpen_baseSet 0).mem_nhds (by rw [vkTangent_baseSet_zero h]; exact hbX)))
    have hDc : ContinuousAt
        (fun y => targetCore.coordChange (false, false) (true, true) y) b :=
      (targetCore.continuousOn_coordChange (false, false) (true, true)).continuousAt
        (Filter.inter_mem
          ((targetCore.isOpen_baseSet (false, false)).mem_nhds
            (gaugeUX_subset_targetCore_ff hbX))
          ((targetCore.isOpen_baseSet (true, true)).mem_nhds
            (gaugeUY_subset_targetCore_tt hb)))
    have hF : ContinuousAt (fun y => (targetCore.coordChange (false, false) (true, true) y).comp
        ((gaugeH0 y).comp ((vkTangent h).coordChange 1 0 y))) b :=
      hDc.clm_comp ((continuousAt_gaugeH0 b hbX).clm_comp hβc)
    have hmem : {b' : Vk | gaugeYNorm b' ≠ 0} ∈ 𝓝 b :=
      (continuousAt_gaugeYNorm b hb).eventually (isOpen_ne.mem_nhds h0)
    have hev : (gaugeH1 h) =ᶠ[𝓝[gaugeUY] b] (fun y =>
        (targetCore.coordChange (false, false) (true, true) y).comp
          ((gaugeH0 y).comp ((vkTangent h).coordChange 1 0 y))) := by
      filter_upwards [nhdsWithin_le_nhds hmem] with b' hb'
      rw [gaugeH1, if_neg hb']
    exact hF.continuousWithinAt.congr_of_eventuallyEq hev (gaugeH1_eq h b hb')

lemma continuousWithinAt_gaugeH1inv
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))
    (b : Vk) (hb : b ∈ gaugeUY) : ContinuousWithinAt (gaugeH1inv h) gaugeUY b := by
  by_cases h0 : gaugeYNorm b = 0
  · have hmem : {b' : Vk | gaugeYNorm b' < 2 / 3} ∈ 𝓝 b :=
      (continuousAt_gaugeYNorm b hb).eventually
        (isOpen_Iio.mem_nhds (by rw [h0]; norm_num))
    have hev : (gaugeH1inv h) =ᶠ[𝓝[gaugeUY] b]
        (fun _ => (1 : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8)) := by
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with b' hb' hbY
      rw [gaugeH1inv]
      split_ifs with h1
      · rfl
      · exact gaugeH1inv_expr_eq_one h b' ⟨gaugeUX_of_mem_gaugeUY b' hbY h1, hbY⟩ (le_of_lt hb')
    have hval : gaugeH1inv h b = 1 := by rw [gaugeH1inv, if_pos h0]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev hval
  · have hbX : b ∈ gaugeUX := gaugeUX_of_mem_gaugeUY b hb h0
    have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hbX, hb⟩
    have hαc : ContinuousAt (fun y => (vkTangent h).coordChange 0 1 y) b :=
      ((vkTangent h).continuousOn_coordChange 0 1).continuousAt
        (Filter.inter_mem
          (((vkTangent h).isOpen_baseSet 0).mem_nhds (by rw [vkTangent_baseSet_zero h]; exact hbX))
          (((vkTangent h).isOpen_baseSet 1).mem_nhds (by rw [vkTangent_baseSet_one h]; exact hb)))
    have hDc : ContinuousAt
        (fun y => targetCore.coordChange (true, true) (false, false) y) b :=
      (targetCore.continuousOn_coordChange (true, true) (false, false)).continuousAt
        (Filter.inter_mem
          ((targetCore.isOpen_baseSet (true, true)).mem_nhds
            (gaugeUY_subset_targetCore_tt hb))
          ((targetCore.isOpen_baseSet (false, false)).mem_nhds
            (gaugeUX_subset_targetCore_ff hbX)))
    have hG : ContinuousAt (fun y => ((vkTangent h).coordChange 0 1 y).comp
        ((gaugeH0inv y).comp (targetCore.coordChange (true, true) (false, false) y))) b :=
      hαc.clm_comp ((continuousAt_gaugeH0inv b hbX).clm_comp hDc)
    have hmem : {b' : Vk | gaugeYNorm b' ≠ 0} ∈ 𝓝 b :=
      (continuousAt_gaugeYNorm b hb).eventually (isOpen_ne.mem_nhds h0)
    have hev : (gaugeH1inv h) =ᶠ[𝓝[gaugeUY] b] (fun y =>
        ((vkTangent h).coordChange 0 1 y).comp
          ((gaugeH0inv y).comp (targetCore.coordChange (true, true) (false, false) y))) := by
      filter_upwards [nhdsWithin_le_nhds hmem] with b' hb'
      rw [gaugeH1inv, if_neg hb']
    exact hG.continuousWithinAt.congr_of_eventuallyEq hev (gaugeH1inv_eq h b hb')

lemma continuousOn_gaugeH1
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)) :
    ContinuousOn (gaugeH1 h) gaugeUY :=
  fun b hb => continuousWithinAt_gaugeH1 h b hb

lemma continuousOn_gaugeH1inv
    (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)) :
    ContinuousOn (gaugeH1inv h) gaugeUY :=
  fun b hb => continuousWithinAt_gaugeH1inv h b hb

end

end Work.Agree
