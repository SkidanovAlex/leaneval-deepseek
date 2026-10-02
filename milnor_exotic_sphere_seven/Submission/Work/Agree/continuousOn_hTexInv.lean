import Mathlib
import Submission.Work.Agree.continuousOn_hTex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the chart expression `hTexInv` of the inverse gauge

`Work.Agree.hTexInv a b i₁ i₂` is the chart expression of the point-dependent inverse gauge
`Work.Agree.gaugeInvOp` realising the inverse isomorphism `ℂ(L^{a-b}) ≅ ℂ(L^aR^b)`: in the source
chart `i₂` (for `ZZ (a-b) 0`) and the target chart `i₁` (for `ZZ a b`) it reads

`hTexInv a b i₁ i₂ p = cc₁ (indexAt p) i₁ p ∘L gaugeInvOp b p ∘L cc₂ i₂ (indexAt p) p`,

the exact mirror image of `Work.Agree.hTex` with the gauge replaced by its pointwise inverse.  The
proof is therefore the mirror image of `Work.Agree.continuousOn_hTex`: on `hemi0` the index map is
constantly `false` and the expression is a composite of continuous transition functions and the
continuous inverse gauge, while at `∞` (only reachable when `i₁ = i₂ = true`) it is locally the
identity because the twist factors cancel by `Work.Agree.shift_cancel_inv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Topology Set Filter

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## Continuity of the inverse gauge on `hemi0` -/

/-- The path `t ↦ dOpInv t` of complex-linear maps is continuous. -/
lemma continuous_dOpInv : Continuous dOpInv := by
  unfold dOpInv
  fun_prop

/-- On the open unit ball of the finite chart `gaugeInvOp` is the identity. -/
lemma gaugeInvOp_eq_one_of_mem_Uunit {b : ℤ} {p : S4} (hp : p ∈ Uunit) :
    gaugeInvOp b p = 1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  apply gaugeInvOp_of_sigR_zero
  show sigFun ‖x‖ = 0
  exact sigFun_of_le_one (le_of_lt hx)

/-- The inverse gauge is continuous at the origin of the finite chart. -/
lemma continuousWithinAt_gaugeInvOp_zero (b : ℤ) :
    ContinuousWithinAt (fun p : S4 => gaugeInvOp b p) hemi0
      (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq
    (show ContinuousWithinAt
      (fun _ : S4 => (1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
      hemi0 _ from continuous_const.continuousWithinAt) ?_ ?_
  · refine Filter.Eventually.filter_mono (nhdsWithin_le_nhds) ?_
    exact Filter.mem_of_superset (isOpen_Uunit.mem_nhds mem_Uunit_zero)
      (fun q hq => gaugeInvOp_eq_one_of_mem_Uunit hq)
  · exact gaugeInvOp_eq_one_of_mem_Uunit mem_Uunit_zero

/-- The inverse gauge is continuous at every point of `hemi0` different from the origin. -/
lemma continuousAt_gaugeInvOp_of_ne (b : ℤ) {p : S4}
    (hpinf : p ≠ OnePoint.infty) (hpzero : p ≠ (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)) :
    ContinuousAt (fun p : S4 => gaugeInvOp b p) p := by
  have hp : p ∈ hemi0 ∩ hemi1 := ⟨hpinf, hpzero⟩
  have h1 : ContinuousAt (fun p : S4 => coord0 p) p :=
    (continuousOn_coord0.continuousWithinAt hp.1).continuousAt (isOpen_hemi0.mem_nhds hp.1)
  have hsig : ContinuousAt sigR p := continuous_sigFun.continuousAt.comp h1.norm
  have hD : ContinuousAt (fun p : S4 => dOpInv (sigR p)) p :=
    continuous_dOpInv.continuousAt.comp hsig
  have hA : ContinuousAt (fun p : S4 => gaugeA b p) p := by
    have hq : ContinuousAt (fun q : Quaternion ℝ => qTwist b 0 q) (uDir p) :=
      (continuousOn_qTwist b 0).continuousAt (isOpen_ne.mem_nhds (uDir_ne_zero p))
    exact Work.Thom.continuous_cxTrans.continuousAt.comp
      (hq.comp ((continuousOn_uDir.continuousWithinAt hp).continuousAt
        ((isOpen_hemi0.inter isOpen_hemi1).mem_nhds hp)))
  have hB : ContinuousAt (fun p : S4 => gaugeB b p) p := by
    have hq : ContinuousAt (fun q : Quaternion ℝ => qTwist (-b) 0 q) (uDir p) :=
      (continuousOn_qTwist (-b) 0).continuousAt (isOpen_ne.mem_nhds (uDir_ne_zero p))
    exact Work.Thom.continuous_cxTrans.continuousAt.comp
      (hq.comp ((continuousOn_uDir.continuousWithinAt hp).continuousAt
        ((isOpen_hemi0.inter isOpen_hemi1).mem_nhds hp)))
  have h : ContinuousAt (fun p : S4 =>
      dOpInv (sigR p) * (gaugeA b p * (dOpInv (sigR p) * gaugeB b p))) p :=
    hD.mul (hA.mul (hD.mul hB))
  simpa only [gaugeInvOp] using h

/-- **The inverse gauge is continuous on the first chart** `hemi0`. -/
lemma continuousOn_gaugeInvOp_hemi0 (b : ℤ) :
    ContinuousOn (fun p : S4 => gaugeInvOp b p) hemi0 := by
  intro p hp
  by_cases hp0 : p = (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)
  · rw [hp0]; exact continuousWithinAt_gaugeInvOp_zero b
  · exact (continuousAt_gaugeInvOp_of_ne b hp hp0).continuousWithinAt

/-! ## The inverse gauge expression is locally the identity near `∞` -/

/-- **Far out in the second chart the chart expression `hTexInv` is the identity**: for
`‖x‖ > 2` the inverse gauge is the twist `cxTrans (qTwist (-b) (-b) (uDir x))` and the two
clutching twists cancel against it by `shift_cancel_inv`. -/
lemma hTexInv_true_true_coe (a b : ℤ) (x : EuclideanSpace ℝ (Fin 4)) (hx : 2 < ‖x‖) :
    hTexInv a b true true (↑x : S4) = 1 := by
  have hne : (↑x : S4) ≠ OnePoint.infty := OnePoint.coe_ne_infty x
  have hg : gaugeInvOp b (↑x : S4) = Work.Thom.cxTrans (qTwist (-b) (-b) (uDir (↑x : S4))) :=
    gaugeInvOp_of_sigR_one (sigR_of_two_le (le_of_lt hx))
  rw [hTexInv, ZZ_indexAt_of_ne_infty a b hne, ZZ_indexAt_of_ne_infty (a - b) 0 hne,
    ZZ_coordChange, ZZ_coordChange, ct_false_true a b (↑x), ct_true_false (a - b) 0 (↑x),
    hg, show (-(a - b) : ℤ) = b - a from by ring, show (-0 : ℤ) = 0 from by ring,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  exact shift_cancel_inv a b (uDir (↑x : S4)) (uDir_ne_zero _)

/-- **At `∞` the chart expression `hTexInv` is the identity.** -/
lemma hTexInv_true_true_infty (a b : ℤ) : hTexInv a b true true (OnePoint.infty : S4) = 1 := by
  have hg : gaugeInvOp b (OnePoint.infty : S4) = 1 := by
    apply gaugeInvOp_of_sigR_zero
    show sigFun ‖(0 : EuclideanSpace ℝ (Fin 4))‖ = 0
    exact sigFun_of_le_one (by norm_num)
  rw [hTexInv, ZZ_indexAt_infty a b, ZZ_indexAt_infty (a - b) 0,
    coordChange_true_true_infty (a - b) 0, coordChange_true_true_infty a b, hg]
  ext v
  simp

/-- `hTexInv a b true true` is eventually the identity at `∞`. -/
lemma eventually_hTexInv_true_true_infty (a b : ℤ) :
    hTexInv a b true true =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)] (fun _ => 1) := by
  have hU : Ufar ∈ 𝓝 (OnePoint.infty : S4) := isOpen_Ufar.mem_nhds mem_Ufar_infty
  have hev : hTexInv a b true true =ᶠ[𝓝 (OnePoint.infty : S4)] (fun _ => 1) :=
    Filter.mem_of_superset hU (fun q hq => by
      rcases hq with hq | ⟨x, hx, rfl⟩
      · rw [hq]; exact hTexInv_true_true_infty a b
      · exact hTexInv_true_true_coe a b x hx)
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi1] (OnePoint.infty : S4) ≤ 𝓝 (OnePoint.infty : S4)) hev

/-- **`hTexInv a b true true` is continuous on the second chart.** -/
lemma continuousOn_hTexInv_true_true (a b : ℤ) :
    ContinuousOn (hTexInv a b true true) hemi1 := by
  intro p hp
  by_cases hpin : p = OnePoint.infty
  · rw [hpin]
    exact ContinuousWithinAt.congr_of_eventuallyEq
      (show ContinuousWithinAt
        (fun _ : S4 => (1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
        hemi1 _ from continuous_const.continuousWithinAt)
      (eventually_hTexInv_true_true_infty a b) (hTexInv_true_true_infty a b)
  · have hp0 : p ∈ hemi0 := hpin
    have hopen1 : IsOpen ((ZZ a b).baseSet false ∩ (ZZ a b).baseSet true) :=
      ((ZZ a b).isOpen_baseSet false).inter ((ZZ a b).isOpen_baseSet true)
    have hopen2 : IsOpen ((ZZ (a - b) 0).baseSet true ∩ (ZZ (a - b) 0).baseSet false) :=
      ((ZZ (a - b) 0).isOpen_baseSet true).inter ((ZZ (a - b) 0).isOpen_baseSet false)
    have hc1 : ContinuousAt (fun q : S4 => (ZZ a b).coordChange false true q) p :=
      ((ZZ a b).continuousOn_coordChange false true).continuousAt
        (hopen1.mem_nhds ⟨hp0, hp⟩)
    have hc2 : ContinuousAt (fun q : S4 => (ZZ (a - b) 0).coordChange true false q) p :=
      ((ZZ (a - b) 0).continuousOn_coordChange true false).continuousAt
        (hopen2.mem_nhds ⟨hp, hp0⟩)
    have hcg : ContinuousAt (fun q : S4 => gaugeInvOp b q) p :=
      (continuousOn_gaugeInvOp_hemi0 b).continuousAt (isOpen_hemi0.mem_nhds hp0)
    have hca : ContinuousAt (fun q : S4 =>
        (ZZ a b).coordChange false true q ∘SL
          (gaugeInvOp b q ∘SL (ZZ (a - b) 0).coordChange true false q)) p :=
      hc1.clm_comp (hcg.clm_comp hc2)
    refine ContinuousWithinAt.congr_of_eventuallyEq hca.continuousWithinAt ?_ ?_
    · have hU : ({OnePoint.infty}ᶜ : Set S4) ∈ 𝓝[hemi1] p :=
        nhdsWithin_le_nhds ((OnePoint.isClosed_infty.isOpen_compl).mem_nhds hpin)
      filter_upwards [hU] with q hq
      rw [hTexInv, ZZ_indexAt_of_ne_infty a b hq, ZZ_indexAt_of_ne_infty (a - b) 0 hq]
    · rw [hTexInv, ZZ_indexAt_of_ne_infty a b hpin, ZZ_indexAt_of_ne_infty (a - b) 0 hpin]

/-! ## The theorem -/

/-- **The chart expression of the inverse gauge is continuous** whenever the relevant base set
lies in the first chart (`hemi0`). -/
lemma continuousOn_hTexInv_of_subset_hemi0 (a b : ℤ) (i₁ i₂ : Bool)
    (hsub : ((ZZ (a - b) 0).baseSet i₂ ∩ (ZZ a b).baseSet i₁) ⊆ hemi0) :
    ContinuousOn (hTexInv a b i₁ i₂) ((ZZ (a - b) 0).baseSet i₂ ∩ (ZZ a b).baseSet i₁) := by
  have hT1 : ContinuousOn (fun p : S4 => (ZZ a b).coordChange false i₁ p)
      ((ZZ (a - b) 0).baseSet i₂ ∩ (ZZ a b).baseSet i₁) :=
    ((ZZ a b).continuousOn_coordChange false i₁).mono (fun p hp => ⟨hsub hp, hp.2⟩)
  have hg : ContinuousOn (fun p : S4 => gaugeInvOp b p)
      ((ZZ (a - b) 0).baseSet i₂ ∩ (ZZ a b).baseSet i₁) :=
    (continuousOn_gaugeInvOp_hemi0 b).mono hsub
  have hT2 : ContinuousOn (fun p : S4 => (ZZ (a - b) 0).coordChange i₂ false p)
      ((ZZ (a - b) 0).baseSet i₂ ∩ (ZZ a b).baseSet i₁) :=
    ((ZZ (a - b) 0).continuousOn_coordChange i₂ false).mono (fun p hp => ⟨hp.1, hsub hp⟩)
  refine ContinuousOn.congr (hT1.clm_comp (hg.clm_comp hT2)) (fun p hp => ?_)
  have hne : p ≠ OnePoint.infty := hsub hp
  rw [hTexInv, ZZ_indexAt_of_ne_infty a b hne, ZZ_indexAt_of_ne_infty (a - b) 0 hne]

theorem continuousOn_hTexInv (a b : ℤ) (i₁ i₂ : Bool) :
    ContinuousOn (Work.Agree.hTexInv a b i₁ i₂)
      ((Work.Agree.ZZ (a - b) 0).baseSet i₂ ∩ (Work.Agree.ZZ a b).baseSet i₁) := by
  cases i₁ <;> cases i₂
  · exact continuousOn_hTexInv_of_subset_hemi0 a b false false (fun p hp => hp.1)
  · exact continuousOn_hTexInv_of_subset_hemi0 a b false true (fun p hp => hp.2)
  · exact continuousOn_hTexInv_of_subset_hemi0 a b true false (fun p hp => hp.1)
  · simpa only [baseSet_ZZ_true (a - b) 0, baseSet_ZZ_true a b, Set.inter_self]
      using continuousOn_hTexInv_true_true a b

end

end Work.Agree
