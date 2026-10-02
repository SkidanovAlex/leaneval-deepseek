import Mathlib
import Submission.Work.Agree.clutchShiftDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the chart expression `hTex` of the gauge

`Work.Agree.hTex a b i₁ i₂` is the chart expression of the point-dependent gauge
`Work.Agree.gaugeOp` realising the isomorphism `ℂ(L^aR^b) ≅ ℂ(L^{a-b})` (see
`Submission/Work/Agree/clutchShiftDefs.lean`): in the source chart `i₁` and the target chart `i₂`
it reads

`hTex a b i₁ i₂ p = cc₂ (indexAt p) i₂ p ∘L gaugeOp b p ∘L cc₁ i₁ (indexAt p) p`,

where `cc₁`, `cc₂` are the (clutching) transition functions of `ZZ a b = ℂ(L^aR^b)` and
`ZZ (a-b) 0 = ℂ(L^{a-b})`.  The theorem below is its continuity on the common base set
`baseSet i₁ ∩ baseSet i₂`, the hypothesis needed to build the bundle isomorphism.

The only subtlety is the index map `indexAt p = if p = ∞ then true else false` of the two-chart
model, which is *not* continuous at `∞`.  It is however irrelevant:

* on `hemi0 = {p | p ≠ ∞}`, `indexAt ≡ false`, and `gaugeOp` is continuous there — its apparent
  discontinuities cancel, both near the origin (`sigR = 0` on the unit ball, where `gaugeOp = 1`)
  and near `∞` (`sigR = 1`, where `gaugeOp` is the twisting `cxTrans (qTwist b b (uDir p))`);
* the only case in which `∞` lies in the base set is `i₁ = i₂ = true` (the base set is then
  `hemi1 = {p | p ≠ 0}`), and there `hTex` is locally constant `1` near `∞`: for `‖coord₀ p‖ > 2`
  the four twist factors of the two clutching functions and of the gauge cancel
  (`Work.Agree.shift_cancel`), and at `∞` itself every factor is the identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Topology Set Filter

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The base sets, the index map and the transition functions of `ZZ a b` -/

/-- The base set of the two-chart bundle `ZZ a b`: `hemi1` for `true`, `hemi0` for `false`. -/
lemma baseSet_ZZ (a b : ℤ) (i : Bool) : (ZZ a b).baseSet i = if i then hemi1 else hemi0 := by
  rw [ZZ, Work.Thom.complexificationCore_baseSet, clutchBundle_baseSet]

/-- `(ZZ a b).baseSet false` is `hemi0` (definitionally). -/
lemma baseSet_ZZ_false (a b : ℤ) : (ZZ a b).baseSet false = hemi0 := by
  rw [baseSet_ZZ]; rfl

/-- `(ZZ a b).baseSet true` is `hemi1` (definitionally). -/
lemma baseSet_ZZ_true (a b : ℤ) : (ZZ a b).baseSet true = hemi1 := by
  rw [baseSet_ZZ]; rfl

/-- Away from `∞` the index map of `ZZ a b` is `false`. -/
lemma ZZ_indexAt_of_ne_infty (a b : ℤ) {p : S4} (hp : p ≠ OnePoint.infty) :
    (ZZ a b).indexAt p = false := by
  classical
  rw [ZZ, Work.Thom.complexificationCore_indexAt]
  show (if p = OnePoint.infty then true else false) = false
  rw [if_neg hp]

/-- At `∞` the index map of `ZZ a b` is `true`. -/
lemma ZZ_indexAt_infty (a b : ℤ) : (ZZ a b).indexAt (OnePoint.infty : S4) = true := by
  classical
  rw [ZZ, Work.Thom.complexificationCore_indexAt]
  show (if (OnePoint.infty : S4) = OnePoint.infty then true else false) = true
  rw [if_pos rfl]

/-- The transition functions of `ZZ a b` are the complexifications of the clutching twists. -/
lemma ZZ_coordChange (a b : ℤ) (i j : Bool) (p : S4) :
    (ZZ a b).coordChange i j p = Work.Thom.cxTrans (ct a b i j p) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Work.Thom.complexificationCore_coordChange, clutchBundle_coordChange]

/-- `∞` lies in the second chart. -/
lemma mem_baseSet_ZZ_true_infty (a b : ℤ) : (OnePoint.infty : S4) ∈ (ZZ a b).baseSet true := by
  rw [baseSet_ZZ]; simp [hemi1]

/-- At `∞` the transition functions of `ZZ a b` are the identity. -/
lemma coordChange_true_true_infty (a b : ℤ) :
    (ZZ a b).coordChange true true (OnePoint.infty : S4) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [(ZZ a b).coordChange_self true OnePoint.infty (mem_baseSet_ZZ_true_infty a b) v]
  rfl

/-! ## Continuity of the gauge on `hemi0` -/

/-- The path `t ↦ dOp t` of complex-linear maps is continuous. -/
lemma continuous_dOp : Continuous dOp := by
  unfold dOp
  fun_prop

/-- The open unit ball of the finite chart of `S⁴`. -/
def Uunit : Set S4 := (↑) '' {x : EuclideanSpace ℝ (Fin 4) | ‖x‖ < 1}

lemma isOpen_Uunit : IsOpen Uunit := by
  have hset : Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1 = {x | ‖x‖ < 1} := by
    ext x; simp [Metric.mem_ball, dist_zero_right]
  rw [Uunit, ← hset]
  exact OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball

lemma mem_Uunit_zero : (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) ∈ Uunit := ⟨0, by simp, rfl⟩

/-- On the open unit ball of the finite chart the radial cutoff `sigR` vanishes, so the gauge is
the identity. -/
lemma gaugeOp_eq_one_of_mem_Uunit {b : ℤ} {p : S4} (hp : p ∈ Uunit) : gaugeOp b p = 1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  apply gaugeOp_of_sigR_zero
  show sigFun ‖x‖ = 0
  exact sigFun_of_le_one (le_of_lt hx)

/-- The gauge is continuous at the origin of the finite chart (where it equals `1` on the unit
ball, although the twisting direction `uDir` is discontinuous there). -/
lemma continuousWithinAt_gaugeOp_zero (b : ℤ) :
    ContinuousWithinAt (fun p : S4 => gaugeOp b p) hemi0
      (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) := by
  refine ContinuousWithinAt.congr_of_eventuallyEq
    (show ContinuousWithinAt
      (fun _ : S4 => (1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
      hemi0 _ from continuous_const.continuousWithinAt) ?_ ?_
  · refine Filter.Eventually.filter_mono (nhdsWithin_le_nhds) ?_
    exact Filter.mem_of_superset (isOpen_Uunit.mem_nhds mem_Uunit_zero)
      (fun q hq => gaugeOp_eq_one_of_mem_Uunit hq)
  · exact gaugeOp_eq_one_of_mem_Uunit mem_Uunit_zero

/-- The gauge is continuous at every point of `hemi0` different from the origin. -/
lemma continuousAt_gaugeOp_of_ne (b : ℤ) {p : S4}
    (hpinf : p ≠ OnePoint.infty) (hpzero : p ≠ (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)) :
    ContinuousAt (fun p : S4 => gaugeOp b p) p := by
  have hp : p ∈ hemi0 ∩ hemi1 := ⟨hpinf, hpzero⟩
  have h1 : ContinuousAt (fun p : S4 => coord0 p) p :=
    (continuousOn_coord0.continuousWithinAt hp.1).continuousAt (isOpen_hemi0.mem_nhds hp.1)
  have hsig : ContinuousAt sigR p := continuous_sigFun.continuousAt.comp h1.norm
  have hD : ContinuousAt (fun p : S4 => dOp (sigR p)) p :=
    continuous_dOp.continuousAt.comp hsig
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
      gaugeA b p * (dOp (sigR p) * (gaugeB b p * dOp (sigR p)))) p :=
    hA.mul (hD.mul (hB.mul hD))
  simpa only [gaugeOp] using h

/-- **The gauge is continuous on the first chart** `hemi0`.  (It is *not* continuous on all of
`S⁴`: near `∞` its limit depends on the direction of approach.) -/
lemma continuousOn_gaugeOp_hemi0 (b : ℤ) :
    ContinuousOn (fun p : S4 => gaugeOp b p) hemi0 := by
  intro p hp
  by_cases hp0 : p = (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)
  · rw [hp0]; exact continuousWithinAt_gaugeOp_zero b
  · exact (continuousAt_gaugeOp_of_ne b hp hp0).continuousWithinAt

/-! ## The gauge is locally the identity near `∞` -/

/-- A neighbourhood of `∞` on which the gauge expression of `hTex` is the identity. -/
def Ufar : Set S4 := {OnePoint.infty} ∪ (↑) '' {x : EuclideanSpace ℝ (Fin 4) | 2 < ‖x‖}

lemma isOpen_Ufar : IsOpen Ufar := by
  have hpre : ((↑) : EuclideanSpace ℝ (Fin 4) → S4) ⁻¹' Ufar
      = {x : EuclideanSpace ℝ (Fin 4) | 2 < ‖x‖} := by
    ext x
    simp only [Set.mem_preimage, Ufar, Set.mem_union, Set.mem_singleton_iff, OnePoint.coe_ne_infty,
      false_or, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [OnePoint.coe_injective hyx] at hy
    · exact fun h => ⟨x, h, rfl⟩
  rw [OnePoint.isOpen_iff_of_mem' (by simp [Ufar]), hpre]
  constructor
  · have hc : ({x : EuclideanSpace ℝ (Fin 4) | 2 < ‖x‖})ᶜ
        = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, Metric.mem_closedBall,
        dist_zero_right]
    rw [hc]
    exact isCompact_closedBall 0 2
  · exact isOpen_lt continuous_const continuous_norm

lemma mem_Ufar_infty : (OnePoint.infty : S4) ∈ Ufar := Or.inl rfl

/-- **Far out in the second chart the chart expression `hTex` is the identity**: for
`‖x‖ > 2` the gauge is the twist `cxTrans (qTwist b b (uDir x))` and the two clutching twists
cancel against it. -/
lemma hTex_true_true_coe (a b : ℤ) (x : EuclideanSpace ℝ (Fin 4)) (hx : 2 < ‖x‖) :
    hTex a b true true (↑x : S4) = 1 := by
  have hne : (↑x : S4) ≠ OnePoint.infty := OnePoint.coe_ne_infty x
  have hg : gaugeOp b (↑x : S4) = Work.Thom.cxTrans (qTwist b b (uDir (↑x : S4))) :=
    gaugeOp_of_sigR_one (sigR_of_two_le (le_of_lt hx))
  rw [hTex, ZZ_indexAt_of_ne_infty a b hne, ZZ_indexAt_of_ne_infty (a - b) 0 hne,
    ZZ_coordChange, ZZ_coordChange, hg, ← ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.mul_def]
  exact shift_cancel a b (uDir (↑x : S4)) (uDir_ne_zero _)

/-- **At `∞` the chart expression `hTex` is the identity**: both transition functions and the
gauge are the identity there. -/
lemma hTex_true_true_infty (a b : ℤ) : hTex a b true true (OnePoint.infty : S4) = 1 := by
  have hg : gaugeOp b (OnePoint.infty : S4) = 1 := by
    apply gaugeOp_of_sigR_zero
    show sigFun ‖(0 : EuclideanSpace ℝ (Fin 4))‖ = 0
    exact sigFun_of_le_one (by norm_num)
  rw [hTex, ZZ_indexAt_infty a b, ZZ_indexAt_infty (a - b) 0,
    coordChange_true_true_infty (a - b) 0, coordChange_true_true_infty a b, hg]
  ext v
  simp

/-- `hTex a b true true` is eventually the identity at `∞` (within the second chart, which is its
base set there). -/
lemma eventually_hTex_true_true_infty (a b : ℤ) :
    hTex a b true true =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)] (fun _ => 1) := by
  have hU : Ufar ∈ 𝓝 (OnePoint.infty : S4) := isOpen_Ufar.mem_nhds mem_Ufar_infty
  have hev : hTex a b true true =ᶠ[𝓝 (OnePoint.infty : S4)] (fun _ => 1) :=
    Filter.mem_of_superset hU (fun q hq => by
      rcases hq with hq | ⟨x, hx, rfl⟩
      · rw [hq]; exact hTex_true_true_infty a b
      · exact hTex_true_true_coe a b x hx)
  exact Filter.Eventually.filter_mono
    (nhdsWithin_le_nhds : 𝓝[hemi1] (OnePoint.infty : S4) ≤ 𝓝 (OnePoint.infty : S4)) hev

/-- **`hTex a b true true` is continuous on the second chart.**  At `∞` the index map jumps, but
the chart expression is locally the identity there. -/
lemma continuousOn_hTex_true_true (a b : ℤ) :
    ContinuousOn (hTex a b true true) hemi1 := by
  intro p hp
  by_cases hpin : p = OnePoint.infty
  · rw [hpin]
    exact ContinuousWithinAt.congr_of_eventuallyEq
      (show ContinuousWithinAt
        (fun _ : S4 => (1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
        hemi1 _ from continuous_const.continuousWithinAt)
      (eventually_hTex_true_true_infty a b) (hTex_true_true_infty a b)
  · have hp0 : p ∈ hemi0 := hpin
    have hopen1 : IsOpen ((ZZ a b).baseSet true ∩ (ZZ a b).baseSet false) :=
      ((ZZ a b).isOpen_baseSet true).inter ((ZZ a b).isOpen_baseSet false)
    have hopen2 : IsOpen ((ZZ (a - b) 0).baseSet false ∩ (ZZ (a - b) 0).baseSet true) :=
      ((ZZ (a - b) 0).isOpen_baseSet false).inter ((ZZ (a - b) 0).isOpen_baseSet true)
    have hc1 : ContinuousAt (fun q : S4 => (ZZ a b).coordChange true false q) p :=
      ((ZZ a b).continuousOn_coordChange true false).continuousAt
        (hopen1.mem_nhds ⟨hp, hp0⟩)
    have hc2 : ContinuousAt (fun q : S4 => (ZZ (a - b) 0).coordChange false true q) p :=
      ((ZZ (a - b) 0).continuousOn_coordChange false true).continuousAt
        (hopen2.mem_nhds ⟨hp0, hp⟩)
    have hcg : ContinuousAt (fun q : S4 => gaugeOp b q) p :=
      (continuousOn_gaugeOp_hemi0 b).continuousAt (isOpen_hemi0.mem_nhds hp0)
    have hca : ContinuousAt (fun q : S4 =>
        (ZZ (a - b) 0).coordChange false true q ∘SL
          (gaugeOp b q ∘SL (ZZ a b).coordChange true false q)) p :=
      hc2.clm_comp (hcg.clm_comp hc1)
    refine ContinuousWithinAt.congr_of_eventuallyEq hca.continuousWithinAt ?_ ?_
    · have hU : ({OnePoint.infty}ᶜ : Set S4) ∈ 𝓝[hemi1] p :=
        nhdsWithin_le_nhds ((OnePoint.isClosed_infty.isOpen_compl).mem_nhds hpin)
      filter_upwards [hU] with q hq
      rw [hTex, ZZ_indexAt_of_ne_infty a b hq, ZZ_indexAt_of_ne_infty (a - b) 0 hq]
    · rw [hTex, ZZ_indexAt_of_ne_infty a b hpin, ZZ_indexAt_of_ne_infty (a - b) 0 hpin]

/-! ## The theorem -/

/-- **The chart expression of the gauge is continuous** on the intersection of the two charts'
base sets, whenever that intersection lies in the first chart (`hemi0`).  There the index map of
both bundles is constantly `false`, so the expression is a composite of continuous transition
functions and the continuous gauge. -/
lemma continuousOn_hTex_of_subset_hemi0 (a b : ℤ) (i₁ i₂ : Bool)
    (hsub : ((ZZ a b).baseSet i₁ ∩ (ZZ (a - b) 0).baseSet i₂) ⊆ hemi0) :
    ContinuousOn (hTex a b i₁ i₂) ((ZZ a b).baseSet i₁ ∩ (ZZ (a - b) 0).baseSet i₂) := by
  have hT1 : ContinuousOn (fun p : S4 => (ZZ a b).coordChange i₁ false p)
      ((ZZ a b).baseSet i₁ ∩ (ZZ (a - b) 0).baseSet i₂) :=
    ((ZZ a b).continuousOn_coordChange i₁ false).mono (fun p hp => ⟨hp.1, hsub hp⟩)
  have hg : ContinuousOn (fun p : S4 => gaugeOp b p)
      ((ZZ a b).baseSet i₁ ∩ (ZZ (a - b) 0).baseSet i₂) :=
    (continuousOn_gaugeOp_hemi0 b).mono hsub
  have hT2 : ContinuousOn (fun p : S4 => (ZZ (a - b) 0).coordChange false i₂ p)
      ((ZZ a b).baseSet i₁ ∩ (ZZ (a - b) 0).baseSet i₂) :=
    ((ZZ (a - b) 0).continuousOn_coordChange false i₂).mono (fun p hp => ⟨hsub hp, hp.2⟩)
  refine ContinuousOn.congr (hT2.clm_comp (hg.clm_comp hT1)) (fun p hp => ?_)
  have hne : p ≠ OnePoint.infty := hsub hp
  rw [hTex, ZZ_indexAt_of_ne_infty a b hne, ZZ_indexAt_of_ne_infty (a - b) 0 hne]

theorem continuousOn_hTex (a b : ℤ) (i₁ i₂ : Bool) :
    ContinuousOn (Work.Agree.hTex a b i₁ i₂)
      ((Work.Agree.ZZ a b).baseSet i₁ ∩ (Work.Agree.ZZ (a - b) 0).baseSet i₂) := by
  cases i₁ <;> cases i₂
  · exact continuousOn_hTex_of_subset_hemi0 a b false false (fun p hp => hp.1)
  · exact continuousOn_hTex_of_subset_hemi0 a b false true (fun p hp => hp.1)
  · exact continuousOn_hTex_of_subset_hemi0 a b true false (fun p hp => hp.2)
  · simpa only [baseSet_ZZ_true (a - b) 0, baseSet_ZZ_true a b, Set.inter_self]
      using continuousOn_hTex_true_true a b

end

end Work.Agree
