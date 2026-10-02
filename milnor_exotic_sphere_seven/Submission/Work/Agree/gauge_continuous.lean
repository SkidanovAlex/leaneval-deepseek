import Mathlib
import Submission.Work.Agree.gaugeDefs
import Submission.Work.Milnor.vMap_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the gauge `H₀` and of its inverse `H₀⁻¹` on the first hemisphere

The gauge `gaugeH0` (and its explicit inverse `gaugeH0inv`) is the block matrix
`[[η J, 0], [a C⁻¹B, 1]]`, where
* `η = etaCut ‖gaugeX ·‖`, `a = aCut ‖gaugeX ·‖` are scalars,
* `B = ∂(vMap (-2))/∂x` blows up like `1/‖gaugeX‖` near `gaugeX = 0`.

Every entry is continuous wherever `gaugeX ≠ 0`, and the `(2,1)` entry carries the cutoff `a`,
which vanishes for `‖gaugeX‖ ≤ 1`: so the only non-trivial point is that the cutoff kills the
blow-up of `B` near the zero set of `gaugeX`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses
open Submission.Glue

noncomputable section

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "HH" => Quaternion ℝ

/-! ## The chart coordinate -/

/-- `chartOfX 0` is continuous at every point of its source, the hemisphere `gaugeUX`. -/
lemma continuousAt_chartOfX (b : Vk) (hb : b ∈ gaugeUX) :
    ContinuousAt (fun b : Vk => (Submission.Milnor.vData (-2)).chartOfX 0 b) b := by
  have hsrc : b ∈ ((Submission.Milnor.vData (-2)).chartOfX
      (0 : Submission.Milnor.MSpace8)).source := by
    rw [chartOfX_source]
    exact hb
  exact OpenPartialHomeomorph.continuousAt _ hsrc

/-- The X-chart coordinate `gaugeX` is continuous at every point of `gaugeUX`. -/
lemma continuousAt_gaugeX (b : Vk) (hb : b ∈ gaugeUX) : ContinuousAt gaugeX b := by
  show ContinuousAt (fun b : Vk => ((Submission.Milnor.vData (-2)).chartOfX 0 b).1) b
  exact (continuousAt_chartOfX b hb).fst

/-- The norm `‖gaugeX ·‖` is continuous at every point of `gaugeUX`. -/
lemma continuousAt_norm_gaugeX (b : Vk) (hb : b ∈ gaugeUX) :
    ContinuousAt (fun b => ‖gaugeX b‖) b :=
  continuous_norm.continuousAt.comp (continuousAt_gaugeX b hb)

/-- The unit direction `gaugeU` is continuous at the points where `gaugeX ≠ 0`. -/
lemma continuousAt_gaugeU (b : Vk) (hb : b ∈ gaugeUX) (h0 : gaugeX b ≠ 0) :
    ContinuousAt gaugeU b := by
  have hdir : ContinuousAt
      (fun x : E4 => ((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : HH))
      (gaugeX b) := by
    have hset : {x : E4 | x ≠ 0} ∈ 𝓝 (gaugeX b) := isOpen_ne.mem_nhds h0
    refine (Work.Milnor.dirVal_contMDiffOn.continuousOn.continuousAt hset).congr ?_
    filter_upwards [hset] with x hx
    exact (Work.Milnor.unitDir_coe x hx).symm
  have h := hdir.comp (continuousAt_gaugeX b hb)
  show ContinuousAt
    (fun b : Vk => ((Submission.Milnor.unitDir (gaugeX b) : Submission.Milnor.QS3) : HH)) b
  simpa only [Function.comp_def] using h

/-! ## The off-diagonal block `C⁻¹ B` -/

/-- `gaugeCinv` is continuous at the points where `gaugeX ≠ 0`. -/
lemma continuousAt_gaugeCinv (b : Vk) (hb : b ∈ gaugeUX) (h0 : gaugeX b ≠ 0) :
    ContinuousAt gaugeCinv b := by
  have hq : ContinuousAt (fun q : HH => qTwist (-2) 1 q) (gaugeU b) :=
    (continuousOn_qTwist (-2) 1).continuousAt (isOpen_ne.mem_nhds (gaugeU_ne_zero b))
  have hc2 : Continuous (fun M : E4 →L[ℝ] E4 => M.comp ofQ) :=
    (continuous_id (X := E4 →L[ℝ] E4)).clm_comp
      (continuous_const : Continuous (fun _ : E4 →L[ℝ] E4 => ofQ))
  have hc1 : Continuous (fun N : HH →L[ℝ] E4 => toQ.comp N) :=
    (continuous_const : Continuous (fun _ : HH →L[ℝ] E4 => toQ)).clm_comp
      (continuous_id (X := HH →L[ℝ] E4))
  have s1 : ContinuousAt (fun b => qTwist (-2) 1 (gaugeU b)) b :=
    hq.comp (continuousAt_gaugeU b hb h0)
  have s2 : ContinuousAt (fun b => (qTwist (-2) 1 (gaugeU b)).comp ofQ) b :=
    hc2.continuousAt.comp s1
  have s3 : ContinuousAt (fun b => toQ.comp ((qTwist (-2) 1 (gaugeU b)).comp ofQ)) b :=
    hc1.continuousAt.comp s2
  show ContinuousAt (fun b : Vk => toQ.comp ((qTwist (-2) 1 (gaugeU b)).comp ofQ)) b
  exact s3

/-- The derivative `fderiv (vMap (-2))` is continuous at the points with `x.1 ≠ 0`. -/
lemma continuousAt_fderiv_vMap (x : Submission.Milnor.MSpace8) (hx : x.1 ≠ 0) :
    ContinuousAt
      (fun x : Submission.Milnor.MSpace8 => fderiv ℝ (Submission.Milnor.vMap (-2)) x) x := by
  have hs : IsOpen {x : Submission.Milnor.MSpace8 | x.1 ≠ 0} :=
    isOpen_ne_fun continuous_fst continuous_const
  have hcd : ContDiffOn ℝ ∞ (Submission.Milnor.vMap (-2))
      {x : Submission.Milnor.MSpace8 | x.1 ≠ 0} :=
    contMDiffOn_iff_contDiffOn.mp (Work.Milnor.vMap_smooth (-2)).1
  exact (ContDiffOn.continuousOn_fderiv_of_isOpen hcd hs (by norm_num)).continuousAt
    (hs.mem_nhds hx)

/-- `gaugeBOff` is continuous at the points where `gaugeX ≠ 0`. -/
lemma continuousAt_gaugeBOff (b : Vk) (hb : b ∈ gaugeUX) (h0 : gaugeX b ≠ 0) :
    ContinuousAt gaugeBOff b := by
  have hfd : ContinuousAt
      (fun x : Submission.Milnor.MSpace8 => fderiv ℝ (Submission.Milnor.vMap (-2)) x)
      ((Submission.Milnor.vData (-2)).chartOfX 0 b) := by
    refine continuousAt_fderiv_vMap _ ?_
    show ((Submission.Milnor.vData (-2)).chartOfX 0 b).1 ≠ 0
    simpa only [gaugeX] using h0
  have h1 : ContinuousAt (fun b : Vk =>
      fderiv ℝ (Submission.Milnor.vMap (-2)) ((Submission.Milnor.vData (-2)).chartOfX 0 b)) b :=
    hfd.comp (continuousAt_chartOfX b hb)
  have hout : Continuous
      (fun L : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 =>
        (ContinuousLinearMap.snd ℝ E4 HH).comp
          (L.comp ((1 : E4 →L[ℝ] E4).prod (0 : E4 →L[ℝ] HH)))) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have h := hout.continuousAt.comp h1
  show ContinuousAt (fun b : Vk => (ContinuousLinearMap.snd ℝ E4 HH).comp
    ((fderiv ℝ (Submission.Milnor.vMap (-2))
        ((Submission.Milnor.vData (-2)).chartOfX 0 b)).comp
      ((1 : E4 →L[ℝ] E4).prod (0 : E4 →L[ℝ] HH)))) b
  simpa only [Function.comp_def] using h

/-- `gaugeXOff = C⁻¹ ∘ B` is continuous at the points where `gaugeX ≠ 0`. -/
lemma continuousAt_gaugeXOff (b : Vk) (hb : b ∈ gaugeUX) (h0 : gaugeX b ≠ 0) :
    ContinuousAt gaugeXOff b := by
  have h := (continuousAt_gaugeCinv b hb h0).clm_comp (continuousAt_gaugeBOff b hb h0)
  show ContinuousAt (fun b : Vk => (gaugeCinv b).comp (gaugeBOff b)) b
  simpa only [Function.comp_def] using h

/-! ## The cutoff argument -/

/-- If `ψ` vanishes on `(-∞, 1]` then `ψ ∘ ‖gaugeX ·‖` kills the blow-up of a function `F` that is
continuous wherever `gaugeX ≠ 0`, so that `b ↦ ψ ‖gaugeX b‖ • F b` is continuous on `gaugeUX`. -/
lemma continuousAt_scalar_smul (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (F : Vk → E4 →L[ℝ] HH) (b : Vk) (hb : b ∈ gaugeUX)
    (hF : gaugeX b ≠ 0 → ContinuousAt F b)
    (hzero : ∀ t : ℝ, t ≤ 1 → ψ t = 0) :
    ContinuousAt (fun b => ψ ‖gaugeX b‖ • F b) b := by
  have hnrm : ContinuousAt (fun b => ‖gaugeX b‖) b := continuousAt_norm_gaugeX b hb
  by_cases h0 : gaugeX b = 0
  · have hsets : ({t : ℝ | t < 1} : Set ℝ) ∈ 𝓝 (‖gaugeX b‖) := by
      rw [h0, norm_zero]
      exact (isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num : (0 : ℝ) < 1)
    have hlt : ∀ᶠ b' in 𝓝 b, ‖gaugeX b'‖ < 1 := hnrm.eventually hsets
    have hev : (fun b' => ψ ‖gaugeX b'‖ • F b') =ᶠ[𝓝 b] (fun _ => (0 : E4 →L[ℝ] HH)) := by
      filter_upwards [hlt] with b' hb'
      rw [hzero _ (le_of_lt hb')]
      exact zero_smul ℝ (F b')
    exact continuousAt_const.congr hev.symm
  · have hsc : ContinuousAt (fun b => ψ ‖gaugeX b‖) b := hψ.continuousAt.comp hnrm
    exact hsc.smul (hF h0)

/-! ## Assembly of the block matrices -/

/-- The product of two continuous linear maps, written through the two projections. -/
lemma prod_eq_inl_inr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E4) (Q : E →L[ℝ] HH) :
    P.prod Q = (ContinuousLinearMap.inl ℝ E4 HH).comp P
      + (ContinuousLinearMap.inr ℝ E4 HH).comp Q := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, Prod.mk_add_mk]
  simp

/-- `gaugeBlk` depends continuously on its three block arguments. -/
lemma continuousAt_gaugeBlk {X : Type*} [TopologicalSpace X] {x : X}
    {A : X → E4 →L[ℝ] E4} {B : X → E4 →L[ℝ] HH} {C : X → HH →L[ℝ] HH}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) (hC : ContinuousAt C x) :
    ContinuousAt (fun y => gaugeBlk (A y) (B y) (C y)) x := by
  have hP : ContinuousAt (fun y => (A y).comp (ContinuousLinearMap.fst ℝ E4 HH)) x :=
    hA.clm_comp continuousAt_const
  have hQ : ContinuousAt (fun y => (B y).comp (ContinuousLinearMap.fst ℝ E4 HH)
      + (C y).comp (ContinuousLinearMap.snd ℝ E4 HH)) x :=
    (hB.clm_comp continuousAt_const).add (hC.clm_comp continuousAt_const)
  have h1 : ContinuousAt (fun y => (ContinuousLinearMap.inl ℝ E4 HH).comp
      ((A y).comp (ContinuousLinearMap.fst ℝ E4 HH))) x := continuousAt_const.clm_comp hP
  have h2 : ContinuousAt (fun y => (ContinuousLinearMap.inr ℝ E4 HH).comp
      ((B y).comp (ContinuousLinearMap.fst ℝ E4 HH)
        + (C y).comp (ContinuousLinearMap.snd ℝ E4 HH))) x := continuousAt_const.clm_comp hQ
  refine (h1.add h2).congr ?_
  filter_upwards with y
  show (ContinuousLinearMap.inl ℝ E4 HH).comp
        ((A y).comp (ContinuousLinearMap.fst ℝ E4 HH))
      + (ContinuousLinearMap.inr ℝ E4 HH).comp
        ((B y).comp (ContinuousLinearMap.fst ℝ E4 HH)
          + (C y).comp (ContinuousLinearMap.snd ℝ E4 HH))
      = gaugeBlk (A y) (B y) (C y)
  rw [gaugeBlk, prod_eq_inl_inr]

/-- `gaugeH0` is continuous at every point of `gaugeUX`. -/
lemma continuousAt_gaugeH0 (b : Vk) (hb : b ∈ gaugeUX) : ContinuousAt gaugeH0 b := by
  have hA : ContinuousAt (fun b : Vk => (etaCut ‖gaugeX b‖) • gaugeJ) b :=
    (continuous_etaCut.continuousAt.comp (continuousAt_norm_gaugeX b hb)).smul
      (continuousAt_const : ContinuousAt (fun _ : Vk => gaugeJ) b)
  have hB : ContinuousAt (fun b : Vk => (aCut ‖gaugeX b‖) • gaugeXOff b) b :=
    continuousAt_scalar_smul aCut continuous_aCut gaugeXOff b hb
      (fun h0 => continuousAt_gaugeXOff b hb h0) (fun _ ht => aCut_of_le_one ht)
  have hblk := continuousAt_gaugeBlk hA hB (continuousAt_const :
    ContinuousAt (fun _ : Vk => (1 : HH →L[ℝ] HH)) b)
  show ContinuousAt (fun y : Vk =>
    gaugeBlk (etaCut ‖gaugeX y‖ • gaugeJ) (aCut ‖gaugeX y‖ • gaugeXOff y) 1) b
  exact hblk

/-- `gaugeH0inv` is continuous at every point of `gaugeUX`. -/
lemma continuousAt_gaugeH0inv (b : Vk) (hb : b ∈ gaugeUX) : ContinuousAt gaugeH0inv b := by
  have hA : ContinuousAt (fun b : Vk => ((etaCut ‖gaugeX b‖)⁻¹) • gaugeJ) b :=
    ((continuous_etaCut.continuousAt.comp (continuousAt_norm_gaugeX b hb)).inv₀
      (etaCut_ne_zero _)).smul (continuousAt_const : ContinuousAt (fun _ : Vk => gaugeJ) b)
  have hB : ContinuousAt (fun b : Vk =>
      (-(aCut ‖gaugeX b‖) * (etaCut ‖gaugeX b‖)⁻¹) • ((gaugeXOff b).comp gaugeJ)) b := by
    refine continuousAt_scalar_smul (fun t : ℝ => -(aCut t) * (etaCut t)⁻¹) ?_
      (fun b => (gaugeXOff b).comp gaugeJ) b hb ?_ ?_
    · exact continuous_aCut.neg.mul (continuous_etaCut.inv₀ etaCut_ne_zero)
    · intro h0
      have hcg : Continuous (fun L : E4 →L[ℝ] HH => L.comp gaugeJ) :=
        (continuous_id (X := E4 →L[ℝ] HH)).clm_comp
          (continuous_const : Continuous (fun _ : E4 →L[ℝ] HH => gaugeJ))
      exact hcg.continuousAt.comp (continuousAt_gaugeXOff b hb h0)
    · intro t ht
      rw [aCut_of_le_one ht]
      ring
  have hblk := continuousAt_gaugeBlk hA hB (continuousAt_const :
    ContinuousAt (fun _ : Vk => (1 : HH →L[ℝ] HH)) b)
  show ContinuousAt (fun y : Vk =>
    gaugeBlk ((etaCut ‖gaugeX y‖)⁻¹ • gaugeJ)
      ((-(aCut ‖gaugeX y‖) * (etaCut ‖gaugeX y‖)⁻¹) • ((gaugeXOff y).comp gaugeJ)) 1) b
  exact hblk

theorem gauge_continuous :
    ContinuousOn Work.Agree.gaugeH0 Work.Agree.gaugeUX ∧
    ContinuousOn Work.Agree.gaugeH0inv Work.Agree.gaugeUX :=
  ⟨continuousOn_of_forall_continuousAt continuousAt_gaugeH0,
    continuousOn_of_forall_continuousAt continuousAt_gaugeH0inv⟩

end

end Work.Agree
