import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OpenCoer.ProjPair

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- **The sharp projector bound in the open class** (with the integrability certificate):
`|⟨𝕡(Transport f), f⟩_{w²}| ≤ √58·√EDthW·√Ef ≤ Ef/20 + 1000·EDthW`, for
`f ∈ RegQo α 2` and the open-class integrability bundle `IntPkgO α f`.

This is the verbatim port of `Work.FTS.CoercivityFix.Coer1T.proj_pair_conj` (interior class
`RegQ α 2`) along the route of `OpenCoer/SlotWCommon.lean`: every use of `RegQ` is replaced by
`RegQo`, and the three `IntPkg`-derived certificates by their `IntPkgO` counterparts
(`hfw_open`, `hfw2_open`, `intDth2_O`, `C0_sq_le_EDthW_O`). -/
theorem proj_pair_conj_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hΓ : Work.Coercivity.GammaL2Bnd α) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ * f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f|
        ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set U : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.Proj α (Work.Coercivity.Transport f) p.1 p.2 * Work.Spaces.w p.1 with hU
  set V : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1 with hV
  set Wt : ℝ × ℝ → ℝ := fun p => 18 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2
      + 8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 * (Work.Coercivity.C0 f) ^ 2
        / (1 + p.1) ^ 2 with hWt
  have hDth2 := Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intDth2_O hIP
  have hDth2P : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2
      * Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod hDth2
  have hfwP : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) P :=
    Work.Coercivity.integrableOn_prod (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.hfw_open hIP)
  have hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f :=
    Work.FTS.StrongEps.EpsE4Thr.OpenCoer.C0_sq_le_EDthW_O hα hIP hf.1
  have hEdnn : 0 ≤ Work.Coercivity.EDthW f := by
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  -- ## the pointwise bound `U² ≤ Wt`
  have hpt : ∀ᵐ p ∂P, (U p) ^ 2 ≤ Wt p := by
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hid : U p = (1 / (1 + p.1)) *
        (3 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
          - 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.Coercivity.C0 f) := by
      simp only [hU, Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Spaces.w,
        Work.Coercivity.C0]
      have hz0 : p.1 ≠ 0 := ne_of_gt hp
      have hz1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    set g : ℝ := Work.Spaces.Gam α p.2 / Work.Spaces.c α with hg
    set Gw : ℝ := Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hGw
    have hquad : (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2
        ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 := by
      have h1 : (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2
          ≤ 2 * ((3 * Gw) ^ 2 + (2 * g * Work.Coercivity.C0 f) ^ 2) := by
        nlinarith [sq_nonneg (3 * Gw + 2 * g * Work.Coercivity.C0 f)]
      have h2 : 2 * ((3 * Gw) ^ 2 + (2 * g * Work.Coercivity.C0 f) ^ 2)
          = 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 := by ring
      linarith
    calc (U p) ^ 2
        = (1 / (1 + p.1)) ^ 2 * (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2 := by
          rw [hid, hGw, hg]; ring
      _ ≤ (1 / (1 + p.1)) ^ 2
            * (18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (by positivity)
      _ ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2 := by
          have hp1 : (0 : ℝ) < (1 + p.1) ^ 2 := pow_pos (by linarith) 2
          have heq : (1 / (1 + p.1)) ^ 2
                * (18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2)
              = 18 * Gw ^ 2 / (1 + p.1) ^ 2
                + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2 := by
            field_simp
          rw [heq]
          have h2z : 18 * Gw ^ 2 / (1 + p.1) ^ 2 ≤ 18 * Gw ^ 2 := by
            rw [div_le_iff₀ hp1]
            nlinarith [sq_nonneg Gw, sq_nonneg p.1, hp]
          linarith [h2z]
      _ = Wt p := by rw [hWt, hGw, hg]
  -- ## integrability of the majorant `Wt`
  have hW1 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => 18 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2) P := by
    have h := hDth2P.const_mul 18
    exact h.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩; ring)
  have hGamCont : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ :=
    Work.Coercivity.continuousOn_Gam α hα
  have hG2int : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) Work.Spaces.Iθ :=
      ((hGamCont.div_const (Work.Spaces.c α)).pow 2)
    exact hcont.integrableOn_Icc
  have hCorrInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := Work.Coercivity.integrable_Iz_one_div_sq.mul_prod hG2int
    rw [hP]
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hW2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
        * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := hCorrInt.const_mul (8 * (Work.Coercivity.C0 f) ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hWint : MeasureTheory.Integrable Wt P := by
    rw [hWt]; exact hW1.add hW2
  have hUAesm : MeasureTheory.AEStronglyMeasurable U P := by
    rw [hU]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hProj : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Coercivity.Proj α (Work.Coercivity.Transport f) p.1 p.2)
        Work.FTS.CoercivityFix.Coer1.Qd := by
      have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
          Work.FTS.CoercivityFix.Coer1.Qd :=
        (hf.1.Dth.forall 0).continuousOn
      have hTrans : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Coercivity.Transport f p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd := by
        change ContinuousOn (fun p : ℝ × ℝ =>
          3 * Work.Spaces.Dth f p.1 p.2 / (1 + p.1)) Work.FTS.CoercivityFix.Coer1.Qd
        exact (continuousOn_const.mul hDth).div
          ((continuous_const.add continuous_fst).continuousOn)
          (fun p hp => ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp.1]))
      have hGam : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.Gam α p.2 / Work.Spaces.c α) Work.FTS.CoercivityFix.Coer1.Qd :=
        ((Work.Coercivity.continuousOn_Gam α hα).div_const (Work.Spaces.c α)).comp
          ((continuous_snd.continuousOn).mono (Set.subset_univ _))
          (fun p hp => ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)
      have hratio : ContinuousOn (fun p : ℝ × ℝ =>
          2 * p.1 ^ 2 / (1 + p.1) ^ 3) Work.FTS.CoercivityFix.Coer1.Qd := by
        refine ContinuousOn.div ((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)))
          ((continuous_const.add continuous_fst).continuousOn.pow 3)
          (fun p hp => pow_ne_zero 3 (by linarith [show (0 : ℝ) < p.1 from hp.1]))
      have hCorr : ContinuousOn (fun p : ℝ × ℝ =>
          (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * Work.Coercivity.C0 f) Work.FTS.CoercivityFix.Coer1.Qd :=
        (hGam.mul hratio).mul continuousOn_const
      have hmain : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Coercivity.Transport f p.1 p.2
            - (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
              * Work.Coercivity.C0 f) Work.FTS.CoercivityFix.Coer1.Qd :=
        hTrans.sub hCorr
      have hfun : (fun p : ℝ × ℝ => Work.Coercivity.Proj α (Work.Coercivity.Transport f)
          p.1 p.2) = fun p : ℝ × ℝ => Work.Coercivity.Transport f p.1 p.2
            - (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
              * Work.Coercivity.C0 f := by
        funext p
        simp only [Work.Coercivity.Proj, Work.Coercivity.C0]
      rw [hfun]
      exact hmain
    exact hProj.mul Work.Coercivity.continuousOn_w_quad
  have hUaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (U p) ^ 2) P := by
    refine (hUAesm.mul hUAesm).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, pow_two]
  have hUint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (U p) ^ 2) P :=
    hWint.mono' hUaesm (hpt.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp)
  have hUA : MeasureTheory.MemLp U 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hUAesm).2 hUint
  -- ## the two normalisations
  have hunorm : ∫ p, (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2 ∂P
      = Work.Coercivity.EDthW f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDthW_eq_prod hDth2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩; ring)
  have hG5 : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 5 :=
    Work.Coercivity.GamDivCSqInt_le_five α hα hα1 hΓ
  have hCorrLe : ∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P
      ≤ 5 := Work.Coercivity.projCorr_sepIntegral_le_five α hα hα1 hG5
  have hWexp : ∫ p, Wt p ∂P
      = 18 * (∫ p, (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2 ∂P)
        + (8 * (Work.Coercivity.C0 f) ^ 2)
          * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P) := by
    rw [hWt, MeasureTheory.integral_add hW1 hW2, MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun p : ℝ × ℝ =>
        8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2)
        = fun p => (8 * (Work.Coercivity.C0 f) ^ 2)
            * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2) from by
      funext p; ring]
    rw [MeasureTheory.integral_const_mul]
  have hWle : ∫ p, Wt p ∂P ≤ 58 * Work.Coercivity.EDthW f := by
    rw [hWexp, hunorm]
    have hkey : (8 * (Work.Coercivity.C0 f) ^ 2)
        * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P)
        ≤ 40 * Work.Coercivity.EDthW f := by
      have h3 : (8 * (Work.Coercivity.C0 f) ^ 2)
          * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
              / (1 + p.1) ^ 2 ∂P) ≤ (8 * (Work.Coercivity.C0 f) ^ 2) * 5 :=
        mul_le_mul_of_nonneg_left hCorrLe (by positivity)
      have h4 : (8 * (Work.Coercivity.C0 f) ^ 2) * 5
          ≤ 40 * Work.Coercivity.EDthW f := by nlinarith [hC0]
      linarith
    linarith [hkey, hEdnn]
  have hU2le : ∫ p, (U p) ^ 2 ∂P ≤ 58 * Work.Coercivity.EDthW f :=
    le_trans (MeasureTheory.integral_mono_ae hUint hWint hpt) hWle
  -- ## the two `L²`-functions and Cauchy–Schwarz
  have hVnorm : ∫ p, (V p) ^ 2 ∂P = Work.Coercivity.Ef f := by
    have h := Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2) f f
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.hfw2_open hIP)
    rw [hP]
    have hcongr : (∫ p, V p ^ 2 ∂(volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ))
        = ∫ p, f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
            ∂(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp only [hV]; ring)
    rw [hcongr, ← h, Work.Coercivity.Ef_eq_wip]
  have hVA : MeasureTheory.MemLp V 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 ?_
    · rw [hV]
      exact (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.aesm_f_open hf.1).mul
        (Work.Spaces.aesm_of_continuousOn_Qd _
          Work.Coercivity.continuousOn_w_quad)
    · exact hfwP.congr (Filter.Eventually.of_forall fun p => by
        simp only [hV])
  have hcs := Work.Coercivity.cs_integral_mul hUA hVA
  have hV2 : (∫ p, V p ^ 2 ∂P) = Work.Coercivity.Ef f := hVnorm
  have hU2 : (∫ p, (U p) ^ 2 ∂P) ≤ 58 * Work.Coercivity.EDthW f := hU2le
  have hUVint : MeasureTheory.Integrable (fun p : ℝ × ℝ => U p * V p) P :=
    hUA.integrable_mul hVA
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hbound : |∫ p, U p * V p ∂P|
      ≤ Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f) := by
    have h1 : (∫ p, U p * V p ∂P) ^ 2
        ≤ (58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f := by
      rw [hV2] at hcs
      exact le_trans hcs (mul_le_mul_of_nonneg_right hU2 hEfnn)
    have h2 : Real.sqrt ((58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f)
        = Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 58 * Work.Coercivity.EDthW f),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 58)]
    calc |∫ p, U p * V p ∂P|
        = Real.sqrt ((∫ p, U p * V p ∂P) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f)
            * Real.sqrt (Work.Coercivity.Ef f) := h2
  have hnum : Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f)
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f := by
    have h := Work.Coercivity.sqrt58_amgm (Real.sqrt (Work.Coercivity.Ef f))
      (Real.sqrt (Work.Coercivity.EDthW f)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hEfnn, Real.sq_sqrt hEdnn] at h
    rw [show Work.Coercivity.Ef f / 20 = (1 / 20) * Work.Coercivity.Ef f by ring] at h
    have hcomm : Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f)
        * Real.sqrt (Work.Coercivity.Ef f)
        = Real.sqrt 58 * Real.sqrt (Work.Coercivity.Ef f)
          * Real.sqrt (Work.Coercivity.EDthW f) := by ring
    rw [hcomm]
    exact h
  -- ## transport the `wip` to the product measure
  have hUVon : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ * f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1T.prod_restrict_eq]
    refine hUVint.congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [hU, hV, Function.uncurry_apply_pair]
    ring
  have hwip : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f
      = ∫ p, U p * V p ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f hUVon, hP]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hU, hV, Function.uncurry_apply_pair]
    ring
  refine ⟨hUVon, ?_⟩
  rw [hwip]
  exact le_trans hbound hnum

end Work.FTS.StrongEps.EpsE4Thr.OpenCoer.ProjPair
