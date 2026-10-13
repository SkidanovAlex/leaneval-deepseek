/-
# `OpenCoer/LGammaCoercive/LGamma_coercive_O` — the weighted `L²` coercivity of `𝓛_Γ`
in the *open* class

This is the open-class (`RegQo α 2` / `IntPkgO`) port of the interior-class proposition
`Work.FTS.CoercivityFix.Coer1T.LGamma_coercive_Q`, which is Elgindi's §6 estimate

  `(𝓛_Γ f, f)_{w²} ≥ 1/4 |f w|²_{L²}`  for `f` in the coercivity class with Hardy hypotheses.

The proof is a *verbatim* transcription: every input that changed class is supplied by
`OpenCoer/SlotWCommon.lean` (`intK_O`, `intG_O`, `intT1_w2_O`) or by
`CoercivityFix/Coer1SO/wip_Dz_self_le_SO.lean` (`wip_L_self_QO` replaces `Coer1.wip_L_self_Q`,
with the open-class `z`-integration-by-parts package `ZIBPO` in place of `ZIBP`); the
integrability bundle is the given `IntPkgO α f` instead of `Coer1.IntPkg_Q α hα hf`, and the
`(f w)²` integrability of `wip_G_bound` is `hfw2_open` instead of `hfw2_of_regQ`.  Everything
else (`wip_K_part_eq`, `wip_G_bound`, `L12_z_byparts_rhs_integrable`, `wip_one_self`,
`Ef_eq_EnOne`, `wip_sub_left`) is class-agnostic and is used unchanged.

The structure of the argument (the same as the frozen one):

* `⟨𝓛_Γ f, f⟩_{w²} = ⟨𝓛 f, f⟩_{w²} - ⟨(2zΓ/(c(1+z)²))L₁₂(f), f⟩_{w²}`;
* `⟨𝓛 f, f⟩_{w²} = ½|f w|²` (the paper's `z`-integration by parts, `wip_L_self_QO`);
* the `L₁₂`-term is split as `Γ/c = K + (Γ/c - K)`: the `K`-half integrates by parts in `z` into
  `-2∫(1+z)/z³ L₁₂(f)² ≤ 0`, and the `(Γ/c-K)`-half is controlled by Cauchy–Schwarz with the
  hypothesis `GammaL2Bnd α` (`wip_G_bound`);
* the numerical conclusion `½x² + 2y² - (7/5)xy ≥ ¼x²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive

set_option maxHeartbeats 1600000

theorem LGamma_coercive_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hΓ : Work.Coercivity.GammaL2Bnd α) :
    (1 / 4) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGamma α f) f := by
  have hs : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  -- ## integrability of the two halves of `𝓛_Γ`
  have hintL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hIP.intL_f_one
  have hF1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod hintL
  have hF4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intT1_w2_O α hα hα1 hIP hs hHH)
  -- ## the two halves of the `L₁₂`-term
  have hintK : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * Work.Spaces.K θ * f z θ * (Work.Spaces.w z / z * Work.Coercivity.L12f f z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intK_O α hα hIP hs hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hintG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ
        * Work.Spaces.w z * (Work.Coercivity.L12f f z / z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intG_O α hα hα1 hIP hs hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hF5 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * Work.Spaces.K p.2 * f p.1 p.2 * (Work.Spaces.w p.1 / p.1
        * Work.Coercivity.L12f f p.1)) P :=
    Work.Coercivity.integrableOn_prod hintK
  have hF6 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2) * f p.1 p.2
        * Work.Spaces.w p.1 * (Work.Coercivity.L12f f p.1 / p.1)) P :=
    Work.Coercivity.integrableOn_prod hintG
  -- ## integrability of `𝓛_Γ f · f w²`
  have hintLG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hintL.sub
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intT1_w2_O α hα hα1 hIP hs hHH)
    rw [MeasureTheory.IntegrableOn] at h ⊢
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
    ring
  -- ## the `wip`s as product-measure integrals
  have hwipLG : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f
      = ∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f hintLG
  have hwipL : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.L f) f
      = ∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.L f) f hintL
  -- ## `𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂(f)`
  have hsplit : (∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2
        * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
            / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
            * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hF1 hF4]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Coercivity.LGamma]
    ring
  -- ## the paper's identity `(LW)`: `(𝓛 f, f)_{w²} = ½|f w|²`
  have hLhalf : (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (1 / 2) * Work.Coercivity.Ef f := by
    rw [← hwipL]
    have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        f z θ ^ 2 * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine (hIP.sqDzOne 0 (by norm_num)).congr_fun ?_
        (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
      ring
    have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine hintL.congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair]
      ring
    have h := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO f hIP.zibp_f
      (fun _ => (1 : ℝ)) h1 h2
    have hw : (fun z θ : ℝ => Work.Spaces.w z ^ 2 * (1 : ℝ))
        = fun z _ => Work.Spaces.w z ^ 2 := by funext z θ; ring
    rw [hw] at h
    rw [h, Work.FTS.CoercivityFix.Coer1.wip_one_self,
      Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]
  -- ## splitting `Γ/c = K + (Γ/c - K)`
  have hTsum : (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
          / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
          * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
        + (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
    rw [← MeasureTheory.integral_add hF5 hF6]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show 2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
      = 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1)
        + 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1)
    by_cases hz : p.1 = 0
    · rw [hz]; simp [Work.Spaces.w]
    · simp only [Work.Spaces.w]
      field_simp
      ring
  -- ## the two radial integrals of the paper
  set Y : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2 with hY
  set Z : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (Work.Coercivity.L12f f z) ^ 2 / z ^ 2 with hZ
  have hEL : Work.Coercivity.EL12z f = Z := by
    rw [hZ]
    simp only [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz, Work.Spaces.Iz]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact div_pow (Work.Coercivity.L12f f z) z 2
  have hWK : (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
        * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P) = -2 * Y := by
    rw [hP, hY]
    exact Work.Coercivity.wip_K_part_eq f hHH hintK
  have hBsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := Work.Coercivity.integrableOn_GammaK_sq α hα hα1
  have hWG : (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
        * f p.1 p.2 * Work.Spaces.w p.1
        * (Work.Coercivity.L12f f p.1 / p.1) ∂P)
      ≤ (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
    have h := (abs_le.mp (Work.Coercivity.wip_G_bound α hα hα1 f hHH
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.hfw2_open hIP) hΓ hBsq hintG)).2
    rw [hEL] at h
    exact h
  have hZY : Z ≤ Y := by
    rw [hZ, hY]
    refine MeasureTheory.integral_mono_ae ?_ (Work.Coercivity.L12_z_byparts_rhs_integrable f hHH) ?_
    · refine (hHH.intA 1 (by norm_num)).congr_fun ?_ measurableSet_Ioi
      intro z _
      norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := hz
      rw [← sub_nonneg]
      have hsub : (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2
          - (Work.Coercivity.L12f f z) ^ 2 / z ^ 2
          = (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 := by
        field_simp
        ring
      rw [hsub]
      positivity
  -- ## the numerical conclusion `½x² + 2y² - (7/5)xy ≥ ¼x²`
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun z => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnum : (1 / 2) * Work.Coercivity.Ef f + 2 * Z
      - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z
      ≥ (1 / 4) * Work.Coercivity.Ef f := by
    nlinarith [Real.sq_sqrt hEfnn, Real.sq_sqrt hZnn,
      sq_nonneg (Real.sqrt (Work.Coercivity.Ef f) - 14 / 5 * Real.sqrt Z),
      sq_nonneg (Real.sqrt Z)]
  calc Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.LGamma α f) f
      = (1 / 2) * Work.Coercivity.Ef f
          - (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
              * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hwipLG, hsplit, hLhalf, hTsum]; ring
    _ = (1 / 2) * Work.Coercivity.Ef f + 2 * Y
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hWK]; ring
    _ ≥ (1 / 2) * Work.Coercivity.Ef f + 2 * Z
          - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
        linarith [hWG, hZY]
    _ ≥ (1 / 4) * Work.Coercivity.Ef f := hnum

end Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive
