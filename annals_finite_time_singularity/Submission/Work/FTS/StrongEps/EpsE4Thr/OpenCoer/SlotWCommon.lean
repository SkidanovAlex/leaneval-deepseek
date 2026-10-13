/-
# `OpenCoer/SlotWCommon.lean` — the shared helpers for the *open-class* `W`-slot of `𝓛_Γ^T`

The frozen ``W``-slot coercivity (`Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT`) is stated on the
interior class `Work.FTS.Nonlin.RegQ α 2`, whose smoothness field is `LocData.SmoothQuad` (analytic
on the half-strip `z > -1`).  The route's data (the projected mollified slice) only carries
`SmoothOpen` (`C^∞` on the *open* quadrant), so the whole slot has to be re-run on the open class
`Work.FTS.StrongEps.EpsE4Thr.RegQo α 2` with the integrability bundle
`Work.FTS.StrongEps.EpsE4Thr.IntPkgO`.

This file collects **all** the auxiliary integrability / measurability facts that the port needs, so
that the two substantive theorems of the port — the `L²`-coercivity of `𝓛_Γ` and the sharp
projector bound — are pure transcriptions of their frozen counterparts:

* `aesm_f_open`            — a.e. strong measurability of an `SmoothOpen` datum;
* `hfw_open`, `hfw2_open`  — joint integrability of `(f w)²` / `f²w²` (from `IntPkgO`);
* `intK_O`, `intG_O`       — integrability of the two halves of the `L₁₂`-pairing;
* `intT1_w2_O`             — integrability of the `L₁₂`-term against `f w²`;
* `intLG_O`                — integrability of `𝓛_Γ f · f w²`;
* `intDth2_O`              — integrability of `(D_θ f)² w²`;
* `aesm_dth_mul_w_O`       — a.e. strong measurability of `D_θ f · w`;
* `C0_sq_le_EDthW_O`       — the bound `(C₀ f)² ≤ EDthW f`.

Every proof is the verbatim port of its `_Q` counterpart in
`Submission/Work/FTS/CoercivityFix/Coer1T/slotW_LGammaT.lean`, the only change being that the
`RegQ`/`IntPkg` inputs are replaced by `RegQo`/`IntPkgO` ones.

**Note to consumers of this file.**  Anything else you need should be declared under your *own*
nested namespace (`Work.FTS.StrongEps.EpsE4Thr.OpenCoer.<YourTag>`), so that two downstream modules
can be imported together without a name clash.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OpenCoer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Measurability and integrability of the datum -/

/-- An `SmoothOpen` datum is a.e. strongly measurable for the product of the two restricted
measures (the two differ from the open quadrant by a null set). -/
theorem aesm_f_open {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ hs.continuousOn

/-- Continuity of an `SmoothOpen` datum on the open quadrant (the class in which the coercivity
identity is used). -/
theorem continuousOn_f_open {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  hs.continuousOn

/-- Continuity of `D_θ f` on the open quadrant (open-class replacement for
`Coer1.continuousOn_mixed_Q hf.1 0 1`). -/
theorem continuousOn_Dth_open {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((hs.Dth).forall 0).continuousOn

/-- `(f w)²` is jointly integrable, from the `D_z⁰`-certificate of `IntPkgO`. -/
theorem hfw_open {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hIP.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  ring

/-- The `f²w²` form of the previous certificate, as used by `wip_G_bound`. -/
theorem hfw2_open {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hfw_open hIP).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair]
  ring

/-! ## The two halves of the `L₁₂`-pairing, and the `L₁₂`-term -/

/-- The `K`-part of the `L₁₂`-pairing is jointly integrable (open class). -/
theorem intK_O (α : ℝ) (hα : 0 < α) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * (Work.Spaces.K θ * f z θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    Work.Spaces.K Work.Coercivity.integrableOn_Kθ_sq
    (Work.Coercivity.continuousOn_Kθ.aestronglyMeasurable measurableSet_Icc)

/-- The `(Γ/c - K)`-part of the `L₁₂`-pairing is jointly integrable (open class). -/
theorem intG_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * ((Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ)
    (Work.Coercivity.integrableOn_GammaK_sq α hα hα1)
    (((Work.Coercivity.continuousOn_Gam α hα).div_const (Work.Spaces.c α)).sub
      Work.Coercivity.continuousOn_Kθ |>.aestronglyMeasurable measurableSet_Icc)

/-- The `L₁₂`-term of `𝓛_Γ` against `f w²` is jointly integrable (open class). -/
theorem intT1_w2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
          * Work.Coercivity.L12f f z * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hGam2 : MeasureTheory.Integrable
      (fun θ : ℝ => (2 * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.of_bound ?_ 400 ?_
    · exact ((((Work.Coercivity.continuousOn_Gam α hα).const_mul
        (2 : ℝ)).div_const (Work.Spaces.c α)).pow 2).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have h2 : |2 * Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 20 := by
        rw [show 2 * Work.Spaces.Gam α θ / Work.Spaces.c α
            = 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      nlinarith [abs_nonneg (2 * Work.Spaces.Gam α θ / Work.Spaces.c α),
        sq_abs (2 * Work.Spaces.Gam α θ / Work.Spaces.c α)]
  have hcm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      (volume.restrict Work.Spaces.Iθ) :=
    (((Work.Coercivity.continuousOn_Gam α hα).const_mul (2 : ℝ)).div_const
      (Work.Spaces.c α)).aestronglyMeasurable measurableSet_Icc
  refine (Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    (fun θ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) hGam2 hcm).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.w]
  rcases eq_or_ne z 0 with rfl | hz
  · norm_num
  · field_simp

/-- The `𝓛_Γ f · f w²` pairing is jointly integrable (open class): `𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂f`
and both halves are known to be integrable. -/
theorem intLG_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := hIP.intL_f_one.sub (intT1_w2_O α hα hα1 hIP hs hHH)
  rw [MeasureTheory.IntegrableOn] at h ⊢
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
  ring

/-! ## The `D_θ`-pairing and the projector kernel -/

/-- `(D_θ f)² w²` is jointly integrable (open class), from the `(i,j) = (1,0)` mixed certificate of
`IntPkgO` (`mixed 0 1 = D_θ`). -/
theorem intDth2_O {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_zero, Work.Spaces.DthIter_succ]
  ring

/-- The a.e. strong measurability of `D_θ f · w` (open class). -/
theorem aesm_dth_mul_w_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((hs.Dth).forall 0).continuousOn.mul Work.Coercivity.continuousOn_w_quad)

/-- **The bound `(C₀ f)² ≤ EDthW f` in the open class**: `L₁₂(Transport f)(0)` is a linear
functional of `D_θ f · w` whose kernel `3K(θ)z/(1+z)³` has `L²`-norm at most `1`. -/
theorem C0_sq_le_EDthW_O {α : ℝ} (hα : 0 < α) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ :=
    fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hint := intDth2_O hIP
  have hu2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod (g := fun z θ => Work.Spaces.Dth f z θ
      * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2) hint
    exact h.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [hu]
      ring)
  have hv2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MeasureTheory.MemLp u 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq (aesm_dth_mul_w_O hs)).2 hu2
  have hvA : MeasureTheory.MemLp v 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.K]
    fun_prop
  have hC0id : Work.Coercivity.C0 f = ∫ p, u p * v p ∂P := by
    have hdef : Work.Coercivity.C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s := by
      simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
        Work.Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDthW_eq_prod hint]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [hu]
    ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
            * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _ hran Work.Coercivity.integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 / 4 :=
      Work.Coercivity.integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (Work.Coercivity.C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) :=
        Work.Coercivity.cs_integral_mul huA hvA
    _ ≤ Work.Coercivity.EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm
          (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = Work.Coercivity.EDthW f := mul_one _

end Work.FTS.StrongEps.EpsE4Thr.OpenCoer
