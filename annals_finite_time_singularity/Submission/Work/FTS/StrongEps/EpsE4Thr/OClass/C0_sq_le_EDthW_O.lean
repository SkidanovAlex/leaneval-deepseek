/-
# `(C₀ f)² ≤ EDthW f` in the open-quadrant class `SmoothOpen`

`Work.FTS.EllipticEst.SmoothOpen f` is genuine `C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)` in the order `Work.Stability.smoothOrder = ∞` (not the analytic `⊤`); this
is the class of a localised (cut-off) datum, and it is *weaker* than the strip class
`Work.FTS.LocData.SmoothQuad` of the sibling `Work.FTS.CoercivityFix.Coer1T.C0_sq_le_EDthW_Q`,
so the quadrant result cannot simply be invoked.  The proof below is the port of that sibling's
proof to the open class: the only input of the Cauchy–Schwarz estimate that depends on the
smoothness class is the a.e. strong measurability of `u = D_θ f · w` with respect to
`(volume.restrict Iz).prod (volume.restrict Iθ)`, and for `SmoothOpen` data this comes from
continuity on the open quadrant alone (`Work.Spaces.aesm_of_continuousOn_Qd`), because the
product measure is concentrated on the quadrant.

The estimate itself is

  `(C₀ f)² = (L₁₂(Transport f)(0))² ≤ (∫ u²)·(∫ v²) ≤ EDthW f`,

with `C₀ f` the `L²`-pairing of `u` and the fixed kernel `v = 3 K(θ) z/(1+z)³`, whose `L²`-norm
is at most `1` (`∫_Iz 9z²/(1+z)⁶ = 3/10`, `∫_Iθ K² ≤ 9/4`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1T.C0_sq_le_EDthW_Q
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Measurability of `D_θ f · w` for `SmoothOpen` data -/

/-- `(z,θ) ↦ D_θ f z θ · w(z)` is continuous on the open quadrant for `SmoothOpen` data:
`D_θ` preserves `C^∞` on the open quadrant (`SmoothOpen.Dth`), and there the weight `w` is
continuous with no singularity. -/
theorem continuousOn_dth_mul_w_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hD : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.FTS.EllipticEst.Q0 := hso.Dth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hD.continuousOn
  exact hcont.mul Work.Coercivity.continuousOn_w_quad

/-- A.e. strong measurability of `D_θ f · w` with respect to the product of the restrictions of
Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`, for `SmoothOpen` data. -/
theorem aesm_dth_mul_w_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_dth_mul_w_O hso)

/-! ## The bound -/

/-- `L₁₂(Transport f)(0)` is a linear functional of `D_θ f · w` whose kernel
`3 K(θ) z/(1+z)³` has `L²`-norm at most `1`; hence `(C₀ f)² ≤ EDthW f`, in the open-quadrant
class `SmoothOpen`. -/
theorem C0_sq_le_EDthW_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ := fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ := fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hu2 : Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod
      (g := fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
      * Work.Spaces.w z ^ 2) hint
    exact h.congr (Eventually.of_forall fun p => by simp only [hu]; ring)
  have hv2 : Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MemLp u 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hu2
    rw [hu, hP]
    exact aesm_dth_mul_w_O hso
  have hvA : MemLp v 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hv2
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
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p ^ 2) hu2]
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hu]; ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
          * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _
      hran Work.Coercivity.integrableOn_Kθ_sq
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

end Work.FTS.StrongEps.EpsE4Thr.OClass
