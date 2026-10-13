import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.dth_LGammaT_expansion
import Submission.Work.Coercivity.zAux
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The projector-correction pairing `⟨T4fun α f, f⟩_{w² sin^{-η}}` in the interior class

`T4fun α f = (Γ(θ)/c)·(2z²/(1+z)³)·C₀(f)`, where `C₀(f) = L₁₂(Transport f)(0)` is a *constant*.
Hence the pairing `wip (w² sin^{-η}) (T4fun α f) f` is `C₀(f)` times the pairing of the fixed
function `(Γ/c)(2z²/(1+z)³)` against `f`, and Cauchy–Schwarz in `L²(dz dθ)` bounds the latter by
`√(∫∫(Γ/c)²(2z²/(1+z)³)²w² sin^{-η})·√(EfEta f)`.  The first factor is
`√(4·∫_θ (Γ/c)² sin^{-η}) ≤ √(4·12100) = 220`, using `(2z²/(1+z)³)²w(z)² = 4/(1+z)²`
(so `∫_z · = 4`) and `Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100`.

The file `Submission/Work/Coercivity/L2CoercivityTransportEta.lean` proves this for the
*analytic* class `IBP`/`CoerciveData` (`Work.Coercivity.gPsi_eta_abs_le`).  The present file
repeats the proof for the **interior** class of the route: the only two ingredients really used
are the joint integrability `hF` of `f² w² sin^{-η}` and the a.e. strong measurability of `f`,
which is supplied here by `SmoothQuad`.
-/

/-- A.e. strong measurability on the quadrant of a function of class `SmoothQuad`: `SmoothQuad`
gives continuity on the *open* quadrant `(-1,∞) × (0,π/2)`, and the closed quadrant differs
from it by a null set. -/
theorem aesm_smoothQuad {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := hsq.continuousOn
  exact hcont.mono (fun p hp => by
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

/-- The joint integrability of `(Γ/c)(2z²/(1+z)³)·f·w²·sin(2θ)^{-η}` from the joint
integrability of `f² w² sin(2θ)^{-η}`: the pointwise bound `2|ab| ≤ a² + b²` with
`a = (Γ/c)(2z²/(1+z)³)w sin(2θ)^{-η/2}` reduces it to the separated product
`a(z,θ)² = [(Γ/c)² sin^{-η}]·[(2z²/(1+z)³)² w²]` (integrable: `∫_θ (Γ/c)² sin^{-η} < ∞` and
`∫_z (2z²/(1+z)³)² w² = ∫_z 4/(1+z)² = 4`) plus the given `f² w² sin^{-η}`. -/
theorem etaW_gPsi_integrable_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)))
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α)
        * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hmem : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hEta : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-Work.Spaces.eta) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hθ2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul hEta 100) ?_ ?_
    · unfold Work.Spaces.Gam
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := by
        rw [Work.Spaces.Gam]
        exact Real.rpow_le_one (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _))
          (Work.Coercivity.sin_mul_cos_sq_le_one hθ) (le_of_lt (by positivity : (0:ℝ) < α / 3))
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := by
        rw [Work.Spaces.Gam]
        exact Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)) _
      have hsq : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
        rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Work.Spaces.c α) ^ 2)]
        have h1 : Work.Spaces.Gam α θ ^ 2 ≤ 1 := by
          have := mul_self_le_mul_self hG0 hG1
          nlinarith [this]
        have h2 : (1:ℝ) ≤ 100 * (Work.Spaces.c α) ^ 2 := by
          have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/10) hc
          nlinarith [this]
        linarith
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hz2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2) Work.Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul Work.Coercivity.integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Work.Spaces.w
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hz0 : (0:ℝ) ≤ z := Set.mem_Ici.mp hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]
        norm_num
      · have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
            = 4 * (1 / (1 + z) ^ 2) := by
          rw [Work.Spaces.w]
          field_simp
          ring
        rw [hkey]
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Work.Spaces.w p.1 ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hz2.mul_prod hθ2
    rw [Work.Coercivity.prod_restrict_eq] at h
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (1 / 2) * (((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))
        * ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 * Work.Spaces.w p.1 ^ 2)
        + f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := Integrable.const_mul (hprod.add hF) (1 / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have hfac : (Function.uncurry (fun z θ =>
        (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        = (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
            * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)))
          * (fun p : ℝ × ℝ => f p.1 p.2) := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.mul_apply]
      ring
    rw [hfac]
    have hw : Measurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * (Work.Spaces.w p.1 ^ 2
          * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      unfold Work.Spaces.Gam Work.Spaces.w
      fun_prop
    exact hw.aestronglyMeasurable.mul haesm
  · filter_upwards [hmem] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    simp only [Function.uncurry_apply_pair]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hρ : 0 ≤ Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hkey := Work.Coercivity.gPsi_pointwise
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) (f z θ)
    have h2 := mul_le_mul_of_nonneg_right hkey hρ
    rw [Real.norm_eq_abs,
      show (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
            * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          = ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ)
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring,
      abs_mul, abs_of_nonneg hρ]
    refine h2.trans (le_of_eq ?_)
    ring

/-- **The Cauchy–Schwarz bound of the projector pairing in the interior class.**  For `Λ = C₀ f`
this is the bound needed for the `η`-slot of `𝓛_Γ^T`; the general `Λ` makes the statement
usable for a constant factor. -/
theorem wip_gPsi_eta_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (Λ : ℝ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hFη : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α)
          * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      ≤ 220 * |Λ| * Real.sqrt (Work.Coercivity.EfEta f) := by
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      * Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have haesm' : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.volume_restrict_prod]; exact haesm
  have hsinesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  -- ### Step 1: the weighted pairing as a product-measure integral of `Λ * (A * B)`
  have hgint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    etaW_gPsi_integrable_Q α hα hα1 f haesm' hFη
  have hIntOn : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ * f z θ
        * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    IntegrableOn.congr_fun (Integrable.const_mul hgint Λ) (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hIntOn' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    IntegrableOn.congr_fun hIntOn (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  have hwip : Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f
      = ∫ p, Λ * (A p * B p) ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f
      hIntOn', ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA, hB]
    have hss : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [← Work.Coercivity.rpow_half_sq _ hs0]; ring
    rw [← hss]
    ring
  -- ### Step 2: a.e. strong measurability of `A` and `B`
  have hAesm : AEStronglyMeasurable A P := by
    rw [hA]
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * Work.Spaces.w p.1) P := by
      apply Measurable.aestronglyMeasurable
      unfold Work.Spaces.Gam Work.Spaces.w
      fun_prop
    exact h1.mul hsinesm
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    have hfmw : AEStronglyMeasurable
        (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.w p.1) P := by
      have hwmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P := by
        apply Measurable.aestronglyMeasurable
        unfold Work.Spaces.w
        fun_prop
      exact haesm.mul hwmeas
    exact hfmw.mul hsinesm
  -- ### Step 3: square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
      Work.Spaces.Iz := by
    refine Integrable.mono' (Integrable.const_mul Work.Coercivity.integrable_Iz_one_div_sq 4) ?_ ?_
    · unfold Work.Spaces.w
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_ne z 0 with h | h
      · rw [h]; norm_num
      · have h1z : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
        have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
            = 4 * (1 / (1 + z) ^ 2) := by
          rw [Work.Spaces.w]; field_simp; ring
        rw [hkey]
  have hb : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul (Work.Spaces.sin_two_rpow (-Work.Spaces.eta)
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1 100) ?_ ?_
    · unfold Work.Spaces.Gam
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have hsq : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
        nlinarith [hG, abs_nonneg (Work.Spaces.Gam α θ / Work.Spaces.c α),
          sq_abs (Work.Spaces.Gam α θ / Work.Spaces.c α)]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hA2 : Integrable (fun p => A p ^ 2) P := by
    rw [hP]
    refine ((ha.mul_prod hb).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA]
    rw [mul_pow, mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    refine ((Work.Coercivity.integrableOn_prod hFη).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  -- ### Step 4: the Cauchy–Schwarz bound
  have hCS := Work.Coercivity.sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P|
      ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### Step 5: the values of the two square-integrals
  have hzsq : ∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2 = 4 := by
    have hI : (∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2 := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [hI]
    have hcongr : (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun z => 4 * (1 / (1 + z) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : z ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hz)
      have h1z : (1 : ℝ) + z ≠ 0 := by have := Set.mem_Ioi.mp hz; linarith
      have hkey : (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2
          = 4 * (1 / (1 + z) ^ 2) := by
        rw [Work.Spaces.w]; field_simp; ring
      rw [hkey]
    rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_const_mul]
    have h1 : (∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2) = 1 := by
      rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      exact Work.Coercivity.integral_Iz_one_div_sq
    rw [h1]
    norm_num
  have hBval : ∫ p, B p ^ 2 ∂P = Work.Coercivity.EfEta f := by
    have hF : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      IntegrableOn.congr_fun hFη (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [Work.Coercivity.EfEta_eq_wip, Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f hF, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => ((2 * p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
            * Work.Spaces.w p.1 ^ 2)
          * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [Work.Coercivity.integral_prod_sep
      (a := fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * Work.Spaces.w z ^ 2)
      (b := fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ha hb]
  -- ### Step 6: numerical conclusion
  have hX := Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hXnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin0 θ hθ) _)
  have hsq_le : Real.sqrt (4 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) ≤ 220 := by
    have h110 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    nlinarith [h110, Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))]
  calc |Work.Coercivity.wip
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * Λ) f|
      = |∫ p, Λ * (A p * B p) ∂P| := by rw [hwip]
    _ = |Λ| * |∫ p, A p * B p ∂P| := by
        rw [MeasureTheory.integral_const_mul, abs_mul]
    _ ≤ |Λ| * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = |Λ| * (Real.sqrt ((∫ z in Work.Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2
            * Work.Spaces.w z ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) * Real.sqrt (Work.Coercivity.EfEta f)) := by
        rw [hAval, hBval]
    _ = |Λ| * (Real.sqrt (4 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
          * Real.sqrt (Work.Coercivity.EfEta f)) := by
        rw [hzsq]
    _ ≤ |Λ| * (220 * Real.sqrt (Work.Coercivity.EfEta f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hsq_le (Real.sqrt_nonneg _)
    _ = 220 * |Λ| * Real.sqrt (Work.Coercivity.EfEta f) := by ring

/-- **The projector-correction pairing of `𝓛_Γ^T`, in the interior class.**
`T4fun α f` is the *constant* `C₀(f) = L₁₂(Transport f)(0)` times the fixed function
`(Γ/c)(2z²/(1+z)³)`, so
`⟨T4fun α f, f⟩_{w² sin^{-η}} = C₀(f)·⟨(Γ/c)(2z²/(1+z)³), f⟩_{w² sin^{-η}}`, and the
Cauchy–Schwarz bound of `Work.Coercivity.gPsi_eta_abs_le` gives the constant `220`. -/
theorem gPsi_eta_abs_le_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f)
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T4fun α f) f|
          ≤ 220 * |Work.Coercivity.C0 f| * Real.sqrt (Work.Coercivity.EfEta f) := by
  have haesm := aesm_smoothQuad hsq
  have haesm' : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.volume_restrict_prod]; exact haesm
  refine ⟨?_, ?_⟩
  · have hg := etaW_gPsi_integrable_Q α hα hα1 f haesm' hF
    refine IntegrableOn.congr_fun (Integrable.const_mul hg (Work.Coercivity.C0 f)) ?_
      (measurableSet_Ici.prod measurableSet_Icc)
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.T4fun]
    ring
  · rw [show Work.Coercivity.T4fun α f
        = fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.C0 f from rfl]
    exact wip_gPsi_eta_le_aux α hα hα1 f (Work.Coercivity.C0 f) haesm hF

end Work.FTS.CoercivityFix.Coer1T
