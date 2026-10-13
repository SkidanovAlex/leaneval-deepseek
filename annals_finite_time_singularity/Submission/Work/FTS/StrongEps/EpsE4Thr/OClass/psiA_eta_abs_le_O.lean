import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1T.psiA_eta_abs_le_Q
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.L2CoercivityTransportEta
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
set_option maxHeartbeats 2000000

/-!
# The `L₁₂`-correction pairing `⟨T1fun α f, f⟩_{w² sin^{-η}}` in the **open** class

`T1fun α f = (2 z Γ(θ)/(c(1+z)²))·L₁₂(f)(z)` is the `L₁₂`-term of `𝓛_Γ`, and this file proves
the two facts about its `η`-weighted pairing against `f` that the `η`-slot of the level-1
coercivity of `𝓛_Γ^T` needs, **in the open class** `SmoothOpen` (genuine `C^∞` on the *open*
quadrant `(0,∞) × (0,π/2)`, the class carried by `RegQo`) rather than the interior class
`SmoothQuad` (`C^∞` on the strip `z > -1`) of
`Submission/Work/FTS/CoercivityFix/Coer1T/psiA_eta_abs_le_Q.lean` (whose statement is
`Work.FTS.CoercivityFix.Coer1T.psiA_eta_abs_le_Q`):

* the integrand `T1fun α f · f · w² sin(2θ)^{-η}` is jointly integrable on the quadrant;
* the pairing obeys `|⟨T1fun α f, f⟩_{w² sin^{-η}}| ≤ 220 √(EL12z f) √(EfEta f)`.

The proof is Cauchy–Schwarz in `L²(P)` (`P` the product of the restrictions of Lebesgue measure
to `Iz` and `Iθ`) after the pointwise split
`(2zΓ/(c(1+z)²))Λ f w² s^{-η} = 2·[(Γ/c)(Λ/z)s^{-η/2}]·[f w s^{-η/2}]`
(valid because `w = z²w²/(1+z)²`, i.e. `z·w²/(1+z)² = w/z`), which is the *only* place the weight
`w` enters.  The two `L²` norms are `√(EL12z f · ∫_θ (Γ/c)²s^{-η})` and `√(EfEta f)`, and
`∫_θ (Γ/c)²s^{-η} ≤ 12100 = 110²` (`Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100`), giving
`2·110 = 220`.

The two ingredients really used are `HardyHyp f` (which supplies `∫ (L₁₂(f)/z)² < ∞` and the
continuity of `L₁₂(f)` on `(0,∞)`) and the joint integrability `hF` of `f²w² sin^{-η}`; the
a.e. strong measurability of `f` comes from `SmoothOpen` via
`Work.Spaces.aesm_of_continuousOn_Qd` (the open quadrant and `Iz ×ˢ Iθ` differ by a null set).
-/

/-- **The pointwise Cauchy–Schwarz splitting** of the `T1fun` pairing.

For `z ≠ 0` and `0 ≤ s = sin(2θ)` one has
`(2zΓ/(c(1+z)²))Λ·f·w² s^{-η} = 2·[(Γ/c)(Λ/z)s^{-η/2}]·[f w s^{-η/2}]`,
because `w = (1+z)²/z²` gives `z w²/(1+z)² = w/z`. -/
theorem T1fun_eta_split_O (α : ℝ) (hc : Work.Spaces.c α ≠ 0) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ≠ 0) (hs : 0 ≤ Real.sin (2 * θ)) :
    Work.Coercivity.T1fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = 2 * (((Work.Spaces.Gam α θ / Work.Spaces.c α)
              * (Work.Coercivity.L12f f z / z)
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2))
            * (f z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2))) := by
  rw [← Work.Coercivity.rpow_half_sq (Real.sin (2 * θ)) hs]
  simp only [Work.Coercivity.T1fun, Work.Spaces.w]
  field_simp

theorem psiA_eta_abs_le_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hfH : Work.Coercivity.HardyHyp f)
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T1fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T1fun α f) f|
          ≤ 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f) := by
  set P : Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (Work.Coercivity.L12f f p.1 / p.1)
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  -- ### A.e. strong measurability
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) P := by
    rw [hP]
    exact Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hso.continuousOn
  have hLesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) P := by
    have h1 := Work.Coercivity.aesm_L12f (Work.Coercivity.L12f_continuousOn f hfH)
    rwa [← Work.Coercivity.prod_restrict_eq] at h1
  have hsinesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hAesm : AEStronglyMeasurable A P := by
    rw [hA]
    have hw : Measurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (p.1)⁻¹ * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) := by
      unfold Work.Spaces.Gam
      fun_prop
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (p.1)⁻¹ * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)
        * Work.Coercivity.L12f f p.1) P :=
      hw.aestronglyMeasurable.mul hLesm
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P := by
      apply Measurable.aestronglyMeasurable
      unfold Work.Spaces.w
      fun_prop
    exact (haesm.mul hw).mul hsinesm
  -- ### Square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) Work.Spaces.Iz := by
    have h1 := hfH.intA 1 (by norm_num : (1 : ℕ) ≤ 2)
    have h2 : IntegrableOn (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
      show (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ))
          = (Work.Coercivity.L12f f z / z) ^ 2
      have hz : (z : ℝ) ^ (2 * ((1 : ℕ) : ℝ)) = z ^ (2 : ℕ) := by
        rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hz, div_pow]
    show Integrable (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact h2
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
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    refine ((Work.Coercivity.integrableOn_prod hF).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  -- ### Joint integrability of the product
  have hABi : Integrable (fun p : ℝ × ℝ => A p * B p) P := by
    refine Integrable.mono' (hA2.add hB2) (hAesm.mul hBesm) ?_
    filter_upwards with p
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    have h1 : 0 ≤ (|A p| - |B p|) ^ 2 := sq_nonneg _
    have h2 : (|A p| - |B p|) ^ 2
        = (A p) ^ 2 - 2 * (|A p| * |B p|) + (B p) ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]
      ring
    have h3 : 0 ≤ |A p| * |B p| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  have hIntProd : Integrable (fun p : ℝ × ℝ => 2 * (A p * B p)) P := hABi.const_mul 2
  -- ### The weighted pairing as a product-measure integral
  have hIntOn : IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.T1fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hIntProd
    rw [IntegrableOn, ← Work.Coercivity.prod_restrict_eq]
    refine h.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos, Work.Coercivity.ae_prod_quadrant] with p hpos hq
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hq
    simp only [Function.uncurry_apply_pair]
    exact (T1fun_eta_split_O α hc f (ne_of_gt hpos) (hsin0 θ hθ)).symm
  have hwip : Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T1fun α f) f = ∫ p, 2 * (A p * B p) ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T1fun α f) f hIntOn, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_pos, Work.Coercivity.ae_prod_quadrant] with p hpos hq
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hq
    exact T1fun_eta_split_O α hc f (ne_of_gt hpos) (hsin0 θ hθ)
  -- ### Cauchy–Schwarz
  have hCS := Work.Coercivity.sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P|
      ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### The values of the two square-integrals
  have hBval : ∫ p, B p ^ 2 ∂P = Work.Coercivity.EfEta f := by
    have hF' : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      IntegrableOn.congr_fun hF (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [Work.Coercivity.EfEta_eq_wip, Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f hF', ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P
      = Work.Coercivity.EL12z f
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => (Work.Coercivity.L12f f p.1 / p.1) ^ 2
          * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [Work.Coercivity.integral_prod_sep
      (a := fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
      (b := fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ha hb]
    rfl
  -- ### Numerical conclusion
  have hX := Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hELnn : 0 ≤ Work.Coercivity.EL12z f := by
    rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hsqrt : Real.sqrt (Work.Coercivity.EL12z f)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ 110 * Real.sqrt (Work.Coercivity.EL12z f) := by
    have h110 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    calc Real.sqrt (Work.Coercivity.EL12z f)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ Real.sqrt (Work.Coercivity.EL12z f) * 110 :=
          mul_le_mul_of_nonneg_left h110 (Real.sqrt_nonneg _)
      _ = 110 * Real.sqrt (Work.Coercivity.EL12z f) := by ring
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun hIntOn (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  · calc |Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.T1fun α f) f|
        = |∫ p, 2 * (A p * B p) ∂P| := by rw [hwip]
      _ = 2 * |∫ p, A p * B p ∂P| := by
          rw [MeasureTheory.integral_const_mul, abs_mul]
          norm_num
      _ ≤ 2 * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
          mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = 2 * (Real.sqrt (Work.Coercivity.EL12z f
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          rw [hAval, hBval]
      _ = 2 * (Real.sqrt (Work.Coercivity.EL12z f)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          rw [Real.sqrt_mul hELnn]
      _ ≤ 2 * ((110 * Real.sqrt (Work.Coercivity.EL12z f))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      _ = 220 * Real.sqrt (Work.Coercivity.EL12z f)
            * Real.sqrt (Work.Coercivity.EfEta f) := by ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
