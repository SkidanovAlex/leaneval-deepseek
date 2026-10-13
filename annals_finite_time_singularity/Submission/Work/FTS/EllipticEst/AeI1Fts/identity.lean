import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.cut_deriv_tendsto_zero
import Submission.Work.FTS.EllipticEst.AeI1Fts.cross_joint_h
import Submission.Work.FTS.EllipticEst.AeI1Fts.radial_identity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/identity` — the weak-class `I₁` chain identity

The identity `IP (AA u) (BB u) = ⟨V,V⟩ - 2η⟨U,U⟩ - 2η(1+η)N - ⟨cw·U, BB⟩` of Step 2 of the
paper (Elgindi, Annals 194 (3) 2021), where `U = z∂_zu`, `V = z∂_z∂_θu`, `AA = z²∂_zzu`,
`BB = ∂_θθu`, `N = ∫∫U²cos²(2θ)sin(2θ)^{-(2+η)}w²`, and `⟨g,h⟩ = AngSecond.IP g h` is the
`w²sin(2θ)^{-η}`-pairing.

The proof combines the two integration-by-parts halves, both proved in this directory:

* `radial_identity` — the radial `z`-integration by parts together with the angular
  `θ`-integration by parts of the mixed term:
  `⟨AA,BB⟩ + ⟨cw·U,BB⟩ = ⟨V,V⟩ - 2η∫∫U·V·cos(2θ)sin(2θ)^{-(1+η)}w²`;
* `cross_joint_h` — the second angular integration by parts, which converts the cross term into
  the diagonal angular energy and the `N`-term:
  `∫∫UVcos(2θ)σ₁w² = ∫∫U²σw² + (1+η)N`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Interval bookkeeping for the pairing `IP` -/

theorem integral_Iz_eq_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z :=
  MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici' (measure_singleton (0 : ℝ))).symm

theorem integral_Iθ_eq_Ioo (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Iθo, f θ :=
  MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (measure_singleton (0 : ℝ))
      (measure_singleton (Real.pi / 2))).symm

theorem IP_self_eq (f : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AngSecond.IP f f
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, (f z θ) ^ 2 * sigE θ := by
  have hIz : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        f z θ * f z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          f z θ * f z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
    integral_Iz_eq_Ioi _
  rw [Work.FTS.EllipticEst.AngSecond.IP, hIz]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  have hIθ : (∫ θ in Work.Spaces.Iθ,
        f z θ * f z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Iθo, f z θ * f z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    integral_Iθ_eq_Ioo _
  rw [hIθ]
  have hre : (fun θ => f z θ * f z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = fun θ => (Work.Spaces.w z) ^ 2 * (f z θ * f z θ * sigE θ) := by
    funext θ
    show f z θ * f z θ * (Work.Spaces.w z) ^ 2 * sigE θ
        = (Work.Spaces.w z) ^ 2 * (f z θ * f z θ * sigE θ)
    ring
  rw [hre, MeasureTheory.integral_const_mul]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  ring

/-! ## The slicewise integrability facts feeding the cross identity -/

/-- The `σ`-weighted square of a slice of an `ℋ⁰`-honest function is integrable. -/
theorem slice_sigE_int {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Iθo := by
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz
  have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
      Work.Spaces.Iθ := hf.1 z hzmem
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => hk_zero_eq α f hθ)
      measurableSet_Icc
  have h3 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
    have h4 : MeasureTheory.Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.const_mul h2 _
    refine MeasureTheory.IntegrableOn.congr_fun h4 (fun θ _ => ?_) measurableSet_Icc
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul]
  exact MeasureTheory.IntegrableOn.congr_set_ae h3
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi/2))

/-- **AM–GM domination of the cross integrand**: `|W W' cos(2θ) σ₁| ≤ (W²cos²(2θ)σ₂ + W'²σ)/2`
pointwise, so the cross term is integrable as soon as the two diagonal terms are. -/
theorem slice_cross_int {W W' : ℝ → ℝ}
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (W θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (W' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => W θ * W' θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Iθo)) :
    MeasureTheory.IntegrableOn
      (fun θ => W θ * W' θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) Iθo := by
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => (W θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        + (W' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := hN.add hD
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.Integrable.const_mul hsum (1/2)) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsp : (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hp2 : ((Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)) ^ 2
      = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    rw [pow_two, ← Real.rpow_add hs]; congr 1; ring
  have hq2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2)) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [pow_two, ← Real.rpow_add hs]; congr 1; ring
  show ‖W θ * W' θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))‖
      ≤ 1 / 2 * (W θ ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
          + W' θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hs.le _), hsp]
  have e1 : (|W θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2)) ^ 2
      = W θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hp2]
  have e2 : (|W' θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2)) ^ 2
      = W' θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, sq_abs, hq2]
  have h := two_mul_le_add_sq
    (|W θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)/2))
    (|W' θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)/2))
  nlinarith [h, e1, e2]

/-! ## The target -/

theorem identity {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta
            * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.U u)
                (Work.FTS.EllipticEst.AeI1Fts.U u)
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
                * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                    (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                      * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
        - Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
            (Work.FTS.EllipticEst.AeI1Fts.BB u) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ## the slicewise integrability hypotheses of the cross identity
  have hintA : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Iθo := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact slice_sigE_int hU hz
  have hintV2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact slice_sigE_int hV hz
  have hintN : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo := by
    have h0 := (N_bound h hV).1
    filter_upwards [h0] with z hz
    exact MeasureTheory.IntegrableOn.congr_fun hz (fun θ _ => by rw [sig2]) measurableSet_Ioo
  have hintC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => U u z θ * V u z θ * Real.cos (2 * θ)
        * sig1 θ) Iθo := by
    filter_upwards [hintN, hintV2, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hNz hVz hz
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun θ => U u z θ * V u z θ * Real.cos (2 * θ)
          * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (MeasureTheory.volume.restrict Iθo) := by
      have hcontU : ContinuousOn (fun θ => U u z θ) Iθo :=
        (contDiffOn_slice_U_one hS hz).continuousOn
      have hcontV : ContinuousOn (fun θ => V u z θ) Iθo :=
        (contDiffOn_slice_V_one hS hz).continuousOn
      have hcontc : ContinuousOn (fun θ => Real.cos (2 * θ)) Iθo :=
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      have hsin2 : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      have hconts : ContinuousOn
          (fun θ => (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) Iθo :=
        hsin2.continuousOn.rpow_const (fun θ hθ => by
          left
          have h1 : (0:ℝ) < 2 * θ := by linarith [hθ.1]
          have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
      exact (((hcontU.mul hcontV).mul hcontc).mul hconts).aestronglyMeasurable measurableSet_Ioo
    have hintC' := slice_cross_int hNz hVz hmeas
    exact MeasureTheory.IntegrableOn.congr_fun hintC' (fun θ _ => by rw [sig1]) measurableSet_Ioo
  -- ## the two halves of the chain
  have hR := radial_identity h hU hV hA hB
  have hC := cross_joint_h h hU hV hintA hintN hintC
  have hIp := IP_self_eq (U u)
  have h1 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                  * Real.cos (2 * θ) * Work.FTS.EllipticEst.AeI1Fts.sig1 θ)
        - Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
            (Work.FTS.EllipticEst.AeI1Fts.BB u) := by
    linarith [hR]
  rw [h1, hC, hIp]
  ring

end

end Work.FTS.EllipticEst.AeI1Fts
