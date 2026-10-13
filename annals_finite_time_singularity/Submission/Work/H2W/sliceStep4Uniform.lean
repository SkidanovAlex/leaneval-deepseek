import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_v_ident
import Submission.Work.FTS.EllipticEst.remov.slice_Q_pointwise
import Submission.Work.FTS.EllipticEst.remov.sliceV2Uniform
import Submission.Work.FTS.EllipticEst.remov.sliceUdivCosUniform
import Submission.Work.FTS.EllipticEst.remov.sliceG2Uniform
import Submission.Work.FTS.EllipticEst.remov.sliceY2Uniform
import Submission.Work.FTS.EllipticEst.remov.Step4.slice_step4_identity
import Submission.Work.FTS.EllipticEst.remov.Step4.abs_integral_mul_sigma_le
import Submission.Work.FTS.EllipticEst.remov.Step4.slice_Xt_sq_bound
import Submission.Work.FTS.EllipticEst.remov.Step4.slice_Xt_T_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.remov

set_option maxHeartbeats 1600000

/-! ## Elementary facts about the angular weight `σ = sin(2θ)^{2-γ}` on `Iθ` -/

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Almost every point of `Iθ` lies in the open interval. -/
private lemma ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun x hx => hx)
  have h2 : (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = (volume : Measure ℝ).restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rwa [h2] at h1

/-- Transferring a pointwise property from `Ioo 0 (π/2)` to `Iθ`. -/
private lemma ae_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), P θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, P θ :=
  ae_Iθ_mem_Ioo.mono fun _ hθ => h _ hθ

private lemma measurable_sig (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun _ => Or.inr (by linarith))).measurable

/-- The pointwise identity `u''' + g' = sinθ v'' − 4cosθ v' + 5 sinθ v`, `v = u/cos θ`,
used to put the pairing `(tan θ u)''·u'''` into the `v`-form. -/
private lemma T_v_form (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv u)) θ + deriv g θ
        = Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + 5 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  rw [slice_gprime_v_ident u g hu hg θ hθ, (slice_v_identities u hu θ hθ).2.1]
  ring

/-- The elementary arithmetic closing the estimate: from the four coercivity bounds and the
absorbed pairing bound, `∫(u''')²σ` is controlled by `D + B + C₁ + C₀`. -/
private lemma step4_arith {A D B C1 C0 V2 Y2 Y3 G2 Cv Ch Cg Cy : ℝ}
    (hD0 : 0 ≤ D) (hB0 : 0 ≤ B) (hC10 : 0 ≤ C1) (hC00 : 0 ≤ C0)
    (_hCv : 0 < Cv) (hCh : 0 < Ch) (hCg : 0 < Cg) (hCy : 0 < Cy)
    (hV2b : V2 ≤ Cv * (D + B + C1 + C0))
    (hY3b : Y3 ≤ Ch * (C1 + C0))
    (hG2b : G2 ≤ Cg * (D + B + C1 + C0))
    (hY2b : Y2 ≤ Cy * (G2 + B + C1 + C0))
    (hmain : A ≤ (1 / 4) * A + (17 / 8) * D + 72 * C1 + 10 * V2 + 31 * Y2 + 13 * Y3) :
    A ≤ ((4 / 3) * ((17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch) + 1)
          * (D + B + C1 + C0) := by
  have hRnn : 0 ≤ D + B + C1 + C0 := by linarith
  have hY2R : Y2 ≤ Cy * (Cg + 1) * (D + B + C1 + C0) := by
    nlinarith [hY2b, hG2b, hCy, hCg, hRnn, hD0, hB0, hC10, hC00]
  have hY3R : Y3 ≤ Ch * (D + B + C1 + C0) := by nlinarith [hY3b, hC10, hC00]
  have hstep : A ≤ (1 / 4) * A +
      ((17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch) * (D + B + C1 + C0) := by
    nlinarith [hmain, hV2b, hY2R, hY3R, hRnn, hD0, hB0, hC10, hC00]
  nlinarith [hstep, hRnn]

theorem sliceStep4Uniform : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
                Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨Cv, hCv0, hV2lem⟩ := sliceV2Uniform
  obtain ⟨Ch, hCh0, hY3lem⟩ := sliceUdivCosUniform
  obtain ⟨Cg, hCg0, hG2lem⟩ := sliceG2Uniform
  obtain ⟨Cy, hCy0, hY2lem⟩ := sliceY2Uniform
  refine ⟨(4 / 3) * ((17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch) + 1, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch := by
      positivity
    linarith
  · intro γ u g hγ1 hγ2 hu hcont hu0 hupi hode hA hB hC1 hC0 hD
    have hγ2' : γ ≤ 2 := by linarith
    have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
    have hσle : ∀ θ ∈ Work.Spaces.Iθ, Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
      fun θ hθ => Real.rpow_le_one (sin_two_nonneg_Iθ hθ) (Real.sin_le_one _) (by linarith)
    have hIθmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
    -- ### the four coercivity bounds
    obtain ⟨hV2int, hV2bd⟩ := hV2lem γ u g hγ1 hγ2 hu hcont hu0 hupi hode hB hC1 hC0 hD
    obtain ⟨hY3int, hY3bd⟩ := hY3lem γ u hγ1 hγ2 hu hcont hu0 hupi hC1 hC0
    obtain ⟨hG2int, hG2bd⟩ := hG2lem γ u g hγ1 hγ2 hu hcont hu0 hupi hode hB hC1 hC0 hD
    obtain ⟨hY2int, hY2bd⟩ := hY2lem γ u g hγ1 hγ2 hu hcont hu0 hupi hode hG2int hB hC1 hC0
    -- ### the `(tan θ u)''·u'''` pairing bound
    have hXt2 := Work.FTS.EllipticEst.remov.Step4.slice_Xt_sq_bound γ (u := u) hu hV2int hY2int hY3int
    have hXtT := Work.FTS.EllipticEst.remov.Step4.slice_Xt_T_bound γ (u := u) hu hV2int hY2int hY3int
    have hXtAE : MeasureTheory.AEStronglyMeasurable
        (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv (deriv (fun t => Real.tan t * u t))).aestronglyMeasurable
    have hfmG : MeasureTheory.AEStronglyMeasurable (fun θ => deriv g θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv g).aestronglyMeasurable
    -- `u''' + g'` agrees a.e. with the explicit `v`-form
    have hTae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
        deriv (deriv (deriv u)) θ + deriv g θ
          = Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
            - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
            + 5 * Real.sin θ * (u θ / Real.cos θ) :=
      ae_of_forall_Ioo (T_v_form u g hu hode)
    have hXtTint : MeasureTheory.IntegrableOn (fun θ =>
        deriv (deriv (fun t => Real.tan t * u t)) θ *
          (deriv (deriv (deriv u)) θ + deriv g θ) *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
      refine Integrable.congr hXtT.1 ?_
      filter_upwards [hTae] with θ hθ
      rw [← hθ]
    have hXtTae : (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ *
          (deriv (deriv (deriv u)) θ + deriv g θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ *
          (Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
            - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
            + 5 * Real.sin θ * (u θ / Real.cos θ)) *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
      filter_upwards [hTae] with θ hθ
      rw [hθ]
    have hXtTbd : (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
        (deriv (deriv (deriv u)) θ + deriv g θ) *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 4 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
      rw [MeasureTheory.integral_congr_ae hXtTae]
      exact hXtT.2
    obtain ⟨hXtGint, hXtGbd⟩ := Work.FTS.EllipticEst.remov.Step4.abs_integral_mul_sigma_le γ 2 (by norm_num)
      (f := fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
      (h := fun θ => deriv g θ) hXtAE hfmG hσnn hXt2.1 hD
    have hXtGbd' : |∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun t => Real.tan t * u t)) θ * deriv g θ *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)|
        ≤ 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (1 / 8) * (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
      have hcoef : (1 : ℝ) / (4 * 2) = 1 / 8 := by norm_num
      simpa only [hcoef] using hXtGbd
    have hnegX : -(∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun t => Real.tan t * u t)) θ * deriv g θ *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (1 / 8) * (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
      le_trans (neg_le_abs _) hXtGbd'
    have hsplitPt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (deriv (fun t => Real.tan t * u t)) θ * deriv (deriv (deriv u)) θ *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        = deriv (deriv (fun t => Real.tan t * u t)) θ *
            (deriv (deriv (deriv u)) θ + deriv g θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          - deriv (deriv (fun t => Real.tan t * u t)) θ * deriv g θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
      intro θ _; ring
    have hsplitAe : (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ *
          deriv (deriv (deriv u)) θ * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ *
            (deriv (deriv (deriv u)) θ + deriv g θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          - deriv (deriv (fun t => Real.tan t * u t)) θ * deriv g θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
      ae_of_forall_Ioo hsplitPt
    have hsplit : (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
        deriv (deriv (deriv u)) θ * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        = (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
            (deriv (deriv (deriv u)) θ + deriv g θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          - (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
            deriv g θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
      rw [MeasureTheory.integral_congr_ae hsplitAe]
      exact MeasureTheory.integral_sub hXtTint hXtGint
    have hXtI2bd : (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
        deriv (deriv (deriv u)) θ * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 10 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 31 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 13 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (1 / 8) * (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
      have hsq := hXt2.2
      linarith [hsplit, hXtTbd, hnegX, hsq]
    -- ### the identity `(E)`
    have hE := Work.FTS.EllipticEst.remov.Step4.slice_step4_identity γ hγ2' (u := u) (g := g) hu hode hA hD hC1
    -- ### integrability of `(u')²σ` and its comparison with `C₁`
    have hu1sig : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
      refine hC1.mono' ?_ ?_
      · exact (((measurable_deriv u).pow_const 2).mul (measurable_sig γ hγ2)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure ℝ))
          (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hσnn θ hθ))]
        exact mul_le_of_le_one_right (sq_nonneg _) (hσle θ hθ)
    have hu1sig_le : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
      refine MeasureTheory.integral_mono_ae hu1sig hC1 ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure ℝ))
        (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
      calc (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          ≤ (deriv u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left (hσle θ hθ) (sq_nonneg _)
        _ = (deriv u θ) ^ 2 := mul_one _
    -- ### the two weighted Young absorptions against `u'''`
    have hfmA : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (deriv (deriv u)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv (deriv (deriv u))).aestronglyMeasurable
    have hfmD : MeasureTheory.AEStronglyMeasurable (fun θ => deriv g θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv g).aestronglyMeasurable
    have hfmC : MeasureTheory.AEStronglyMeasurable (fun θ => deriv u θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (measurable_deriv u).aestronglyMeasurable
    obtain ⟨hI1int, hI1bd⟩ :=
      Work.FTS.EllipticEst.remov.Step4.abs_integral_mul_sigma_le γ (1 / 8) (by norm_num) hfmA hfmD hσnn hA hD
    obtain ⟨hI3int, hI3bd⟩ :=
      Work.FTS.EllipticEst.remov.Step4.abs_integral_mul_sigma_le γ (1 / 48) (by norm_num) hfmA hfmC hσnn hA hu1sig
    rw [show (1 : ℝ) / (4 * (1 / 8)) = 2 by norm_num] at hI1bd
    rw [show (1 : ℝ) / (4 * (1 / 48)) = 12 by norm_num] at hI3bd
    -- swap the order of the factors so the integrals match the identity `(E)`
    have hI1swap : (∫ θ in Work.Spaces.Iθ, deriv (deriv (deriv u)) θ * deriv g θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
        = ∫ θ in Work.Spaces.Iθ, deriv g θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    have hI3swap : (∫ θ in Work.Spaces.Iθ, deriv (deriv (deriv u)) θ * deriv u θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
        = ∫ θ in Work.Spaces.Iθ, deriv u θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- ### abbreviations
    set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hAdef
    set D : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hDdef
    set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ with hBdef
    set C1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hC1def
    set C0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hC0def
    set V2 : ℝ := ∫ θ in Work.Spaces.Iθ,
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hV2def
    set Y2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hY2def
    set Y3 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hY3def
    set G2 : ℝ := ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hG2def
    set I1 : ℝ := ∫ θ in Work.Spaces.Iθ, deriv g θ * deriv (deriv (deriv u)) θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hI1def
    set I2 : ℝ := ∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun t => Real.tan t * u t)) θ * deriv (deriv (deriv u)) θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hI2def
    set I3 : ℝ := ∫ θ in Work.Spaces.Iθ, deriv u θ * deriv (deriv (deriv u)) θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) with hI3def
    -- ### nonnegativity of the resources
    have hD0 : 0 ≤ D := by
      rw [hDdef]
      exact MeasureTheory.setIntegral_nonneg hIθmeas fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hσnn θ hθ)
    have hB0 : 0 ≤ B := by
      rw [hBdef]
      exact MeasureTheory.setIntegral_nonneg hIθmeas fun θ hθ =>
        mul_nonneg (sq_nonneg _) (by
          rw [Work.FTS.EllipticEst.sEta]
          exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    have hC10 : 0 ≤ C1 := by
      rw [hC1def]
      exact MeasureTheory.setIntegral_nonneg hIθmeas fun θ _ => sq_nonneg _
    have hC00 : 0 ≤ C0 := by
      rw [hC0def]
      exact MeasureTheory.setIntegral_nonneg hIθmeas fun θ _ => sq_nonneg _
    -- ### the three integral bounds in the abbreviated notation
    have hI1std : |I1| ≤ (1 / 8) * A + 2 * D := by
      have h := hI1bd
      rw [hI1swap] at h
      linarith [h]
    have hI3std : |I3| ≤ (1 / 48) * A + 12 * C1 := by
      have h := hI3bd
      rw [hI3swap] at h
      linarith [h, hu1sig_le]
    have hI2std : I2 ≤ 10 * V2 + 31 * Y2 + 13 * Y3 + (1 / 8) * D := hXtI2bd
    -- ### absorb
    have hmain : A ≤ (1 / 4) * A + (17 / 8) * D + 72 * C1 + 10 * V2 + 31 * Y2 + 13 * Y3 := by
      have h1 : -I1 ≤ (1 / 8) * A + 2 * D := le_trans (neg_le_abs I1) hI1std
      have h3 : -(6 * I3) ≤ 72 * C1 + (1 / 8) * A := by
        refine le_trans (neg_le_abs (6 * I3)) ?_
        rw [show |6 * I3| = 6 * |I3| by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]]
        linarith [hI3std]
      linarith [hE, h1, hI2std, h3]
    exact step4_arith hD0 hB0 hC10 hC00 hCv0 hCh0 hCg0 hCy0 hV2bd hY3bd hG2bd hY2bd hmain


end Work.H2W
