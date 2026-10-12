import ChallengeDeps
import Submission.Work.BoseBoxFock.L1Tails.W1fun_coulomb_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem W1fun_integrable_of_regime {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) ∧
      (∀ᵐ x : ℝ³, 0 ≤ Work.BoseFixR.W1fun v h ℓ x) ∧
      (∀ x : ℝ³, R ≤ ‖x‖ → Work.BoseFixR.W1fun v h ℓ x = 0) := by
  set δ : ℝ := 2 * C * (R / ℓ) ^ 2 with hδdef
  -- the dominating weight `g₀ = v(1−ω)` is integrable
  have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  -- the a.e. two-sided sandwich `g₀ ≤ W₁ ≤ (1+δ)g₀` and `g₀ ≥ 0` a.e.
  have hsand := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := ℓ)
    (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hg0ae := Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hW10 : ∀ᵐ x : ℝ³, 0 ≤ Work.BoseFixR.W1fun v h ℓ x := by
    filter_upwards [hsand, hg0ae] with x hx hgx
    have h' : 0 ≤ Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x := by
      linarith [hx.1, hgx]
    simpa [Work.BoseFixR.W1fun] using h'
  -- integrability of `W₁ = wScaled ℓ g₀`: a.e. strong measurability from the
  -- explicit representation, then domination by `(1+δ)g₀`
  have hW1I : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    have hconv : MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ³ => (Submission.BoseGases.convScale ℓ x)⁻¹) :=
      (Measurable.inv ((Submission.BoseGases.conv_contDiff.continuous.measurable).comp
        (measurable_id.const_smul (ℓ⁻¹)))).aestronglyMeasurable
    have hmeas : MeasureTheory.AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
      refine MeasureTheory.AEStronglyMeasurable.congr (hgI.aestronglyMeasurable.mul hconv) ?_
      filter_upwards with x
      simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
    refine MeasureTheory.Integrable.mono' (hgI.const_mul (1 + δ)) hmeas ?_
    filter_upwards [hW10, hsand] with x h0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h2 : Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x ≤
        (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by linarith [hx.2]
    rw [hδdef]
    simpa [Work.BoseFixR.W1fun] using h2
  refine ⟨hW1I, hW10, ?_⟩
  -- support: `W₁` cannot leave `supp v ⊆ ball 0 R`
  intro x hx
  have hgx : Submission.BoseGases.g0 v h x = 0 :=
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hgx]

end Work.BoseBoxFock
