import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1omega_low_nonneg
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.w1omegaFun_facts`

The `L¹`-weight facts about FS's §4 kernel `W₁ω = W(1−ω)ω`, in the form in
which the `L¹`-tail chapter consumes them: for a nonnegative radial potential
`v` of range `R` with scattering solution `h`, in the regime

  `R/ℓ ≤ r₁`  and  `C·(R/ℓ)² ≤ 1/2`,   where `|(χ⋆χ)(x) − 1| ≤ C‖x‖²` on `‖x‖ ≤ r₁`

(so that the χ-renormalisation denominator `(χ⋆χ)(·/ℓ)` is within `C(R/ℓ)²` of
`1` on the support `ball 0 R` of the numerator), one has

* `W₁ω ∈ L¹(ℝ³)`;
* `0 ≤ W₁ω` a.e.;
* `W₁ω ≤ (1 + 2C(R/ℓ)²)·g₀` a.e. (the renormalisation factor is `≤ 1+2a` when
  `a = C(R/ℓ)² ≤ 1/2`, since `(1+2a)(1−a) = 1 + a(1−2a) ≥ 1`);
* `W₁ω` vanishes outside `ball 0 R`.

The numerical core of the last two items is that
`1 - a ≤ (χ⋆χ)(·/ℓ) ≤ 1 + a` on the support, together with `0 ≤ ω ≤ 1` a.e. and
`g₀ = v(1−ω) ≥ 0` a.e.
-/

namespace Work.BoseBoxFock.L1Tails

open MeasureTheory
open scoped Topology Real

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.BoseB7AK.W1rows

/-- **The χ-renormalisation denominator is `≥ 1 − C(R/ℓ)²` on `ball 0 R`.**

For `‖z‖ ≤ R` the rescaled argument `z/ℓ` satisfies `‖z/ℓ‖ ≤ R/ℓ ≤ r₁`, so the
Taylor hypothesis `hT` applies there and gives
`|(χ⋆χ)(z/ℓ) − 1| ≤ C‖z/ℓ‖² = C(‖z‖/ℓ)² ≤ C(R/ℓ)²`. -/
lemma convScale_ge_one_sub {R r₁ C ℓ : ℝ} (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    ∀ z : ℝ³, ‖z‖ ≤ R → 1 - C * (R / ℓ) ^ 2 ≤ Submission.BoseGases.convScale ℓ z := by
  intro z hz
  have hℓinv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hzr : ‖(ℓ⁻¹) • z‖ ≤ R / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg hℓinv]
    have h1 : ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * R := mul_le_mul_of_nonneg_left hz hℓinv
    have h2 : ℓ⁻¹ * R = R / ℓ := by field_simp
    linarith [h1, h2]
  have hnorm : ‖(ℓ⁻¹) • z‖ ≤ r₁ := le_trans hzr hreg
  have htz := hT ((ℓ⁻¹) • z) hnorm
  have hsq : C * ‖(ℓ⁻¹) • z‖ ^ 2 ≤ C * (R / ℓ) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzr 2) hC
  have hb := abs_le.mp (le_trans htz hsq)
  have hkey : 1 - C * (R / ℓ) ^ 2
      ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
          ((ℓ⁻¹) • z) := by
    linarith [hb.1]
  simpa [Submission.BoseGases.convScale] using hkey

/-- **The pointwise domination of `W₁ω` by the scattering `g₀`, a.e.**

On `ball 0 R` the numerator `g₀ω = v(1−ω)ω` is `≤ g₀` a.e. and the
renormalisation denominator is `≥ 1 − a` with `a = C(R/ℓ)² ≤ 1/2`, so
`W₁ω = g₀·ω/(χ⋆χ)(·/ℓ) ≤ g₀·(1+2a)`; outside `ball 0 R` both sides vanish. -/
lemma W1omegaFun_le_g0_ae {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    ∀ᵐ x ∂(volume : Measure ℝ³),
      Work.BoseFixR.W1omegaFun v h ℓ x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hb := Submission.BoseGases.scattering_bounds_ae hR hv hvrad hv_supp hrad hw
  have hgn := Submission.BoseGases.scattering_g_nonneg hR hv hvrad hv_supp hrad hw
  have ha0 : 0 ≤ C * (R / ℓ) ^ 2 := mul_nonneg hC (sq_nonneg _)
  have h2a : 0 ≤ 1 + 2 * C * (R / ℓ) ^ 2 := by linarith
  have key : (1 : ℝ) ≤ (1 + 2 * C * (R / ℓ) ^ 2) * (1 - C * (R / ℓ) ^ 2) := by
    have h1 : 0 ≤ 1 - 2 * (C * (R / ℓ) ^ 2) := by linarith
    nlinarith [mul_nonneg ha0 h1]
  filter_upwards [hb.1, hb.2, hgn] with x hw0 hw1 hg0
  rcases le_or_gt R ‖x‖ with hx | hx
  · have hxz : Work.BoseFixR.W1omegaFun v h ℓ x = 0 :=
      W1omegaFun_eq_zero_of_R_le_norm hv_supp h hx
    have hg0z : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
    rw [hxz, hg0z, mul_zero]
  · have hxle : ‖x‖ ≤ R := le_of_lt hx
    have hcs := convScale_ge_one_sub (R := R) (r₁ := r₁) (C := C) (ℓ := ℓ)
      hC hr₁ hT hℓ hreg hcond x hxle
    have hcspos : 0 < Submission.BoseGases.convScale ℓ x := by linarith
    have hg0' : 0 ≤ Submission.BoseGases.g0 v h x := by simpa [Submission.BoseGases.g0] using hg0
    have hratio : Classical.choose h x / Submission.BoseGases.convScale ℓ x
        ≤ 1 + 2 * C * (R / ℓ) ^ 2 := by
      rw [div_le_iff₀ hcspos]
      have h1 : (1 : ℝ) ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.convScale ℓ x := by
        calc (1 : ℝ) ≤ (1 + 2 * C * (R / ℓ) ^ 2) * (1 - C * (R / ℓ) ^ 2) := key
          _ ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.convScale ℓ x :=
              mul_le_mul_of_nonneg_left hcs h2a
      linarith [hw1, h1]
    have hW : Work.BoseFixR.W1omegaFun v h ℓ x
        = Submission.BoseGases.g0 v h x * Classical.choose h x
            / Submission.BoseGases.convScale ℓ x := rfl
    rw [hW]
    calc Submission.BoseGases.g0 v h x * Classical.choose h x
            / Submission.BoseGases.convScale ℓ x
        = Submission.BoseGases.g0 v h x
            * (Classical.choose h x / Submission.BoseGases.convScale ℓ x) := by ring
      _ ≤ Submission.BoseGases.g0 v h x * (1 + 2 * C * (R / ℓ) ^ 2) :=
            mul_le_mul_of_nonneg_left hratio hg0'
      _ = (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by ring

/-- **`W₁ω ∈ L¹`.**  The numerator `g₀ω` is integrable and vanishes outside
`ball 0 R`, where the renormalisation denominator is `≥ 1 − a ≥ 1/2`; hence
`|W₁ω| ≤ 2|g₀ω|` pointwise and `Integrable.mono'` applies. -/
lemma W1omegaFun_integrable' {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) := by
  have hNil : MeasureTheory.Integrable (W1omegaNum v h) :=
    W1omegaNum_integrable hR (fun x => hv x) hvrad hv_supp h
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → W1omegaNum v h z = 0 := fun z hz => by
    have hz0 : Submission.BoseGases.g0 v h z = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    simp [W1omegaNum, hz0]
  have hWm : AEStronglyMeasurable (Work.BoseFixR.W1omegaFun v h ℓ) := by
    have h1 : AEMeasurable (Work.BoseFixR.W1omegaFun v h ℓ) := by
      rw [W1omegaFun_eq]
      exact hNil.aemeasurable.div
        (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    exact h1.aestronglyMeasurable
  have hdom : ∀ᵐ z ∂(volume : Measure ℝ³),
      ‖Work.BoseFixR.W1omegaFun v h ℓ z‖ ≤ 2 * |W1omegaNum v h z| := by
    refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs]
    by_cases hz : W1omegaNum v h z = 0
    · rw [W1omegaFun_eq]
      simp [Submission.BoseGases.wScaled, hz]
    · have hzR : ‖z‖ < R := lt_of_not_ge (fun hge => hz (hsupp z hge))
      have hcs := convScale_ge_one_sub (R := R) (r₁ := r₁) (C := C) (ℓ := ℓ)
        hC hr₁ hT hℓ hreg hcond z hzR.le
      have hhalf : (1 / 2 : ℝ) ≤ Submission.BoseGases.convScale ℓ z := by linarith
      have hpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le (by norm_num) hhalf
      rw [W1omegaFun_eq]
      dsimp only [Submission.BoseGases.wScaled]
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have hstep := mul_le_mul_of_nonneg_left hhalf
        (show (0 : ℝ) ≤ 2 * |W1omegaNum v h z| by positivity)
      linarith [hstep]
  exact MeasureTheory.Integrable.mono' (hNil.abs.const_mul 2) hWm hdom

theorem w1omegaFun_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : Work.UBB.ScatSol v) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) ∧
      (∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixR.W1omegaFun v h ℓ x) ∧
      (∀ᵐ x : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1omegaFun v h ℓ x
          ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → Work.BoseFixR.W1omegaFun v h ℓ x = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact W1omegaFun_integrable' hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  · exact W1omegaFun_nonneg_ae hR (fun x => hv x) hvrad hv_supp h
  · exact W1omegaFun_le_g0_ae hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  · intro x hx
    exact W1omegaFun_eq_zero_of_R_le_norm hv_supp h hx

end Work.BoseBoxFock.L1Tails
