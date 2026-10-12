import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.L1Tails.coulInt_integrable_of_le
import Submission.Work.BoseBoxFock.L1Tails.w1omegaFun_facts
import Submission.Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.W1fun_coulomb_le` (T5 of the `L¹`-tail chapter)

The honest weights of the pair/cubic tails are only `L¹` (`W₁ ≤ (1+δ)g₀`, `g₀ ∈ L¹`), so the
`L²`-kernel route is unusable.  What pays is the **Coulomb energy** `∬W(x)W(y)/‖x−y‖`: it is
finite for `W = W₁ = wScaled ℓ g₀` and `W = W₁ω = wScaled ℓ (g₀ω)`, uniformly bounded by
`256π²·(a v)` — FS's `ĝω(0) = (2π)⁻³∫ĝ²/(2k²)`, i.e. `W ∈ Ḣ⁻¹`.

Route (design `sources/boseDCF/bose_L1tails.md`, T5):

* `g₀ := v(1−ω)`, `ω = Classical.choose h`; `∫g₀ = 8π(a v)` (`chosen_scattering_integral`) and
  `∬g₀g₀/‖x−y‖ = 8π∫g₀ω ≤ (8π)²(a v)` (`chosen_newton_double_le`);
* the Newton representation makes the **slice** of `g₀` bounded a.e.:
  `∫⁻_y g₀(y)‖x−y‖⁻¹ ≤ 8π` a.e. `x` (`Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le`, from
  `scattering_newton_representation` + `0 ≤ ω ≤ 1`);
* `coulInt_integrable_of_le` upgrades that slice bound to the pair integrability
  `CoulInt(A) ∈ L¹` and the bound `∫ CoulInt(A) ≤ c²κ∫g₀` for every a.e.-nonnegative `A` with
  `A ≤ c·g₀` a.e. and `κ = 8π`;
* both weights are sandwiched by the same `(1+2C(R/ℓ)²)g₀` (`wScaled_sandwich_at` /
  `wScaled_g0_ae_bounds` for `g₀`, and `wScaled_sandwich_ae` applied to the numerator `g₀ω`, which
  is `≤ g₀` since `0 ≤ ω ≤ 1` a.e.), and `1 + 2C(R/ℓ)² ≤ 2` by `hcond`;
* hence `∫ CoulInt(A) ≤ 2²·8π·8π(a v) = 256π²(a v)`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

theorem W1fun_coulomb_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : Work.UBB.ScatSol v) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    MeasureTheory.Integrable (Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ))
      ∧ (∫ p, Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ) p)
          ≤ 256 * Real.pi ^ 2 * _root_.BoseGases.a v
      ∧ MeasureTheory.Integrable (Work.BoseBoxFock.coulInt (Work.BoseFixR.W1omegaFun v h ℓ))
      ∧ (∫ p, Work.BoseBoxFock.coulInt (Work.BoseFixR.W1omegaFun v h ℓ) p)
          ≤ 256 * Real.pi ^ 2 * _root_.BoseGases.a v := by
  set g : E3 → ℝ := Submission.BoseGases.g0 v h with hgdef
  set δ : ℝ := 2 * C * (R / ℓ) ^ 2 with hδdef
  have hδeq : δ = 2 * C * (R / ℓ) ^ 2 := hδdef
  have hδ0 : 0 ≤ δ := by rw [hδeq]; exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)
  have hδle : δ ≤ 1 := by rw [hδeq]; linarith [hcond]
  have h1δ0 : 0 ≤ 1 + δ := by linarith
  have h1δsq : (1 + δ) ^ 2 ≤ 4 := by nlinarith
  -- facts about `g = g₀`
  have hgI : MeasureTheory.Integrable g := by
    rw [hgdef]; exact Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0 : ∀ᵐ x : E3, 0 ≤ g x := by
    rw [hgdef]; exact Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hgm : (∫ x, g x) = 8 * Real.pi * _root_.BoseGases.a v := by
    rw [hgdef]; exact Submission.BoseGases.chosen_scattering_integral h
  have hgnn : (0 : ℝ) ≤ ∫ x, g x := MeasureTheory.integral_nonneg_of_ae hg0
  have hslice : ∀ᵐ x : E3,
      (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) ≤ ENNReal.ofReal (8 * Real.pi) := by
    have hh := Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le (v := v) h hv hvrad hR hv_supp
    simpa [hgdef] using hh
  -- facts about `W₁ = wScaled ℓ g₀`
  have hsand := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := ℓ)
    (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hW1ge : ∀ᵐ x : E3, g x ≤ Work.BoseFixR.W1fun v h ℓ x := by
    filter_upwards [hsand] with x hx
    have h1 : Submission.BoseGases.g0 v h x ≤
        Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x := by linarith [hx.1]
    simpa [hgdef, Work.BoseFixR.W1fun] using h1
  have hW1le : ∀ᵐ x : E3, Work.BoseFixR.W1fun v h ℓ x ≤ (1 + δ) * g x := by
    filter_upwards [hsand] with x hx
    rw [hδeq]
    have h2 : Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by nlinarith [hx.2]
    simpa [hgdef, Work.BoseFixR.W1fun] using h2
  have hW10 : ∀ᵐ x : E3, 0 ≤ Work.BoseFixR.W1fun v h ℓ x := by
    filter_upwards [hg0, hW1ge] with x hgx hgex
    linarith
  have hW1I : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    have hconv : AEStronglyMeasurable
        (fun x : E3 => (Submission.BoseGases.convScale ℓ x)⁻¹) :=
      (Measurable.inv ((Submission.BoseGases.conv_contDiff.continuous.measurable).comp
        (measurable_id.const_smul (ℓ⁻¹)))).aestronglyMeasurable
    have hmul := hgI.aestronglyMeasurable.mul hconv
    have hmeas : AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
      refine AEStronglyMeasurable.congr hmul ?_
      filter_upwards with x
      simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hgdef, div_eq_mul_inv]
    refine MeasureTheory.Integrable.mono' (hgI.const_mul (1 + δ)) hmeas ?_
    filter_upwards [hW10, hW1le] with x h0 hle
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hle
  -- facts about `W₁ω = wScaled ℓ (g₀ω)`
  obtain ⟨hW2I, hW20, hW2le0, _⟩ := w1omegaFun_facts (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁)
    (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hW2le : ∀ᵐ x : E3, Work.BoseFixR.W1omegaFun v h ℓ x ≤ (1 + δ) * g x := by
    filter_upwards [hW2le0] with x hx
    rw [hδeq]
    simpa [hgdef] using hx
  -- the two instantiations of the a.e.-slice-bound engine
  have hres1 := coulInt_integrable_of_le (g := g) (A := Work.BoseFixR.W1fun v h ℓ)
    (c := 1 + δ) (κ := 8 * Real.pi) h1δ0 (by positivity) hgI hg0 hW1I hW10 hW1le hslice
  have hres2 := coulInt_integrable_of_le (g := g) (A := Work.BoseFixR.W1omegaFun v h ℓ)
    (c := 1 + δ) (κ := 8 * Real.pi) h1δ0 (by positivity) hgI hg0 hW2I hW20 hW2le hslice
  -- the numeric conclusion `(1+δ)²·8π·∫g₀ = (1+δ)²·64π²(a v) ≤ 256π²(a v)`
  have key : ∀ A : E3 → ℝ,
      (∫ p, Work.BoseBoxFock.coulInt A p) ≤ (1 + δ) ^ 2 * (8 * Real.pi) * (∫ x, g x) →
      (∫ p, Work.BoseBoxFock.coulInt A p) ≤ 256 * Real.pi ^ 2 * _root_.BoseGases.a v := by
    intro A hA
    have hpos : (0 : ℝ) ≤ 8 * Real.pi * (∫ x, g x) :=
      mul_nonneg (by positivity) hgnn
    have hle : (1 + δ) ^ 2 * (8 * Real.pi * (∫ x, g x))
        ≤ 4 * (8 * Real.pi * (∫ x, g x)) :=
      mul_le_mul_of_nonneg_right h1δsq hpos
    calc (∫ p, Work.BoseBoxFock.coulInt A p)
        ≤ (1 + δ) ^ 2 * (8 * Real.pi) * (∫ x, g x) := hA
      _ = (1 + δ) ^ 2 * (8 * Real.pi * (∫ x, g x)) := by ring
      _ ≤ 4 * (8 * Real.pi * (∫ x, g x)) := hle
      _ = 4 * (8 * Real.pi * (8 * Real.pi * _root_.BoseGases.a v)) := by rw [hgm]
      _ = 256 * Real.pi ^ 2 * _root_.BoseGases.a v := by ring
  exact ⟨hres1.1, key _ hres1.2, hres2.1, key _ hres2.2⟩

end Work.BoseBoxFock.L1Tails
