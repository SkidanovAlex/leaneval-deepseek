import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.integralAddLe` — additivity for nonnegative integrands

Mathlib's `MeasureTheory.integral_add` needs *integrability* of both summands.  The chain of
`Work.BoseFixB1B.pairingRungBox` has to split a nonnegative integrand `(X + Y)·PGen` into its two
nonnegative halves without knowing either is integrable (the Bochner integral of a non-integrable
nonnegative function is the junk value `0`, which would break the inequality).  The correct tool is
the `lintegral` route: `∫⁻` is *unconditionally* additive on measurable nonnegative functions, and
`ENNReal.toReal` is subadditive (`ENNReal.toReal_add_le`).

    ∫ x, (f x + g x) ∂μ ≤ (∫ x, f x ∂μ) + ∫ x, g x ∂μ

for `0 ≤ᵐ f`, `0 ≤ᵐ g` and `f, g` a.e. strongly measurable — no integrability anywhere.  The
`⊤`-case is separated out: if `∫⁻ f = ⊤` then `f ≤ f + g` forces `∫⁻ (f + g) = ⊤`, and both
`.toReal` values are `0`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1B.pairRung

/-- **Additivity of the Bochner integral on nonnegative integrands**, without integrability. -/
theorem integral_add_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ) :
    ∫ x, (f x + g x) ∂μ ≤ (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  have hfg : 0 ≤ᵐ[μ] fun x => f x + g x :=
    (hf.and hg).mono fun x hx => add_nonneg hx.1 hx.2
  rw [integral_eq_lintegral_of_nonneg_ae hfg (hfm.add hgm),
    integral_eq_lintegral_of_nonneg_ae hf hfm,
    integral_eq_lintegral_of_nonneg_ae hg hgm]
  have hpt : ∀ᵐ x ∂μ,
      ENNReal.ofReal (f x + g x) ≤ ENNReal.ofReal (f x) + ENNReal.ofReal (g x) :=
    (hf.and hg).mono fun x hx => le_of_eq (ENNReal.ofReal_add hx.1 hx.2)
  have hle : (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ)
      ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (g x) ∂μ) := by
    calc (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ)
        ≤ ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (g x)) ∂μ := lintegral_mono_ae hpt
      _ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (g x) ∂μ) :=
          lintegral_add_left'
            (ENNReal.measurable_ofReal.comp_aemeasurable hfm.aemeasurable) _
  by_cases hc : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ⊤
  · have hone : (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ) = ⊤ := by
      rcases ENNReal.add_eq_top.mp hc with h | h
      · exact top_le_iff.mp (h ▸ lintegral_mono_ae ((hf.and hg).mono fun x hx =>
          ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hx.2)))
      · exact top_le_iff.mp (h ▸ lintegral_mono_ae ((hf.and hg).mono fun x hx =>
          ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hx.1)))
    rw [hone]
    simp only [ENNReal.toReal_top]
    positivity
  · calc (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ).toReal
        ≤ ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) + (∫⁻ x, ENNReal.ofReal (g x) ∂μ)).toReal :=
          ENNReal.toReal_mono hc hle
      _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal
            + (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal := ENNReal.toReal_add_le

end Work.BoseFixB1B.pairRung
