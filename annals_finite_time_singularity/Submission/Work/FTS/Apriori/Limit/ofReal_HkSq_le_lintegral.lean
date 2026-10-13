/-
# `ofReal_HkSq_le_lintegral` — `HkSq` is dominated by the `lintegral` of the integrand

The `ℋ⁴`-energy `Work.Spaces.HkSq α 4 f` is the *iterated Bochner* integral of the
nonnegative integrand `Work.Spaces.HkIntegrand α 4 f` over `Iz × Iθ`, while the right-hand
side of the lower semicontinuity argument is the *`lintegral`* of `ofReal` of the same
integrand with respect to the product measure `Qμ = (volume.restrict Iz).prod (volume.restrict
Iθ)`.

`ofReal_HkSq_le_lintegral` compares the two.  The point is that nothing is assumed about
integrability: for a non-integrable function Lean's Bochner integral is `0`
(`MeasureTheory.integral_undef`), so `ofReal` of the iterated Bochner integral is *bounded*
by the `lintegral` in all cases.  Concretely, with `g = HkIntegrand α 4 f ≥ 0`,

* `ofReal (∫_z ∫_θ g) ≤ ∫⁻_z ofReal (∫_θ g)`  (set-integral version of the comparison,
  applied on `Iz`; needs `0 ≤ ∫_θ g`, which holds pointwise since `g ≥ 0`);
* `ofReal (∫_θ g z θ) ≤ ∫⁻_θ ofReal (g z θ)` for every `z` (same comparison on `Iθ`);
* `∫⁻_z ∫⁻_θ ofReal (g z θ) = ∫⁻_{(z,θ)} ofReal (g z θ)`, Tonelli for the product measure,
  which is where the hypothesis `SmoothQuad f` enters: it makes the uncurried integrand
  continuous on the open quadrant (`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`),
  hence a.e. strongly measurable for `Qμ` (`Work.Spaces.aesm_of_continuousOn_Qd`), the
  complement of the open quadrant in `Iz ×ˢ Iθ` being null.

No new hypothesis beyond `SmoothQuad` is needed, and no integrability of `g` is required.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

/-- **`ofReal` of a Bochner integral is bounded by the `lintegral` of `ofReal`.**  For a
nonnegative function on a measurable set the comparison holds unconditionally: if the function
is not integrable the Bochner integral is `0` (`MeasureTheory.integral_undef`), and
`0 ≤ ∫⁻ x in s, ofReal (F x)`. -/
theorem ofReal_setIntegral_le_lintegral {s : Set ℝ} (hs : MeasurableSet s) {F : ℝ → ℝ}
    (hF : ∀ x ∈ s, 0 ≤ F x) :
    ENNReal.ofReal (∫ x in s, F x) ≤ ∫⁻ x in s, ENNReal.ofReal (F x) := by
  by_cases h : Integrable F (volume.restrict s)
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h
      (MeasureTheory.ae_restrict_of_forall_mem hs hF)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

theorem ofReal_HkSq_le_lintegral {α : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) :
    ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      ≤ MeasureTheory.lintegral Work.FTS.Apriori.Limit.Qμ
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) := by
  -- The integrand is a sum of squares, hence nonnegative.
  have hg : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  -- `SmoothQuad` makes it continuous on the open quadrant, hence a.e. strongly measurable.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hf
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) Qμ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable
  -- Tonelli: the `lintegral` over the product measure is the iterated `lintegral`.
  have hton : MeasureTheory.lintegral Qμ
        (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) := by
    rw [show Qμ = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      from rfl]
    exact MeasureTheory.lintegral_prod _ hmeas
  calc ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := rfl
    _ ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
        ofReal_setIntegral_le_lintegral measurableSet_Ici
          (fun z _ => integral_nonneg fun θ => hg z θ)
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) :=
        lintegral_mono fun z =>
          ofReal_setIntegral_le_lintegral measurableSet_Icc (fun θ _ => hg z θ)
    _ = MeasureTheory.lintegral Qμ
          (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) :=
        hton.symm

end Work.FTS.Apriori.Limit
