import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-- Tonelli/Fubini for a real-valued, a.e. nonnegative function on a product of s-finite
measures whose fibres are a.e. integrable: the Bochner integral over the product equals the
iterated Bochner integral. (No integrability of `f` on the product is assumed: when the
product integral is infinite both sides are junk-zero, and the a.e. integrability of the
fibres is exactly what is needed to identify the two.) -/
theorem integral_prod_eq_iterated_of_ae_fibre_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    {f : α × β → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f (μ.prod ν))
    (hnn : 0 ≤ᵐ[μ.prod ν] f)
    (hfib : ∀ᵐ x ∂μ, MeasureTheory.Integrable (fun y => f (x, y)) ν) :
    ∫ p, f p ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  -- a.e. nonnegativity of the fibres, obtained from the a.e. nonnegativity on the product
  have hnn_fib : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, 0 ≤ f (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hnn
  -- a.e. finiteness of the inner lintegral of `f`, from integrability of the fibres
  have hfin : ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν) < ⊤ := by
    filter_upwards [hfib] with x hx
    exact hx.lintegral_lt_top
  -- the outer Bochner integrand is a.e. strongly measurable
  have hG_meas : MeasureTheory.AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
    hf.integral_prod_right'
  -- a.e. it agrees with the `toReal` of the inner lintegral
  have hG_eq : (fun x => ∫ y, f (x, y) ∂ν) =ᵐ[μ]
      fun x => (∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν).toReal := by
    filter_upwards [hfib, hnn_fib] with x hxint hxnn
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hxnn hxint.aestronglyMeasurable
  -- hence it is a.e. nonnegative
  have hG_nn : 0 ≤ᵐ[μ] fun x => ∫ y, f (x, y) ∂ν := by
    filter_upwards [hG_eq] with x hx
    rw [hx]
    exact ENNReal.toReal_nonneg
  -- and `ofReal` of it agrees a.e. with the inner lintegral
  have hkey : (fun x => ENNReal.ofReal (∫ y, f (x, y) ∂ν)) =ᵐ[μ]
      fun x => ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν := by
    filter_upwards [hG_eq, hfin] with x hx hxfin
    rw [hx, ENNReal.ofReal_toReal (ne_of_lt hxfin)]
  -- Tonelli
  have hton : ∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν)
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν ∂μ :=
    MeasureTheory.lintegral_prod _
      (ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable)
  calc ∫ p, f p ∂(μ.prod ν)
      = (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hf
    _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν ∂μ).toReal := by rw [hton]
    _ = (∫⁻ x, ENNReal.ofReal (∫ y, f (x, y) ∂ν) ∂μ).toReal := by
        rw [← MeasureTheory.lintegral_congr_ae hkey]
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
        (MeasureTheory.integral_eq_lintegral_of_nonneg_ae hG_nn hG_meas).symm

end Work.BoseFixB1B
