import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Filter

theorem integrable_sq_mul_le_of_tendsto_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {g : α → ℝ} {B : ℝ} {φ : ℕ → ℕ} {u : α → ℝ}
    (hgpos : ∀ᵐ x ∂μ, 0 < g x) (hgmeas : AEMeasurable g μ)
    (hvmeas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hint : ∀ n, Integrable (fun x => (v n x) ^ 2 * g x) μ)
    (hb : ∀ n, (∫ x, (v n x) ^ 2 * g x ∂μ) ≤ B)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => v (φ k) x) Filter.atTop (nhds (u x))) :
    Integrable (fun x => (u x) ^ 2 * g x) μ ∧
      (∫ x, (u x) ^ 2 * g x ∂μ) ≤ B := by
  -- The weight is nonnegative a.e., hence so is every integrand.
  have hg_nonneg : 0 ≤ᵐ[μ] g := hgpos.mono fun x hx => hx.le
  have hnn : ∀ k, 0 ≤ᵐ[μ] fun x => (v (φ k) x) ^ 2 * g x :=
    fun k => hg_nonneg.mono fun x hx => mul_nonneg (sq_nonneg _) hx
  -- The limit of the squared functions is measurable, being an a.e. sequential limit.
  have hmeas_v : ∀ k, AEStronglyMeasurable (fun x => (v (φ k) x) ^ 2 * g x) μ :=
    fun k => ((hvmeas (φ k)).pow 2).mul hgmeas.aestronglyMeasurable
  have hae : ∀ᵐ x ∂μ, Tendsto (fun k => (v (φ k) x) ^ 2 * g x) atTop (nhds ((u x) ^ 2 * g x)) :=
    hlim.mono fun x hx => (hx.pow 2).mul_const (g x)
  have hsm : AEStronglyMeasurable (fun x => (u x) ^ 2 * g x) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas_v hae
  -- Bochner integrals of the nonnegative members are the corresponding `lintegral`s.
  have hlin : ∀ k, ENNReal.ofReal (∫ x, (v (φ k) x) ^ 2 * g x ∂μ)
      = ∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ :=
    fun k => ofReal_integral_eq_lintegral_ofReal (hint (φ k)) (hnn k)
  have hbnd : ∀ k, (∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ) ≤ ENNReal.ofReal B := by
    intro k
    rw [← hlin k]
    exact ENNReal.ofReal_le_ofReal (hb (φ k))
  -- Fatou's lemma along the subsequence `φ`.
  have hfat := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun k x => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x))
    (fun k => (hmeas_v k).aemeasurable.ennreal_ofReal)
  have hliminf_eq : ∀ᵐ x ∂μ,
      liminf (fun k => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) atTop
        = ENNReal.ofReal ((u x) ^ 2 * g x) :=
    hae.mono fun x hx => (ENNReal.tendsto_ofReal hx).liminf_eq
  have key : ∫⁻ x, ENNReal.ofReal ((u x) ^ 2 * g x) ∂μ ≤ ENNReal.ofReal B := by
    calc ∫⁻ x, ENNReal.ofReal ((u x) ^ 2 * g x) ∂μ
        = ∫⁻ x, liminf (fun k => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) atTop ∂μ :=
          (lintegral_congr_ae hliminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ) atTop := hfat
      _ ≤ ENNReal.ofReal B := by
          rw [Filter.liminf_eq_iSup_iInf_of_nat]
          refine iSup_le fun n => le_trans ?_ (hbnd n)
          exact le_trans (iInf_le _ n) (iInf_le _ le_rfl)
  -- Finiteness of the `lintegral` gives integrability.
  have hfin : HasFiniteIntegral (fun x => (u x) ^ 2 * g x) μ := by
    rw [hasFiniteIntegral_iff_ofReal (hg_nonneg.mono fun x hx => mul_nonneg (sq_nonneg _) hx)]
    exact lt_of_le_of_lt key ENNReal.ofReal_lt_top
  refine ⟨⟨hsm, hfin⟩, ?_⟩
  -- Finally convert the `lintegral` bound back to a Bochner integral bound.
  have hB : 0 ≤ B := le_trans (integral_nonneg_of_ae (hnn 0)) (hb (φ 0))
  rw [integral_eq_lintegral_of_nonneg_ae
    (hg_nonneg.mono fun x hx => mul_nonneg (sq_nonneg _) hx) hsm]
  calc (∫⁻ x, ENNReal.ofReal ((u x) ^ 2 * g x) ∂μ).toReal
      ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = B := ENNReal.toReal_ofReal hB

end Work.FTS.PhiStar.Honesty.SlotsLimit
