import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Linf_H2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ConstructionInstance

/-- **Pointwise `L^∞`(domain) bound for `H²` functions.**  This is the pointwise form of
`Work.Spaces.Linf_H2`: every value `g z θ` on the closed quadrant is bounded by
`100 / √(γ-1)` times the `H²`-norm.  The proof repeats the pointwise estimate
`(g z θ)² ≤ (100/(γ-1)) |g|²_{H²}` that `Linf_H2` establishes before passing to the
supremum, and then takes square roots. -/
theorem abs_le_of_linf_H2 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayInZ 2 g) (hmem : Work.Spaces.HkMem α 2 g) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 2 g := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz := hmem.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz :=
    hPhi_int.const_mul _
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (g z θ) ^ 2 ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
    intro z hz θ hθ
    have hAES : AEStronglyMeasurable
        (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
      have h1 : Measurable (fun z' => pz g z' θ) := by
        simpa [pz] using measurable_deriv (fun z'' => g z'' θ)
      have hD : Measurable (fun z' => Dz g z' θ) := measurable_id.mul h1
      have h2 : Measurable (fun z' => (Dz g z' θ) ^ 2) := by
        have : Measurable (fun z' => Dz g z' θ * Dz g z' θ) := hD.mul hD
        simpa [pow_two] using this
      have hw : Measurable w := by
        show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
        have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
          have h : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
            (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
          simpa [pow_two] using h
        have hden : Measurable (fun z : ℝ => z ^ 2) := by
          have h : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
          simpa [pow_two] using h
        exact hnum.div hden
      have hw2 : Measurable (fun z' => (w z') ^ 2) := by
        have : Measurable (fun z' => w z' * w z') := hw.mul hw
        simpa [pow_two] using this
      exact (h2.mul hw2).aestronglyMeasurable
    have hFint : IntegrableOn (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) Iz := by
      refine MeasureTheory.Integrable.mono' hbnd hAES ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
        have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ
        have hFnn : 0 ≤ (Dz g z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
        exact hstep)
    have hHZ : (g z θ) ^ 2 ≤ ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2 :=
      HardyZ g θ hsm hθ (by simpa using hdec 0 0 (by norm_num) θ hθ) hFint z hz
    have hIntLe : ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
        ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
      calc ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
          ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z' σ :=
            MeasureTheory.setIntegral_mono_of_nonneg
              (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ)
              hbnd
        _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 g z' σ := by
            rw [MeasureTheory.integral_const_mul]
        _ = (100 / (gam α - 1)) * HkSq α 2 g := rfl
    exact le_trans hHZ hIntLe
  have hAle : (100 / (gam α - 1)) * HkSq α 2 g
      ≤ (100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g := by
    rw [div_pow, Real.sq_sqrt hgam1.le]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num : (100 : ℝ) ≤ 100 ^ 2) hgam1.le)
      (HkSq_nonneg α 2 g)
  have hsqrt : Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
      ≤ (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := by
    calc Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
        ≤ Real.sqrt ((100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g) := Real.sqrt_le_sqrt hAle
      _ = (100 / Real.sqrt (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
          rw [Real.sqrt_mul (sq_nonneg _),
              Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
      _ = (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := rfl
  intro z θ hz hθ
  have hzIz : z ∈ Iz := by simpa [Iz] using hz
  exact le_trans (Real.abs_le_sqrt (hpoint z hzIz θ hθ)) hsqrt

end Work.ConstructionInstance
