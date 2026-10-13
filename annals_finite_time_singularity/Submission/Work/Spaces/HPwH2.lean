import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.Linf_H2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Elgindi, §H2: `H²` functions are pointwise bounded by `100/(γ-1)·|·|²_{H²}`.**
For `h` a smooth function on a neighbourhood of the closed quadrant, vanishing on the two
angular boundaries, decaying to `0` in `z` along each angle, and of class `H²`, every
pointwise value on the domain satisfies
`(h z θ)² ≤ (100/(γ-1)) · HkSq α 2 h`.

This is the pointwise form of the paper's Corollary *Linfty*: it combines the radial
Hardy inequality `HardyZ` with the angular Hardy inequality applied to `D_z h`
(`Dz_HardyTheta_HkIntegrand`), after which the surviving angular integral is a single
term of the `H²`-integrand. -/
theorem HPwH2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd h) (hvt : Work.Spaces.VanishTheta h)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0))
    (hmem : Work.Spaces.HkMem α 2 h) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (h z θ) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 2 h := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcoef : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hgam1.le
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 h z σ) Iz := hmem.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 h z σ) Iz :=
    hPhi_int.const_mul _
  intro z hz θ hθ
  have hAES : AEStronglyMeasurable
      (fun z' => (Dz h z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
    have h1 : Measurable (fun z' => pz h z' θ) := by
      simpa [pz] using measurable_deriv (fun z'' => h z'' θ)
    have hD : Measurable (fun z' => Dz h z' θ) := measurable_id.mul h1
    have h2 : Measurable (fun z' => (Dz h z' θ) ^ 2) := by
      have : Measurable (fun z' => Dz h z' θ * Dz h z' θ) := hD.mul hD
      simpa [pow_two] using this
    have hw : Measurable w := by
      show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
      have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
        have hm : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
          (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
        simpa [pow_two] using hm
      have hden : Measurable (fun z : ℝ => z ^ 2) := by
        have hm : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
        simpa [pow_two] using hm
      exact hnum.div hden
    have hw2 : Measurable (fun z' => (w z') ^ 2) := by
      have : Measurable (fun z' => w z' * w z') := hw.mul hw
      simpa [pow_two] using this
    exact (h2.mul hw2).aestronglyMeasurable
  have hFint : IntegrableOn (fun z' => (Dz h z' θ) ^ 2 * (w z') ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono' hbnd hAES ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
      have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 h hsm hvt hmem z' hz' θ hθ
      have hFnn : 0 ≤ (Dz h z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
      exact hstep)
  have hHZ : (h z θ) ^ 2 ≤ ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2 :=
    HardyZ h θ hsm hθ (hdec θ hθ) hFint z hz
  have hIntLe : ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2
      ≤ (100 / (gam α - 1)) * HkSq α 2 h := by
    calc ∫ z' in Iz, (Dz h z' θ) ^ 2 * (w z') ^ 2
        ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 h z' σ :=
          MeasureTheory.setIntegral_mono_of_nonneg
            (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 h hsm hvt hmem z' hz' θ hθ)
            hbnd
      _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 h z' σ := by
          rw [MeasureTheory.integral_const_mul]
      _ = (100 / (gam α - 1)) * HkSq α 2 h := rfl
  exact le_trans hHZ hIntLe

end Work.Spaces
