import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Spaces.Linf_H2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces

/-- **Pointwise bound from the `ℋ²` norm** (the paper's `Linf_H2` corollary, in the pointwise form
needed by the compactness step): at every point of the closed quadrant,
`(f z θ)^2 ≤ 100/(γ-1) * |f|²_{ℋ²}`, for `0 < α ≤ 1`, `f` smooth on a neighbourhood of the closed
quadrant, vanishing on the angular boundaries, with radial decay at `∞` and in `ℋ²`.

The proof is literally the interior estimate established inside `Work.Spaces.Linf_H2`
(the local lemma `hpoint` there), whose final step only passes from the pointwise bound to `supAbs`;
here that final step is omitted.  (The bound is the reason a uniform `ℋ²`-bound gives pointwise
compactness.) -/
theorem sq_le_HkSq_two {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.Spaces.SmoothNbhd f) (hv : Work.Spaces.VanishTheta f)
    (hd : Work.Spaces.DecayInZ 2 f) (hm : Work.Spaces.HkMem α 2 f)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (f z θ) ^ 2 ≤ 100 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 2 f := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 f z σ) Iz := hm.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 f z σ) Iz :=
    hPhi_int.const_mul _
  have hAES : AEStronglyMeasurable
      (fun z' => (Dz f z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
    have h1 : Measurable (fun z' => pz f z' θ) := by
      simpa [pz] using measurable_deriv (fun z'' => f z'' θ)
    have hD : Measurable (fun z' => Dz f z' θ) := measurable_id.mul h1
    have h2 : Measurable (fun z' => (Dz f z' θ) ^ 2) := by
      have : Measurable (fun z' => Dz f z' θ * Dz f z' θ) := hD.mul hD
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
  have hFint : IntegrableOn (fun z' => (Dz f z' θ) ^ 2 * (w z') ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono' hbnd hAES ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
      have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 f hsm hv hm z' hz' θ hθ
      have hFnn : 0 ≤ (Dz f z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
      exact hstep)
  have hHZ : (f z θ) ^ 2 ≤ ∫ z' in Iz, (Dz f z' θ) ^ 2 * (w z') ^ 2 :=
    HardyZ f θ hsm hθ (by simpa using hd 0 0 (by norm_num) θ hθ) hFint z hz
  have hIntLe : ∫ z' in Iz, (Dz f z' θ) ^ 2 * (w z') ^ 2
      ≤ (100 / (gam α - 1)) * HkSq α 2 f := by
    calc ∫ z' in Iz, (Dz f z' θ) ^ 2 * (w z') ^ 2
        ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 f z' σ :=
          MeasureTheory.setIntegral_mono_of_nonneg
            (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 f hsm hv hm z' hz' θ hθ)
            hbnd
      _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 f z' σ := by
          rw [MeasureTheory.integral_const_mul]
      _ = (100 / (gam α - 1)) * HkSq α 2 f := rfl
  exact le_trans hHZ hIntLe

end Work.FTS.Galerkin.Hilbert
