import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS_RegExport.RXA1w.AgmonZ
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The a.e. weighted slice bound

`mixed_slice_pointwise_le`: for `a + b ≤ 2` and `z > 0`,

  `sin(2σ)^{-γ} (D_z^bD_θ^{a+1}f(z,σ))² ≤ 5 z³/(1+z)⁴ · ∫_s HkIntegrand β 4 f s σ`  a.e. in `σ`.

This is the weighted radial Agmon inequality `agmonZ_weight` applied to the radial slice
`s ↦ D_z^bD_θ^{a+1}f(s,σ)`, whose two Agmon integrals are dominated by the `ℋ⁴`-integrand
through `mixed_slot_sq_w_le_HkIntegrand`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- `(1+z)⁴/z³ = w(z)² · z`. -/
private lemma w_sq_mul_eq {z : ℝ} : (1 + z) ^ 4 / z ^ 3 = (Work.Spaces.w z) ^ 2 * z := by
  rw [Work.Spaces.w, div_pow]
  field_simp

theorem mixed_slice_pointwise_le {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ} (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
  filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem b (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem (b + 1) (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_HkIntegrand_slice_C4 h4 hmem,
    Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hIntA hIntB hIntHk hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hint1 : MeasureTheory.IntegrableOn
      (fun x => (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz :=
    hIntA.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2
      rw [mul_pow])
  have hint2 : MeasureTheory.IntegrableOn
      (fun x => (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
        * Work.Spaces.w x) ^ 2) Work.Spaces.Iz :=
    hIntB.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
      rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
          = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl, mul_pow])
  have hdec : Filter.Tendsto
      (fun x => x * (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      Filter.atTop (𝓝 0) := ((htr (a + 1) b (by omega)).1 σ hσ).2
  have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.mixed b (a + 1) f s σ) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hσ
      (contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 1 (by omega))
  have hvderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => Work.Spaces.mixed b (a + 1) f s σ)
        (deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x) x := by
    intro x hx
    exact ((hcd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hagmon := agmonZ_weight hz hvderiv hint1 hint2 hdec
  have hagmon' : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 4 * (∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
          + ∫ x in Work.Spaces.Iz,
              (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
                * Work.Spaces.w x) ^ 2 := hagmon
  have hA_le : (∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        mixed_slot_sq_w_le_HkIntegrand (f := f) hβ b (a + 1) (by omega) (by omega) x hσ)
  have hB_le : (∫ x in Work.Spaces.Iz,
        (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    have heq : (∫ x in Work.Spaces.Iz,
          (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            * Work.Spaces.w x) ^ 2)
        = ∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2
        rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl])
    rw [heq, ← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        mixed_slot_sq_w_le_HkIntegrand (f := f) hβ (b + 1) (a + 1) (by omega) (by omega) x hσ)
  have hsum : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by
    refine le_trans hagmon' ?_
    have h5 : (4 : ℝ) * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
        + (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
        = 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by ring
    have := add_le_add (mul_le_mul_of_nonneg_left hA_le (by norm_num : (0 : ℝ) ≤ 4)) hB_le
    linarith [this, h5]
  have hρpos : 0 < (Work.Spaces.w z) ^ 2 * z := by
    have h1 := Work.FTS.H2.one_le_w_sq hz
    nlinarith [hz, h1]
  have hcancel : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β) = 1 := by
    rw [← Real.rpow_add hsin, show -(Work.Spaces.gam β) + Work.Spaces.gam β = 0 by ring,
      Real.rpow_zero]
  have hcount : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      / ((Work.Spaces.w z) ^ 2 * z) :=
    div_nonneg (Real.rpow_nonneg hsin.le _) hρpos.le
  have h2 := mul_le_mul_of_nonneg_left hsum hcount
  have hL : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * ((Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    have hwz : Work.Spaces.w z ≠ 0 := by
      intro h0; rw [h0] at hρpos; simp at hρpos
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp <;> try ring
  have hR : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
      = 5 * (z ^ 3 / (1 + z) ^ 4)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← w_sq_mul_eq]
    have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((1 + z) ^ 4 / z ^ 3)
        = z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by
      field_simp <;> try ring
    rw [h1]
    have h2 : z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
        = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
            * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
              * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)) := by ring
    rw [h2, hcancel, mul_one]
  rw [hL, hR] at h2
  exact h2

end Work.FTS_RegExport.RXA1w
