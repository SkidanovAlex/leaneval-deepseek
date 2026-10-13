import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Tools.PtBdDefs` — the pointwise master-bound vocabulary and integral helpers

* `PtBdDth α` / `PtBdDz α` are the pointwise level-`6` master bounds of
  `Tools/ptBoundDth.lean` / `Tools/ptBoundDz.lean`;
* `ae_mem_Ioo_Iθ_fts`, `ae_mem_Ioi_Iz_fts`, `integral_add_three`, `integral_add_three_z`,
  `ten_le_inv_gam_sub_one` are the elementary integration helpers used by
  `Tools/shiftProdDth.lean` and `Tools/shiftProdDz.lean`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- The pointwise master bound for `A · D_θ f` (the content of `Tools/ptBoundDth.lean`). -/
def PtBdDth (α : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
              * Work.Spaces.Wt α z θ) ^ 2

/-- The pointwise master bound for `A · D_z f` (the content of `Tools/ptBoundDz.lean`). -/
def PtBdDz (α : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2

/-- Almost every angle of `Iθ` is interior. -/
theorem ae_mem_Ioo_Iθ_fts : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := (0 : ℝ))
    (b := Real.pi / 2))
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h

/-- Almost every radius of `Iz` is positive. -/
theorem ae_mem_Ioi_Iz_fts : ∀ᵐ z ∂(volume.restrict Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
  rwa [Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h

/-- Linearity of the integral over a sum of three functions (`Iθ`). -/
theorem integral_add_three {f g h : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Iθ)) (hg : Integrable g (volume.restrict Iθ))
    (hh : Integrable h (volume.restrict Iθ)) :
    (∫ x in Iθ, (f x + g x + h x)) = (∫ x in Iθ, f x) + (∫ x in Iθ, g x)
      + (∫ x in Iθ, h x) := by
  have h2 : (∫ x in Iθ, (f x + g x) + h x) = (∫ x in Iθ, f x + g x)
      + (∫ x in Iθ, h x) := MeasureTheory.integral_add (hf.add hg) hh
  have h1 : (∫ x in Iθ, f x + g x) = (∫ x in Iθ, f x) + (∫ x in Iθ, g x) :=
    MeasureTheory.integral_add hf hg
  rw [h2, h1]

/-- Linearity of the integral over a sum of three functions (`Iz`). -/
theorem integral_add_three_z {f g h : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Iz)) (hg : Integrable g (volume.restrict Iz))
    (hh : Integrable h (volume.restrict Iz)) :
    (∫ x in Iz, (f x + g x + h x)) = (∫ x in Iz, f x) + (∫ x in Iz, g x)
      + (∫ x in Iz, h x) := by
  have h2 : (∫ x in Iz, (f x + g x) + h x) = (∫ x in Iz, f x + g x)
      + (∫ x in Iz, h x) := MeasureTheory.integral_add (hf.add hg) hh
  have h1 : (∫ x in Iz, f x + g x) = (∫ x in Iz, f x) + (∫ x in Iz, g x) :=
    MeasureTheory.integral_add hf hg
  rw [h2, h1]

/-- `(γ-1)⁻¹ ≥ 10` for `0 < α ≤ 1`. -/
theorem ten_le_inv_gam_sub_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (10 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := by
  have hsub : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hp : (0 : ℝ) < α / 10 := by linarith
  have hle : α / 10 ≤ 1 / 10 := by linarith
  have h := (inv_le_inv₀ (show (0 : ℝ) < 1 / 10 by norm_num) hp).mpr hle
  rw [show ((1 : ℝ) / 10)⁻¹ = 10 by norm_num] at h
  rwa [← hsub] at h

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
