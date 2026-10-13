import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sigmaCritWeight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hardyAngL2Integrable` — `L²`-integrability of the critical angular Hardy slot

For `α ∈ (0,1]` and `h` of class `C¹` on `(0,π/2)` whose `sin(2·)`-weighted squared derivative
is integrable against the super-critical weight `sin(2θ)^{-γ}`, `γ = 1 + α/10`, the function
`h² sin(2θ)^{-(1-α/10)}` is integrable on `Iθ = [0,π/2]`.

This is the *integrability* half of the two-weight Hardy inequality `thetaHardyA`; the route here
avoids the (delicate) endpoint analysis of that file by using the *pointwise* Hardy bound
`slicePtBound`: it dominates `h θ²` by a constant `K` on the open interval, so the integrand is
dominated a.e. by `K · sin(2θ)^{α/10-1}`, which is integrable on `Iθ` because its exponent is
`> -1` (`integrableOn_sin_two_rpow`), the two endpoints being of measure zero.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open MeasureTheory Set
open scoped Real Topology

/-- `Ioo 0 (π/2)` carries the same restricted measure as `Iθ = Icc 0 (π/2)`. -/
private theorem restrict_Ioo_eq_Iθ_t6 :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))

/-- A function continuous on the open interval is a.e. strongly measurable on `Iθ`. -/
private theorem aesm_slice_Iθ_t6 {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [← restrict_Ioo_eq_Iθ_t6]
  exact hf.aestronglyMeasurable measurableSet_Ioo

theorem hardyAngL2Integrable : ∀ α ∈ Set.Ioc 0 1, ∀ h : ℝ → ℝ,
    ContDiffOn ℝ 1 h (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ) * deriv h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 - α / 10))) Work.Spaces.Iθ := by
  intro α hα h hC1 hint
  obtain ⟨hα0, hα1⟩ := hα
  have hβ0 : (0 : ℝ) < α / 10 := by linarith
  have hβ1 : α / 10 ≤ 1 := by linarith
  -- on the open interval the two weights are the same, in the two-weight form
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sin (2 * θ) * deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.StrongPersist.N6Trans.SixRoute.sin_two_pos_of_lt_half hθ.1 hθ.2
    have hpow : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (1 - α / 10) := by
      have hγ : Work.Spaces.gam α = 1 + α / 10 := rfl
      rw [← Real.rpow_two, ← Real.rpow_add hs]
      congr 1
      rw [hγ]; ring
    calc (Real.sin (2 * θ) * deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (deriv h θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ = (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10) := by rw [hpow]
  have hintIoo : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ) * deriv h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hint.mono_set Set.Ioo_subset_Icc_self
  have hintS : MeasureTheory.IntegrableOn (fun θ => (deriv h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (1 - α / 10)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hintIoo.congr_fun (fun θ hθ => hpt θ hθ) measurableSet_Ioo
  -- the weight alone is integrable since `α/10 - 1 > -1`
  have hintB : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongPersist.N6Trans.SixRoute.integrableOn_sin_two_rpow (c := α / 10 - 1)
      (by linarith)
  -- the pointwise Hardy bound of `slicePtBound`
  have hb := Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound (β := α / 10) hβ0 hβ1 hC1
    hintS hintB
  set K : ℝ := 2 * h (Real.pi / 4) ^ 2
    + (2 * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - α / 10))
      * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (α / 10 - 1) with hK
  have hle : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (h θ) ^ 2 ≤ K := by
    intro θ hθ
    rw [hK]
    exact hb θ hθ
  -- hence the integrand is dominated a.e. by `K · sin(2θ)^{α/10-1}`
  have hdom : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))‖
        ≤ K * (Real.sin (2 * θ)) ^ (α / 10 - 1) := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.StrongPersist.N6Trans.SixRoute.sin_two_pos_of_lt_half hθ.1 hθ.2
    have hexp : -(1 - α / 10) = α / 10 - 1 := by ring
    rw [hexp]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))]
    exact mul_le_mul_of_nonneg_right (hle θ hθ) (Real.rpow_nonneg hs.le _)
  have hgd : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1))
      Work.Spaces.Iθ :=
    hintB.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2)).symm
  have hg : MeasureTheory.Integrable (fun θ => K * (Real.sin (2 * θ)) ^ (α / 10 - 1))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hgd.const_mul K
  have hcont : ContinuousOn (fun θ : ℝ => (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine (hC1.continuousOn.pow 2).mul ?_
    exact ((Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt
        (Work.FTS.StrongPersist.N6Trans.SixRoute.sin_two_pos_of_lt_half hθ.1 hθ.2))))
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := aesm_slice_Iθ_t6 hcont
  show MeasureTheory.Integrable (fun θ : ℝ => (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  exact MeasureTheory.Integrable.mono' hg haesm (by
    rw [← restrict_Ioo_eq_Iθ_t6]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hdom)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
