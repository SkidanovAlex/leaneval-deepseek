import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.boxState_memLp` — the box state lies in `L¹ ∩ L²`

FS's localised box state
`statU ℓ u ψ = 1_{Λ(u)} (ψ − m_u)` (the complexified product
`indU ℓ u · Qfree ℓ u ψ` of `Work.BoseKinLoc.Defs`) is supported in the moving box
`Λ(u) = lamBox ℓ u`, which is a translate of the centred cube `acube ℓ` — compact,
hence of finite volume.  On that (compact) box the smooth real state `ψ`, and
therefore the mean-free part `Qfree ℓ u ψ = ψ − m_u`, is bounded.  Consequently the
box state is bounded and supported in a finite-measure set, and so belongs to
`L¹(ℝ³)` and `L²(ℝ³)`.

This module records that fact, together with the two geometric inputs it rests on
(measurability and compactness of the moving box) and the continuity of `Qfree`.
-/

namespace Work.BoseKinLoc.Kinetic

open MeasureTheory

/-- The moving box `Λ(u) = lamBox ℓ u` is measurable. -/
lemma lamBox_measurable (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
  rw [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)

/-- The moving box `Λ(u) = lamBox ℓ u` is compact for `0 < ℓ` (it is a translate of the
centred cube `acube ℓ`). -/
lemma lamBox_compact {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    IsCompact (Work.BoseKinLoc.lamBox ℓ u) := by
  have heq : Work.BoseKinLoc.lamBox ℓ u
      = (fun x : EuclideanSpace ℝ (Fin 3) => ℓ • u + x) '' Submission.BoseGases.acube ℓ := by
    ext x
    simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, Set.mem_ofPred_eq,
      Set.mem_image, Submission.BoseGases.mem_acube_iff]
    constructor
    · intro hx
      exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  exact (Submission.BoseGases.acube_compact hℓ).image (by fun_prop)

/-- The moving box has finite volume. -/
lemma lamBox_measure_ne_top {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    volume (Work.BoseKinLoc.lamBox ℓ u) ≠ ⊤ :=
  (lamBox_compact hℓ u).measure_lt_top.ne

/-- The mean-free box projection `Q_uψ = ψ − m_u` of a continuous state is continuous. -/
lemma Qfree_continuous {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ)
    (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := by
  rw [show Work.BoseKinLoc.Qfree ℓ u ψ
      = fun x => ψ x - Work.BSKinetic.bsMean ℓ u ψ from rfl]
  exact hψ.sub continuous_const

theorem boxState_memLp {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    MeasureTheory.MemLp (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))
      1 MeasureTheory.volume
    ∧ MeasureTheory.MemLp (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))
      2 MeasureTheory.volume := by
  have hbox_meas : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := lamBox_measurable ℓ u
  have hcomp : IsCompact (Work.BoseKinLoc.lamBox ℓ u) := lamBox_compact hℓ u
  have hvol : volume (Work.BoseKinLoc.lamBox ℓ u) ≠ ⊤ := lamBox_measure_ne_top hℓ u
  have hQc : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := Qfree_continuous hψ.continuous ℓ u
  -- the mean-free state is bounded on the compact moving box
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hQc.continuousOn
  have hM0 : 0 ≤ max C 0 := le_max_right _ _
  have hC' : ∀ x ∈ Work.BoseKinLoc.lamBox ℓ u,
      ‖Work.BoseKinLoc.Qfree ℓ u ψ x‖ ≤ max C 0 :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  -- the box state is the (complexified) mean-free state, cut off to the box
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))
      = (Work.BoseKinLoc.lamBox ℓ u).indicator
          (fun z => ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) := by
    funext z
    by_cases hz : z ∈ Work.BoseKinLoc.lamBox ℓ u <;>
      simp [Work.BoseKinLoc.indU, hz]
  have haesm : AEStronglyMeasurable
      ((Work.BoseKinLoc.lamBox ℓ u).indicator
        (fun z => ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))) volume :=
    ((Complex.continuous_ofReal.comp hQc).aestronglyMeasurable).indicator hbox_meas
  -- and it is dominated by the (L^p) cut-off of the constant `max C 0`
  have hbound : ∀ᵐ z ∂volume,
      ‖(Work.BoseKinLoc.lamBox ℓ u).indicator
        (fun z => ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) z‖
      ≤ ‖(Work.BoseKinLoc.lamBox ℓ u).indicator
        (fun _ => ((max C 0 : ℝ) : ℂ)) z‖ := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z ∈ Work.BoseKinLoc.lamBox ℓ u
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      rw [show ‖((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)‖
            = ‖Work.BoseKinLoc.Qfree ℓ u ψ z‖ from by simp]
      rw [show ‖(((max C 0 : ℝ) : ℂ))‖ = ‖(max C 0 : ℝ)‖ from by simp]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM0]
      exact hC' z hz
    · simp [hz]
  constructor
  · rw [hfun]
    exact (memLp_indicator_const 1 hbox_meas ((max C 0 : ℝ) : ℂ) (Or.inr hvol)).mono
      haesm hbound
  · rw [hfun]
    exact (memLp_indicator_const 2 hbox_meas ((max C 0 : ℝ) : ℂ) (Or.inr hvol)).mono
      haesm hbound

end Work.BoseKinLoc.Kinetic
