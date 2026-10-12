import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.q3kinMomFormLeGapBare`

The large-momentum kinetic word `momForm ℓ d u ψ` is dominated by the bare mean-free box mass
`gapBare ℓ u ψ = ∫_{Λ(u)}(Q_uψ)²`, with **only continuity** of `ψ` assumed (the corpus parent
`Work.BoseKinLoc.Kinetic.momForm_le_box` asks for `ContDiff ℝ ⊤ ψ` and `HasCompactSupport ψ`,
but its proof never uses either: the only place smoothness enters is the `L¹ ∩ L²` statement
`boxState_memLp`, whose proof uses `hψ.continuous` alone).

The argument is the (c1)-side "cheap half" of the sliding momentum localisation:

* `momForm` is definitionally `(2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (boxState ℓ u ψ) p‖²`
  (`Work.BoseKinLoc.Kinetic.momForm_eq_boxState`), with `boxState ℓ u ψ` the complexified
  localised mean-free state `1_{Λ(u)}(ψ − m_u)`;
* the cut-off is `0 ≤ momProj ℓ d ≤ 1`, so it can be discarded
  (`integral_mono_of_nonneg`);
* `boxState ℓ u ψ ∈ L¹ ∩ L²` for continuous `ψ` (proved below as
  `boxState_memLp_of_continuous`, by copying the proof of
  `Work.BoseKinLoc.Kinetic.boxState_memLp` and replacing `hψ.continuous` for `hψ`), so
  Plancherel in the `p`-convention (`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`) gives
  `(2π)⁻³ ∫_p ‖kinFT (boxState ℓ u ψ) p‖² = ∫_x ‖boxState ℓ u ψ x‖²`;
* the latter is `∫_{Λ(u)}(Q_uψ)² = gapBare ℓ u ψ` (`integral_boxState_normSq`).

Note `d` is completely arbitrary (even `d ≤ 0`); the cut-off is thrown away.
-/

noncomputable section

namespace Work.BoseBox

open MeasureTheory Filter

/-- **`L¹ ∩ L²` for the localised box state of a merely continuous state.**  The complexified
mean-free localised state `1_{Λ(u)}(ψ − m_u)` is supported in the compact moving box
`Λ(u) = lamBox ℓ u`, where the continuous `Q_uψ = ψ − m_u` is bounded; hence it lies in both
`L¹` and `L²`.  This is `Work.BoseKinLoc.Kinetic.boxState_memLp` with the unnecessarily strong
hypothesis `ContDiff ℝ ⊤ ψ` weakened to `Continuous ψ` (the proof of the parent uses only
continuity). -/
theorem boxState_memLp_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    MeasureTheory.MemLp (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) 1 MeasureTheory.volume
      ∧ MeasureTheory.MemLp (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) 2 MeasureTheory.volume := by
  have hbox_meas : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) :=
    Work.BoseKinLoc.Kinetic.lamBox_measurable ℓ u
  have hcomp : IsCompact (Work.BoseKinLoc.lamBox ℓ u) :=
    Work.BoseKinLoc.Kinetic.lamBox_compact hℓ u
  have hvol : volume (Work.BoseKinLoc.lamBox ℓ u) ≠ ⊤ :=
    Work.BoseKinLoc.Kinetic.lamBox_measure_ne_top hℓ u
  have hQc : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) :=
    Work.BoseKinLoc.Kinetic.Qfree_continuous hψ ℓ u
  -- the mean-free state is bounded on the compact moving box
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hQc.continuousOn
  have hM0 : 0 ≤ max C 0 := le_max_right _ _
  have hC' : ∀ x ∈ Work.BoseKinLoc.lamBox ℓ u,
      ‖Work.BoseKinLoc.Qfree ℓ u ψ x‖ ≤ max C 0 :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  -- the box state is the (complexified) mean-free state, cut off to the box
  have hfun : Work.BoseKinLoc.Kinetic.boxState ℓ u ψ
      = (Work.BoseKinLoc.lamBox ℓ u).indicator
          (fun z => ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) := by
    funext z
    by_cases hz : z ∈ Work.BoseKinLoc.lamBox ℓ u <;>
      simp [Work.BoseKinLoc.Kinetic.boxState, Work.BoseKinLoc.indU, hz]
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

theorem q3kinMomFormLeGapBare {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.momForm ℓ d u ψ ≤ Work.BoseKinLoc.gapBare ℓ u ψ := by
  -- the localised mean-free state is in `L¹ ∩ L²`
  obtain ⟨hF1, hF2⟩ := boxState_memLp_of_continuous (ℓ := ℓ) hℓ u hψ
  -- Plancherel for the `p`-convention transform, plus integrability of the energy density
  obtain ⟨hInt, hPlanch⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (F := Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) hF1 hF2
  -- discarding the cut-off `momProj ≤ 1`
  have hmono : ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun p =>
        mul_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))
      hInt
      (Eventually.of_forall fun p =>
        mul_le_of_le_one_left (sq_nonneg _) (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p))
  rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ∫ x : EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseKinLoc.Kinetic.boxState ℓ u ψ x‖ ^ 2 := hPlanch
    _ = Work.BoseKinLoc.gapBare ℓ u ψ := by
        rw [Work.BoseKinLoc.Kinetic.integral_boxState_normSq]
        rfl

end Work.BoseBox
