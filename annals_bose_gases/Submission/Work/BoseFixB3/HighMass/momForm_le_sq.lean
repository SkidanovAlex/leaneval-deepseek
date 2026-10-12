import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.momForm_le_sq`

The large-momentum word `momForm ℓ d u ψ` of FS `eq:DefT`'s third term (with the cut-off
parameter `d`) is dominated by the *uncut* mean-free box mass `∫_{Λ(u)}(Q_uψ)²`, and at the
anchored box `u = 0` the latter is `∫_{acube ℓ}(bsQ ℓ 0 ψ)²`.

The point is that the momentum cut-off is a multiplication by `momProj ℓ d ∈ {0,1}`, hence
`≤ 1` pointwise, so it can simply be discarded; the resulting uncut momentum integral is the
`L²`-mass of the localised mean-free state, by the `p`-convention Plancherel identity
`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`.

Unlike `Work.BoseKinLoc.Kinetic.momForm_le_box` (which asks `ψ` to be smooth and compactly
supported, the class for which `boxState_memLp` was set up), the statement below only
assumes `ψ` continuous.  The `L¹ ∩ L²` membership of the localised state is *automatic* for
continuous `ψ`: the state is supported in the compact box `Λ(u) = ℓu + acube ℓ`, where the
mean-free part `Q_uψ` is bounded.  `boxState_memLp_of_continuous` records that, by the same
argument as `boxState_memLp` (the `ContDiff` hypothesis there is only ever used through
`ContDiff.continuous`).

Note that no sign hypothesis on `d` is needed: `momProj ℓ d p = 1_{(d²ℓ)⁻¹ < ‖p‖}` is
`≤ 1` for *every* real `d` (in particular `d = 0`, where `(d²ℓ)⁻¹ = 0` and the cut-off only
removes the measure-zero set `{p = 0}`), and `d < 0` gives the same indicator as `|d|`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.HighMass

open Work.BoseKinLoc

/-- The localised mean-free box state `boxState ℓ u ψ = 1_{Λ(u)}·(ψ − m_u)` lies in
`L¹ ∩ L²` as soon as `ψ` is continuous (and `0 < ℓ`): it is supported in the compact box
`Λ(u)`, on which the continuous mean-free part is bounded.

This is `Work.BoseKinLoc.Kinetic.boxState_memLp` with the smoothness hypothesis weakened from
`ContDiff ℝ ⊤ ψ` to `Continuous ψ` (its proof only uses the latter). -/
lemma boxState_memLp_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
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
  -- and it is dominated by the `L^p` cut-off of the constant `max C 0`
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

/-- The anchored moving box `Λ(0)` is the centred cube `acube ℓ`. -/
lemma lamBox_zero_eq_acube (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- **The momentum cut-off is free at `u = 0`.**  For every `0 < ℓ`, every real `d` and every
continuous `ψ`,

    `momForm ℓ d 0 ψ ≤ ∫_{acube ℓ}(Q_0ψ)²`.

The cut-off `momProj ℓ d` is a `{0,1}`-valued multiplier, hence `≤ 1`, so dropping it costs
nothing; the resulting uncut momentum integral is the `L²`-mass of the localised mean-free
state `1_{acube ℓ}(ψ − m_0)`, by Plancherel. -/
theorem momForm_le_sq {ℓ d : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.momForm ℓ d 0 ψ
      ≤ ∫ x in Submission.BoseGases.acube ℓ, (Work.BSKinetic.bsQ ℓ 0 ψ x) ^ 2 := by
  -- the localised mean-free state is in `L¹ ∩ L²` (continuity alone suffices)
  obtain ⟨hml1, hml2⟩ := boxState_memLp_of_continuous hℓ 0 hψ
  -- Plancherel for the `p`-convention transform, plus integrability of the energy density
  obtain ⟨hInt, hPlanch⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hml1 hml2
  -- discarding the cut-off `momProj ≤ 1`
  have hmono : ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ) p‖ ^ 2
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ) p‖ ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun p =>
        mul_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))
      hInt
      (Filter.Eventually.of_forall fun p =>
        mul_le_of_le_one_left (sq_nonneg _) (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p))
  have hkey : Work.BoseKinLoc.momForm ℓ d 0 ψ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ) p‖ ^ 2 := by
    rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  -- the uncut momentum mass is the mean-free box mass over the anchored cube
  have hfin : ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ x‖ ^ 2
      = ∫ x in Submission.BoseGases.acube ℓ, (Work.BSKinetic.bsQ ℓ 0 ψ x) ^ 2 := by
    rw [Work.BoseKinLoc.Kinetic.integral_boxState_normSq, lamBox_zero_eq_acube]
    simp only [Work.BoseKinLoc.Qfree]
  rw [hPlanch] at hkey
  exact hkey.trans (le_of_eq hfin)

end Work.BoseFixB3.HighMass
