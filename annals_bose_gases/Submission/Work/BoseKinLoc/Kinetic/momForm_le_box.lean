import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseKinLoc.Kinetic.boxState_memLp
import Submission.Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.momForm_le_box`

The large-momentum word `momForm` of FS `eq:DefT`'s third term is dominated by the
mean-free box mass `∫_{Λ(u)}(Q_uψ)²`.  Concretely, with `Λ(u) = lamBox ℓ u` and
`1_{Λ(u)}(ψ − m_u)` the complexified mean-free localised state,

`momForm ℓ d u ψ = (2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (1_{Λ(u)}(ψ − m_u)) p‖²`,

and `momProj ℓ d = 1_{(d²ℓ)⁻¹,∞)}(‖·‖) ≤ 1` pointwise, so the whole cut-off is simply
discarded:

`momForm ℓ d u ψ ≤ (2π)⁻³ ∫_p ‖kinFT (1_{Λ(u)}(ψ − m_u)) p‖² = ∫_x ‖1_{Λ(u)}(ψ − m_u) x‖²`

by `p`-convention Plancherel in `L¹ ∩ L²` (`kinFT_sq_of_memLp`), and the last integral is
`∫_{Λ(u)}(Q_uψ)²` because `1_{Λ(u)}` is the indicator of the box.

This is the (c1)-side "cheap" half of the sliding momentum localisation: the *content* of FS
`eq:Q1Qslide` is the `u`-average of this family, not the pointwise cut-off.

The two integration-theoretic inputs are delegated and imported:
`boxState_memLp` (the localised state is in `L¹ ∩ L²`) and `kinFT_sq_of_memLp`
(Plancherel for the `p`-convention transform, including integrability of the energy density).
-/

noncomputable section

namespace Work.BoseKinLoc.Kinetic

open MeasureTheory Filter

/-- The complexified mean-free localised box state `1_{Λ(u)}(ψ − m_u)` whose `p`-Fourier
transform is the `momForm` integrand (definitionally the function appearing in
`Work.BoseKinLoc.momForm`). -/
def boxState (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℂ :=
  fun x => ((Work.BoseKinLoc.indU ℓ u x : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ x : ℝ) : ℂ)

/-- `momForm` is the `(2π)⁻³`-normalised `p`-integral of the cut-off times the squared
`p`-Fourier transform of the localised mean-free state. -/
lemma momForm_eq_boxState (ℓ d : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.momForm ℓ d u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (boxState ℓ u ψ) p‖ ^ 2 := rfl

/-- The momentum cut-off is `≤ 1`. -/
lemma momProj_le_one (ℓ d : ℝ) (p : ℝ³) : Work.BoseKinLoc.momProj ℓ d p ≤ 1 := by
  unfold Work.BoseKinLoc.momProj
  split <;> norm_num

/-- The momentum cut-off is nonnegative. -/
lemma momProj_nonneg (ℓ d : ℝ) (p : ℝ³) : 0 ≤ Work.BoseKinLoc.momProj ℓ d p := by
  unfold Work.BoseKinLoc.momProj
  split <;> norm_num

/-- The moving box `Λ(u) = ℓu + acube ℓ` is measurable (preimage of the measurable cube under
the translation `x ↦ x − ℓu`). -/
lemma momForm_lamBox_measurable (ℓ : ℝ) (u : ℝ³) : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u
      = (fun x : ℝ³ => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
  rw [h]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage
    (continuous_id.sub continuous_const).measurable

/-- Pointwise, `‖1_{Λ(u)}(ψ − m_u)‖²` is the indicator of the box times `(Q_uψ)²`. -/
lemma boxState_normSq_eq_indicator (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    ‖boxState ℓ u ψ x‖ ^ 2
      = (Work.BoseKinLoc.lamBox ℓ u).indicator
          (fun z => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2) x := by
  by_cases hx : x ∈ Work.BoseKinLoc.lamBox ℓ u
  · simp only [Set.indicator_of_mem hx, boxState, Work.BoseKinLoc.indU]
    simp
  · simp only [Set.indicator_of_notMem hx, boxState, Work.BoseKinLoc.indU]
    simp

/-- The `L²` mass of the localised mean-free state is the mean-free box mass. -/
lemma integral_boxState_normSq (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    ∫ x : ℝ³, ‖boxState ℓ u ψ x‖ ^ 2
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2 := by
  simp_rw [boxState_normSq_eq_indicator ℓ u ψ]
  rw [MeasureTheory.integral_indicator (momForm_lamBox_measurable ℓ u)]

theorem momForm_le_box {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BoseKinLoc.momForm ℓ d u ψ
      ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2 := by
  -- the localised mean-free state is in `L¹ ∩ L²`
  obtain ⟨hF1, hF2⟩ := boxState_memLp (ℓ := ℓ) hℓ u hψ
  -- Plancherel for the `p`-convention transform, plus integrability of the energy density
  obtain ⟨hInt, hPlanch⟩ := kinFT_sq_of_memLp (F := boxState ℓ u ψ) hF1 hF2
  -- discarding the cut-off `momProj ≤ 1`
  have hmono : ∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (boxState ℓ u ψ) p‖ ^ 2
      ≤ ∫ p : ℝ³, ‖Submission.BoseGases.kinFT (boxState ℓ u ψ) p‖ ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun p => mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _))
      hInt
      (Eventually.of_forall fun p => mul_le_of_le_one_left (sq_nonneg _) (momProj_le_one ℓ d p))
  rw [momForm_eq_boxState]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (boxState ℓ u ψ) p‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
          ‖Submission.BoseGases.kinFT (boxState ℓ u ψ) p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ∫ x : ℝ³, ‖boxState ℓ u ψ x‖ ^ 2 := hPlanch
    _ = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2 :=
        integral_boxState_normSq ℓ u ψ

end Work.BoseKinLoc.Kinetic
