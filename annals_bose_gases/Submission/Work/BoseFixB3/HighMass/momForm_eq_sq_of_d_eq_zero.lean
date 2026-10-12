import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.momForm_le_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.momForm_eq_sq_of_d_eq_zero`

**The large-momentum word is *exactly* the mean-free box mass at the cut-off `d = 0`.**

FS `eq:DefT`'s third kinetic piece is the momentum form of the windowed mean-free state

`momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹,∞)}(‖p‖)·‖kinFT (θ_u·Q_uψ) p‖²`

with the cut-off `momProj ℓ d p = 1_{(d²ℓ)⁻¹ < ‖p‖}`.  At `d = 0` the threshold is
`(0²·ℓ)⁻¹ = 0`, so the cut-off only removes the single momentum `p = 0`:

`momProj ℓ 0 p = 1` for every `p ≠ 0`, and `{0}` is a null set for the Lebesgue measure on
`ℝ³`.  Hence the cut-off may be dropped *without error* (not merely bounded by `1`, as in
the companion `Work.BoseFixB3.HighMass.momForm_le_sq`), and the uncut momentum integral is
the `L²`-mass of the localised mean-free state by the `p`-convention Plancherel identity
`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`:

    `momForm ℓ 0 0 ψ = (2π)⁻³ ∫_p ‖kinFT (θ_0 Q_0ψ) p‖² = ∫_{Λ(0)} (Q_0ψ)²
                    = ∫_{acube ℓ} (bsQ ℓ 0 ψ)²`,

the last step because the anchored box is the centred cube, `Λ(0) = lamBox ℓ 0 = acube ℓ`
(`lamBox_zero_eq_acube`).

Note that no property of the *mean* of `ψ` is used: the identity is a pure Plancherel
statement, and the `p = 0` mode dropped by the cut-off is of measure zero regardless of
its value.

The two integration-theoretic inputs are the colleagues' lemmas
`boxState_memLp_of_continuous` (the localised state of a continuous `ψ` lies in `L¹ ∩ L²`
— it is supported in the compact box, where the continuous mean-free part is bounded) and
`kinFT_sq_of_memLp` (Plancherel for the `p`-convention transform).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.HighMass

open Work.BoseKinLoc

/-- **The cut-off at `d = 0` is the indicator of `p ≠ 0`.**  For every real `ℓ` and every
`p ≠ 0` one has `momProj ℓ 0 p = 1`: the threshold `(0²·ℓ)⁻¹ = 0` is smaller than the
strictly positive norm `‖p‖`. -/
lemma momProj_zero_eq_one_of_ne_zero (ℓ : ℝ) {p : EuclideanSpace ℝ (Fin 3)} (hp : p ≠ 0) :
    Work.BoseKinLoc.momProj ℓ 0 p = 1 := by
  rw [Work.BoseKinLoc.momProj, if_pos (by simpa using norm_pos_iff.mpr hp)]

/-- **The cut-off at `d = 0` equals `1` almost everywhere**: it can differ from `1` only at
the origin, a null set. -/
lemma ae_momProj_zero_eq_one (ℓ : ℝ) :
    ∀ᵐ p ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      Work.BoseKinLoc.momProj ℓ 0 p = 1 := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (measure_singleton (0 : EuclideanSpace ℝ (Fin 3)))
  intro p hp
  by_contra hp0
  exact hp (momProj_zero_eq_one_of_ne_zero ℓ hp0)

/-- **`momForm` at the cut-off `d = 0` is the mean-free box mass.**  For every `0 < ℓ` and
every continuous `ψ : ℝ³ → ℝ`,

    `momForm ℓ 0 0 ψ = ∫_{acube ℓ} (bsQ ℓ 0 ψ)²`.

The cut-off `momProj ℓ 0 = 1_{p ≠ 0}` is `1` off a null set, so it drops out of the
`p`-integral; the remaining momentum integral is the `L²`-mass of the localised mean-free
state `1_{acube ℓ}(ψ − m_0)` by Plancherel, and the anchored box `Λ(0)` is `acube ℓ`. -/
theorem momForm_eq_sq_of_d_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.momForm ℓ 0 0 ψ
      = ∫ x in Submission.BoseGases.acube ℓ, (Work.BSKinetic.bsQ ℓ 0 ψ x) ^ 2 := by
  -- the localised mean-free state lies in `L¹ ∩ L²` (continuity of `ψ` suffices)
  obtain ⟨hml1, hml2⟩ := boxState_memLp_of_continuous hℓ 0 hψ
  -- Plancherel for the `p`-convention transform, plus integrability of the energy density
  obtain ⟨hInt, hPlanch⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hml1 hml2
  -- the cut-off agrees with `1` almost everywhere, so discarding it is an equality
  have hcut : ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ 0 p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ) p‖ ^ 2
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0 ψ) p‖ ^ 2 :=
    MeasureTheory.integral_congr_ae
      ((ae_momProj_zero_eq_one ℓ).mono fun p hp => by simp [hp])
  rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState, hcut, hPlanch,
    Work.BoseKinLoc.Kinetic.integral_boxState_normSq, lamBox_zero_eq_acube]
  -- `Qfree ℓ 0 ψ` is `bsQ ℓ 0 ψ` by definition
  rfl

end Work.BoseFixB3.HighMass
