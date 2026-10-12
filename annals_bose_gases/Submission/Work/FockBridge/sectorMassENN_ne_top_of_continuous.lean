import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.FockBridge.sectorMassENN_ne_top_of_continuous`

**The `abox`-`L²`-mass of a *continuous* state is finite.**

Everything in the Fock / particle-number layer `Submission.Work.FockBridge` is a mass taken over
the corpus analysis box `abox N L` (`Λ(L)^N`), the same normalisation slot as the corpus's
`sqNormN N L Φ = ∫_{abox N L} Φ²`.  The real-valued (`toReal`) part of that layer — e.g.
`Work.FockBridge.sum_sectorMass_eq_sqNorm` and its consumers — is conditioned on

    hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤

(the `ENNReal`-valued total mass being finite, so that `toReal` is additive over the sectors).
For a state that is *continuous* on the configuration space this is not an extra hypothesis but a
theorem, proved here.

The proof is the elementary compactness argument.  For **every** `L` the box `abox N L` is
contained in the honest box `abox N (max L 1)` (`acube` is monotone in the side length, and
`max L 1 > 0`), which is compact (`Submission.BoseGases.abox_compact`).  A continuous function is
bounded on a compact set, `‖Φ x‖ ≤ C` (`IsCompact.exists_bound_of_continuousOn`), so the
integrand is dominated on the box by the constant `(max C 0)²`; hence

    ∫⁻_{abox N L} ofReal (Φ²) ≤ ofReal ((max C 0)²) · volume (abox N L) < ∞

because the centred box has finite volume (`Submission.BoseGases.abox_lt_top`).
-/

namespace Work.FockBridge

open MeasureTheory
open Submission.BoseGases

theorem sectorMassENN_ne_top_of_continuous {N : ℕ} {L : ℝ}
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΦ : Continuous Φ) :
    (∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤ := by
  -- The box with side length `max L 1` is honest (positive side length) and contains `abox N L`.
  have hMpos : 0 < max L 1 := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
  have hsub : Submission.BoseGases.abox N L ⊆ Submission.BoseGases.abox N (max L 1) := by
    intro x hx
    simp only [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_acube_iff,
      Set.mem_Icc] at hx ⊢
    intro i m
    exact ⟨by linarith [(hx i m).1, le_max_left L 1],
           by linarith [(hx i m).2, le_max_left L 1]⟩
  -- A continuous function is bounded on the compact box `abox N (max L 1)`.
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hMpos).exists_bound_of_continuousOn
    hΦ.continuousOn
  have hbound : ∀ x ∈ Submission.BoseGases.abox N L,
      ENNReal.ofReal ((Φ x) ^ 2) ≤ ENNReal.ofReal ((max C 0) ^ 2) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    rw [sq_le_sq, abs_of_nonneg (le_max_right C 0)]
    calc |Φ x| = ‖Φ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ C := hC x (hsub hx)
      _ ≤ max C 0 := le_max_left C 0
  -- The box has finite volume (the restricted measure is finite).
  have hμ : (volume : Measure (Submission.BoseGases.X N)) (Submission.BoseGases.abox N L) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (Submission.BoseGases.abox_lt_top N (max L 1) (le_of_lt hMpos))
  have hle : ∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)
      ≤ ENNReal.ofReal ((max C 0) ^ 2) * volume (Submission.BoseGases.abox N L) := by
    calc ∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)
        ≤ ∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((max C 0) ^ 2) :=
          setLIntegral_mono measurable_const hbound
      _ = ENNReal.ofReal ((max C 0) ^ 2) * volume (Submission.BoseGases.abox N L) :=
          setLIntegral_const _ _
  exact ne_of_lt (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ))

end Work.FockBridge
