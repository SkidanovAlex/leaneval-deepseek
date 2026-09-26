import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.Smooth.Morse.Flow.fderiv_pullback_normalisedGradField
import Submission.Work.Smooth.Morse.Flow.regionEquivalent_of_periodicFlow
import Submission.Work.Smooth.Morse.Flow.lipschitzWith_descentField
import Submission.Work.Smooth.Morse.Flow.norm_descentField_le_one
import Submission.Work.Smooth.Morse.Flow.exists_localFlow_of_lipschitz
import Submission.Work.Smooth.Morse.Flow.flow_equivariant_of_periodic
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound_of_regularValue
import Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta
import Submission.Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region

/-!
# The normalised gradient flow of `g|_F`, and item 3 completed

This file assembles the flow input of item 3.  It contains the two halves of the argument:

* the *field*: `Work.Smooth.Morse.descentField ψ g p = -((1 + (∂₁G)² + (∂₂G)²)⁻¹) • (∂₁G, ∂₂G)` in
  the parameter plane, where `G = pullback ψ g`.  It is smooth, bounded by `1` and `2π`-periodic
  (`Work.Smooth.Morse.Flow.lipschitzWith_descentField`,
  `…norm_descentField_le_one`), and it lowers the level of `G` at the rate `descentRate`
  (`Work.Smooth.Morse.fderiv_pullback_descentField`);
* the *flow*: `Work.Smooth.Morse.Flow.exists_localFlow_of_lipschitz` (Picard–Lindelöf for a
  bounded Lipschitz field), `…flow_equivariant_of_periodic` (the flow commutes with the period
  lattice, by uniqueness), `…exists_descentRate_lower_bound_of_regularValue` (the rate is bounded
  below by a positive constant on a critical-free level band) and
  `…pullback_flow_descends_of_eta` (the flow carries the level `b` below the level `a`);
* the *assembly*: `Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region` — every loop of
  `F ∩ {g < b}` is homotopic, through loops of the surface, to a loop of `F ∩ {g < a}`, and hence
  `Work.Smooth.Morse.regularEquivalent_of_contDiff_two`: **`RegularEquivalent ψ g` holds for every
  `g` of class `C²`**.  This is item 3 of the chapter, proved (the only inputs are the two
  statements of `Pullback_flow_descends`-type which are themselves proved here).

Consequences: for `g` of class `C²` the winding span is constant across every critical-value-free
interval (`Work.Smooth.Morse.RegularEquivalent.windingSpan_eq`), and the hypotheses of the sweep
theorem `Work.Smooth.Morse.windingSpan_eq_of_levelSweep` reduce to the Morse/Sard input and the
local models at the critical values.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ}

/-- **Item 3.**  For a function of class `C²`, the sublevel regions across a critical-value-free
interval are related by `Work.SurgeryInvariance.RegionEquivalent`: every loop of the larger region
is transported to a loop of the smaller one with the same winding vector, and conversely (by
monotonicity).

The transport is the normalised gradient flow of `g|_F`, in the form of
`Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region`; the winding vector is unchanged because
the transported loop is homotopic to the original through loops of the surface
(`Work.SurgeryInvariance.WindingOf.homotopic_eq`). -/
theorem regularEquivalent_of_contDiff_two (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ 2 g) : RegularEquivalent ψ g := by
  intro a b hab hreg
  refine ⟨?_, ?_⟩
  · intro γ hγ
    exact ⟨γ, fun t => region_mono ψ g hab (hγ t), rfl⟩
  · intro γ hγ
    obtain ⟨γ', hγ', hhom⟩ :=
      Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region ψ hg hab hreg γ hγ
    exact ⟨γ', hγ', (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm⟩

/-- The `C^∞` form of `Work.Smooth.Morse.regularEquivalent_of_contDiff_two`. -/
theorem regularEquivalent_of_contDiff (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : RegularEquivalent ψ g :=
  regularEquivalent_of_contDiff_two ψ (hg.of_le (WithTop.coe_le_coe.mpr le_top))

end

end Work.Smooth.Morse
