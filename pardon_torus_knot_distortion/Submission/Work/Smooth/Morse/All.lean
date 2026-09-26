import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.ParamDeriv
import Submission.Work.Smooth.Morse.Immersion
import Submission.Work.Smooth.Morse.Surface.isCompact_torus
import Submission.Work.Smooth.Morse.Surface.isCompact_levelSet
import Submission.Work.Smooth.Morse.Surface.isCompact_closedRegion
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.Smooth.Morse.Critical.isClosed_criticalParam
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_countable
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_locallyFinite
import Submission.Work.Smooth.Morse.Regular.pullback_local_arc
import Submission.Work.Smooth.Morse.Regular.pullback_local_arc_contDiff
import Submission.Work.Smooth.Morse.Regular.pullback_local_arc_ball
import Submission.Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue
import Submission.Work.Smooth.Morse.Regular.isCircleUnion_components_embeddedCircle
import Submission.Work.Smooth.Morse.Regular
import Submission.Work.Smooth.Morse.Span
import Submission.Work.Smooth.Morse.Span.carrier_eq_top
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.Smooth.Morse.MorseModel
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq
import Submission.Work.Smooth.Morse.MorseModel.exists_discRegion_eq_inter_ball
import Submission.Work.Smooth.Morse.MorseModel.not_discModel_of_lt
import Submission.Work.Smooth.Morse.Sweep.windingSpan_locally_const_of_regularValue
import Submission.Work.Smooth.Morse.Sweep.regionEquivalent_locally_of_regularValue
import Submission.Work.Smooth.Morse.Sweep
import Submission.Work.Smooth.Morse.Sweep.exists_levelFamily_of_levelData
import Submission.Work.Smooth.Morse.Sweep.exists_levelFamily_of_crossing
import Submission.Work.Smooth.Morse.Sweep.exists_levelFamily_of_crossing_on
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.Smooth.Morse.Banded
import Submission.Work.Smooth.Morse.Flow.fderiv_pullback_normalisedGradField
import Submission.Work.Smooth.Morse.Flow.regionEquivalent_of_periodicFlow
import Submission.Work.Smooth.Morse.Flow.lipschitzWith_descentField
import Submission.Work.Smooth.Morse.Flow.lipschitzWith_scaled_smul
import Submission.Work.Smooth.Morse.Flow.norm_descentField_le_one
import Submission.Work.Smooth.Morse.Flow.exists_localFlow_of_lipschitz
import Submission.Work.Smooth.Morse.Flow.flow_equivariant_of_periodic
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound_of_regularValue
import Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta
import Submission.Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region
import Submission.Work.Smooth.Morse.Gauge
import Submission.Work.Smooth.Morse.Gauge.PBox_subset_boxGauge
import Submission.Work.Smooth.Morse.Gauge.boxGauge_subset_PBox
import Submission.Work.Smooth.Morse.Gauge.gaugeSandwich
import Submission.Work.Smooth.Morse.Gauge.exists_smooth_gauge_of_not_mem_centre
import Submission.Work.Smooth.Morse.Gauge.smoothGaugeSandwich
import Submission.Work.Smooth.Morse.Application
import Submission.Work.Smooth.Morse.Application.levelSweep_span_not_const
import Submission.Work.Smooth.Morse.Application.global_sweep_vacuous
import Submission.Work.Smooth.Morse.Application.exists_sweep_of_doubleBubble

/-!
# `Work.Smooth.Morse` — the smooth level-set / Morse chapter

This is the entry point of the chapter: importing this module gives the whole area.  See
`Submission/Work/Smooth/Morse/README.md` for a prose account of what is proved, what is isolated
as an input, and what is deliberately *not* claimed.

## The setting

For `ψ : Submission.Diffeo` the surface `F = ψ(standard torus of revolution)` is a smoothly
embedded torus, parametrised by `param ψ p = ψ (torusMap p.1 p.2)`
(`Work.Smooth.Morse.param`, `Work.Smooth.Morse.torus`); for `g : ℝ³ → ℝ` the sweep is the family of
level sets `{g = t}` and the regions are `Work.Smooth.Morse.region ψ g t = F ∩ {g < t}`.

## Main results

* **item 1** — `Work.Smooth.Morse.isImmersion`: the parametrisation of `F` is an immersion, from
  the explicit derivative `Work.Smooth.Morse.torusDeriv` of the torus parametrisation
  (`Work.Smooth.Morse.Immersion.hasFDerivAt_torusMap`,
  `Work.Smooth.Morse.Immersion.torusDeriv_injective`);
* **item 2** — `Work.Smooth.Morse.niceLevel_of_regularValue`,
  `Work.Smooth.Morse.ae_niceLevel_of_countable`,
  `Work.Smooth.Morse.ae_niceLevel_of_locallyFinite`: a regular level of `g|_F` is a compact finite
  disjoint union of simple closed curves of the torus, and almost every level is regular;
* **item 3** — `Work.Smooth.Morse.regularEquivalent_of_contDiff_two` /
  `Work.Smooth.Morse.regularEquivalent_of_contDiff`: **across a critical-value-free interval the two
  sublevel regions are `RegionEquivalent`**, proved for every `g` of class `C²`/`C^∞` from the
  normalised gradient flow (`Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region`); the
  reduction from an abstract transport datum is
  `Work.Smooth.Morse.SublevelTransport.toRegionEquivalent`,
  `Work.Smooth.Morse.regularEquivalent_of_transport`;
* **item 4** — the satisfiable first-tangency model `Work.Smooth.Morse.DiscGrowth`
  (`…of_min`, `…toSurgeryShape`, `…toSurgeryStepZero`, `…windingSpan_eq`) and the fact that the
  stronger-looking `Work.Smooth.Morse.MorseModel.not_discModel_of_lt` shows `DiscModel` to be
  available only at the bottom of the range of `g|_F`; `Work.Smooth.Morse.DiscModel.toSurgeryShape`,
  `Work.Smooth.Morse.DiscModel.toSurgeryStepZero`,
  `Work.Smooth.Morse.MorseModel.windingSpan_locally_const`;
* **item 5** — `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing`,
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_of_crossing` and
  `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_surgeryStepZero'` (the transport discharged and
  the local model in its satisfiable form);
  also `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_contDiff` and
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_of_contDiff` (with `DiscModel`, vacuous);
  `Work.Smooth.Morse.windingSpan_eq_of_levelSweep` (and the variants
  `…_of_span`, `…_of_surgeryStepZero`), `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep`,
  `Work.Smooth.Morse.LevelFamily.windingSpan_eq`, `Work.Smooth.Morse.LevelFamily.containsEssentialLoop_iff`,
  `Work.Smooth.Morse.Sweep.exists_levelFamily_of_levelData`.
* **the *banded* form of item 5** (`Submission/Work/Smooth/Morse/Banded.lean`) — the form in which
  the local models are only imposed on the band `Set.Icc a b` of levels actually swept, and the only
  non-vacuous form (on all of `ℝ` the sandwich `PBox(t) ⊆ {g < t}` together with the crossing data
  is contradictory):
  `Work.Smooth.Morse.eq_of_locally_constOn` (a quantity locally constant at every point of `[a,b]`
  is constant on `[a,b]`), `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing_on`,
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_of_crossing_on`,
  `Work.Smooth.Morse.containsEssentialLoop_of_levelSweep_of_crossing_on`, and their
  transport-explicit forms `Work.Smooth.Morse.windingSpan_eq_of_levelSweep_on`,
  `Work.Smooth.Morse.containsEssentialLoop_iff_of_levelSweep_on`.  The box-sweeping steps are
  `Work.Smooth.Morse.boxSweep_containsEssentialLoop_of_crossing_on` and
  `Work.Smooth.Morse.boxSweep_containsEssentialLoop_on`; Pardon's Lemma 3 in this chapter's
  vocabulary is `Work.Smooth.Morse.doubleBubble_containsEssentialLoop` together with the satisfiable
  forms `Work.Smooth.Morse.doubleBubble_containsEssentialLoop_of_split`, `…_of_regionEquivalent`
  and `…_of_sweep`, and the union step `Work.Smooth.Morse.containsEssentialLoop_of_union`.
* **the *vacuity* of the global form**: `Work.Smooth.Morse.WindingSpan_carrier_eq_top` and
  `Work.Smooth.Morse.Application.not_global_crossing` — the crossing hypothesis imposed at *every*
  critical value is unsatisfiable for a `C^∞` function on the compact torus, so the global forms of
  Pardon's sweeping step prove nothing and the banded forms are the ones to use.
* **the explicit rounded box**: `Work.Smooth.Morse.Gauge.gaugeSandwich`,
  `Work.Smooth.Morse.Gauge.exists_smooth_gauge_of_not_mem_centre` and their composition
  `Work.Smooth.Morse.Gauge.exists_smooth_gauge_with_sandwich` (a `C^∞` gauge with
  `PBox(t) ⊆ {g < t} ⊆ PBox((1+δ) t)` and an explicit arbitrarily small room `δ`).
* **the sharpness of the whole construction**: `Work.Smooth.Morse.Application.levelSweep_span_not_const`
  — for the standard torus and a height coordinate the winding span of `F ∩ {g < t}` genuinely jumps
  from `⊥` to `⊤`, so the persistence along a *level* family is false in general; the sweep theorems
  of item 5 are therefore stated with explicit local-model/ crosssing hypotheses, and the local model
  which Pardon's argument uses lives on the *sphere* family put in general position
  (`Work.SurgeryInvariance.SurgeryShape`).

* **the flow input of item 3** — `Work.Smooth.Morse.Flow.fderiv_pullback_normalisedGradField`
  (the descent field lowers the level at unit speed) and
  `Work.Smooth.Morse.Flow.regionEquivalent_of_periodicFlow` (a periodic level flow descends to the
  surface and gives `RegionEquivalent`).

## The two isolated inputs

* `Work.Smooth.Morse.CompactOneManifoldInput` — the classification of compact `1`-manifolds (a
  compact set which is locally an arc is a finite disjoint union of simple closed curves); Mathlib
  has no classification of `1`-manifolds;
* `Work.Smooth.Morse.LocallyFiniteCriticalValues` (or countability of the critical values) — the
  Sard/Morse input that the critical values are locally finite; Mathlib has no Sard theorem
  (and Sard for `C¹` maps is *false*, so the smoothness hypothesis of the application — a rounded
  box with a `C^∞` gauge — is what makes the statement true); the same input follows for a Morse
  function on a compact surface from the finiteness of the critical set.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

end Work.Smooth.Morse
