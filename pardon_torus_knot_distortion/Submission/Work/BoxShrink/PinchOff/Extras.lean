import Submission.Work.BoxShrink.PinchOff.closedDiscsCover_of_compact
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.exists_preconnected_not_isCompact_of_nontrivial_continuum
import Submission.Work.BoxShrink.PinchOff.exists_unbounded_component_compl_of_preconnected_compact
import Submission.Work.BoxShrink.PinchOff.fundamentalSquare_winding_zero
import Submission.Work.BoxShrink.PinchOff.isPreconnected_diff_singleton_of_minimal
import Submission.Work.BoxShrink.PinchOff.isPreconnected_sInter_of_chain
import Submission.Work.BoxShrink.PinchOff.lowerRegion_rank_zero_or_two
import Submission.Work.BoxShrink.PinchOff.mem_closure_connectedComponentIn_sdiff_singleton_of_isCompact
import Submission.Work.BoxShrink.PinchOff.niceLevel_boxRegion_rank_zero_or_two
import Submission.Work.BoxShrink.PinchOff.not_general_frontierCutting
import Submission.Work.BoxShrink.PinchOff.preconnected_subsingleton_of_preconnected_compact
import Submission.Work.BoxShrink.PinchOff.upperRegion_rank_zero_or_two
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_eq_top_of_compact_preimage

/-!
# The supporting results of the chapter: Pardon's dichotomy for the box, the half-regions and the
plane, and the covering of a compact slice by discs

This module collects the delegations and supporting lemmas of the earlier stretches of the chapter
which are not part of the main line (`Basic.lean`, `Tamed.lean`, …) but are used by it or are
relevant to the residual.  Everything here is sorry-free and axiom-free.

## Pardon's equation (1) — the `⊥`/`⊤` dichotomy, **discharged**

* `equation1Input_holds` — **Pardon's equation (1) itself**: for every smooth torus, every
  continuous `g` and every *nice* level (a finite disjoint union of simple closed curves) whose
  level set carries no essential loop, the sublevel region has winding span `⊥` or `⊤`.  This is the
  carried classical input `Work.BoxShrink.Pinch.Equation1Input` of the parent chapter, **proved**
  here from the engine below (the family of circles of `NiceLevel.circleUnion`, the two open
  sublevel/superlevel pieces, and trichotomy of `<`).  It removes that input from the chapter's
  carried list.
* `windingSpan_bot_or_top_of_inessential_boundary` — **the engine**: a region of the torus whose
  boundary is a finite disjoint union of simple *inessential* closed curves, split into two open
  pieces, has winding span `⊥` or `⊤`;
* `niceLevel_boxRegion_rank_zero_or_two` — the box region `Ω = F ∩ PBox s c σ` at a *nice* level `s`
  whose trace carries no essential loop has rank `0` or `2`;
* `upperRegion_rank_zero_or_two`, `lowerRegion_rank_zero_or_two` — the same for the two
  half-regions, as `Work.BoxShrink.Bubble.PardonDichotomy` statements: these are cases of the
  carried classical input `Work.BoxShrink.Pinch.Equation1Input` for the level functions
  `upperLevel`/`lowerLevel` of the pinch.

## The local topology of the surface

* `exists_discRegion_of_not_isEssential` — an inessential simple closed curve of the surface bounds
  an embedded disc of the surface;
* `closedDiscsCover_of_compact` (and the size-controlled disc `exists_discRegion_carrier_subset_open`)
  — a compact slice is covered by the interiors of finitely many embedded discs;
* `windingSpan_sdiff_eq_top_of_compact_preimage` — removing a piece of the surface with compact
  preimage from a region leaves the winding span `⊤`.

## Plane and separation lemmas

* `fundamentalSquare_winding_zero`, `not_general_frontierCutting` — the winding of a curve of the
  fundamental square, and the failure of a general "frontier cutting" statement (the local
  obstruction of the parent chapter's §10.5);
* `isPreconnected_sInter_of_chain`, `isPreconnected_diff_singleton_of_minimal`,
  `preconnected_subsingleton_of_preconnected_compact`,
  `mem_closure_connectedComponentIn_sdiff_singleton_of_isCompact`,
  `exists_preconnected_not_isCompact_of_nontrivial_continuum`,
  `exists_unbounded_component_compl_of_preconnected_compact` — the continuum lemmas of the
  separation arguments (they are the tools behind `Work.PinchLemma3`'s and the parent chapter's
  plane arguments, kept here because this chapter uses them).

See `README.md` §14 for the statements and the role of each.
-/

namespace Work.BoxShrink.PinchOff

end Work.BoxShrink.PinchOff
