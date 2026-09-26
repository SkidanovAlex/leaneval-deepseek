import Mathlib
import Submission.Work.PinchCounted.Assemble
import Submission.Work.SurgeryInvariance.All

/-!
# From Pardon's counted pinching family to a loop-level sweep

`Work.PinchCounted.CountedSweep P β` records Pardon's pinching family with the counting of his proof:
the regions `F ∩ int(S_t)`, the intermediate spheres `S_t` with *Pardon's two inputs* at each of them
(their trace is cleaned, `CleansInSphere`, and meets `β` fewer than `I(F,β)` times), the transport of
the loop content away from the exceptional parameters, and the local moves at them — the region
changes by an open piece `Z` of `F` whose **loops are matched by loops of the intermediate sphere**
`S_t` with the same winding vectors, or is transported.

This module converts that data into the library's loop-level sweep
`Work.SurgeryInvariance.SweepLoops P`, which is the interface the rest of the surgery-invariance
subproject consumes (`SweepLoops.spherefamily`, `SweepLoops.double_bubble`, ...).

The only mathematical input is Pardon's Lemma 2 in the shape proved in `Assemble.lean`
(`CountedSweep.windingSpan_eq_bot_of_loops_match`): a piece of the surface whose loops are matched by
loops of a clean, low-count sphere has **vanishing winding span**.  Applied to the changed piece `Z` of a local
move, this turns Pardon's geometric description of the pinch into the *span-preserving* local model
`SurgeryStepZero` which `SweepLoops` demands.  The regions and the exceptional parameters are carried
over verbatim, so the resulting sweep has exactly the same region function.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The local moves of a `CountedSweep` are loop-level surgery steps.**  At an exceptional
parameter, near which the region changes by an open piece `Z` whose loops are matched, with their
winding vectors, by loops of the intermediate sphere `S_t`, that change is a `SurgeryStepZero` — a
change by a piece of vanishing winding span — by Pardon's Lemma 2
(`CountedSweep.windingSpan_eq_bot_of_loops_match`); otherwise the local move is a `RegionEquivalent`
to begin with.

This is exactly the `surgery` field of `Work.SurgeryInvariance.SweepLoops`, with the same `ε`. -/
theorem countedSweep_surgeryStepZero_or_regionEquivalent {β : Work.CoreTopology.ClosedCurve P}
    (D : CountedSweep P β) (t : ℝ) (ht : t ∈ D.exc) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Work.SurgeryInvariance.SurgeryStepZero P (D.region t) (D.region s) ∨
        Work.SurgeryInvariance.RegionEquivalent P (D.region t) (D.region s) := by
  obtain ⟨ε, hε, hstep⟩ := D.surgery t ht
  refine ⟨ε, hε, fun s hs => ?_⟩
  rcases hstep s hs with ⟨Z, hZopen, hZmatch, hcase⟩ | h
  · refine Or.inl ⟨Z, ?_, D.region_open t, D.region_open s, hZopen, hcase⟩
    exact CountedSweep.windingSpan_eq_bot_of_loops_match (β := β)
      (D.sphere_clean t) (D.sphere_count t) hZmatch
  · exact Or.inr h

/-- **Pardon's pinching family, counted, is a loop-level sweep.**

The regions, the exceptional parameters and the local moves transport verbatim: away from `exc` the
loop content is transported, and at `t ∈ exc` either the region changes by a piece whose loops are matched by
loops of the low-count intermediate sphere `S_t` — a `SurgeryStepZero` by Pardon's Lemma 2 — or it is
transported.  In particular the region function is *unchanged*,
`S'.region = D.region`. -/
theorem exists_sweepLoops_of_countedSweep {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P} (D : Work.PinchCounted.CountedSweep P β) :
    ∃ S' : Work.SurgeryInvariance.SweepLoops P, S'.region = D.region :=
  ⟨{ region := D.region
     exc := D.exc
     regular := D.regular
     surgery := countedSweep_surgeryStepZero_or_regionEquivalent D }, rfl⟩

end

end Work.PinchCounted
