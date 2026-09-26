import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API
import Submission.Work.SurgeryInvariance.Sweep.exists_of_single_surgery

/-!
# The double bubble at the level of sweeps

Pardon's Lemma 3 (the "double bubble") decomposes the region `A = F ∩ int(S)` inside the original
sphere as the union of the two half-box regions `H₁`, `H₂` and the interior of the disc `D` cut out
by the cutting plane:

`A = (H₁ ∪ H₂) ∪ D.interior`,   `Disjoint H₁ H₂`,   `Disjoint (H₁ ∪ H₂) D.interior`,

the two halves and the disc being open in the surface `F = torus ψ`.

The content of this file is that this geometric situation is already a **sweep** in the sense of
`Work.SurgeryInvariance.Sweep`: it is the single `2`-surgery that removes the interior of the
embedded disc `D` from `A`, and it is realised by the family which is constant equal to `A` before
the critical parameter `1/2` and constant equal to `H₁ ∪ H₂` after it
(`Work.SurgeryInvariance.Sweep.exists_of_single_surgery`).  The openness of `H₁ ∪ H₂` in the
surface is the only place where the openness certificates `hopen₁`, `hopen₂` are used, and the
sweep is regular away from `1/2` because the family is locally constant there.

## Scope: what the hypothesis `A = (H₁ ∪ H₂) ∪ D.interior` does and does not describe

`D.interior` here is the interior of an **embedded disc of the surface** `F`, so the hypothesis says
that the region inside the pinched sphere differs from the union of the two half-regions by an open
piece of `F` — the local model of a single `2`-surgery
(`Work.SurgeryInvariance.SurgeryShape`).  This is exactly the input of
`Work.SurgeryInvariance.Sweep` and it is the form in which the sibling subproject
`Work.SurgeryInvariance` states Pardon's Lemma 3.

It is *not* the decomposition of Pardon's closed slice: the trace on `F` of the *cutting plane* is a
`1`-dimensional slice `F ∩ PBox ∩ {y = const}`, a closed subset of the region with empty interior,
and by `Work.BoxShrink.Bubble.Obstruction` such a piece can never be removed by a single
`SurgeryStepZero` (a `2`-surgery removes a piece which is clopen in the region).  For the closed
slice the honest input is a `RegionEquivalent` between the region and the union of the two halves
(the `SlicePushOff` of `Work.BoxShrink.Bubble`), consumed by
`Work.Smooth.Morse.doubleBubble_containsEssentialLoop_of_regionEquivalent`.  This file provides the
`Sweep` for the `2`-surgery model; the two inputs are genuinely different statements.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Morse.Application

/-- **The double bubble is the sweep of a single `2`-surgery.**  If `A = (H₁ ∪ H₂) ∪ D.interior`
with `H₁`, `H₂`, `D.interior` open in the surface, `H₁` disjoint from `H₂` and both disjoint from
the disc `D`, then there is a sweep of `torus ψ` whose region at time `0` is `A` and whose region
at time `1` is `H₁ ∪ H₂`.

This is the geometric input of the double-bubble step of Pardon's argument, packaged in the
vocabulary of the sweep: the passage from the region inside the sphere to the region inside the
double bubble is a single `2`-surgery, namely the removal of the interior of the embedded disc `D`.
The sweep is the piecewise constant family `region t = A` for `t ≤ 1/2` and `region t = H₁ ∪ H₂`
for `t > 1/2`, whose only exceptional parameter is `1/2`. -/
theorem exists_sweep_of_doubleBubble (ψ : Submission.Diffeo) {A H₁ H₂ : Set LeanEval.KnotTheory.PardonDistortion.R3} {D : Work.SurgeryInvariance.DiscRegion (Work.Smooth.Morse.torus ψ)} (hopen₁ : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) H₁) (hopen₂ : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) H₂) (hdisj : Disjoint H₁ H₂) (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior) (hcover : A = (H₁ ∪ H₂) ∪ D.interior) : ∃ S : Work.SurgeryInvariance.Sweep (Work.Smooth.Morse.torus ψ), S.region 0 = A ∧ S.region 1 = H₁ ∪ H₂ := by
  -- The two half-box regions are two open pieces of the surface, disjoint from one another.
  have hdisjHalf : Disjoint H₁ H₂ := hdisj
  -- Hence their union `H₁ ∪ H₂` is open in the surface, and `A` is obtained from it by adjoining
  -- the interior of the embedded disc `D`, which is disjoint from `H₁ ∪ H₂`.
  exact Work.SurgeryInvariance.Sweep.exists_of_single_surgery A (H₁ ∪ H₂) D
    (Work.SurgeryInvariance.isOpenInCarrier_union (Work.Smooth.Morse.torus ψ) hopen₁ hopen₂)
    hdisjZ hcover

end Work.Smooth.Morse.Application
