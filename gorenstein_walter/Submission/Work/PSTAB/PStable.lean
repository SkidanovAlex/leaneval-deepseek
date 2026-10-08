/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.NoQuaternionSectionProp
import Submission.Work.PSTAB.QuadPairIrrSection
import Submission.Work.PSTAB.BadSectionOfQuotient
import Submission.Work.PSTAB.StabPerFactorSection
import Submission.Work.PSTAB.StabilityLift
import Submission.Work.GLUE.pCore_eq_opCore

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped MatrixGroups
open Subgroup

/-!
# AREA PSTAB — the deliverable `Work.GW2.PStableProp`

`Work.GW2.PStableProp` is the contract statement

```
∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → DihOrCycSylow X → IsPStable' p X
```

("`Qd(p)` is not involved, so `X` is `p`-stable" — Glauberman Lemma 6.3, (a) ⇒ (b)).

The proof is the design's §3 chain, in the section-strength form (design pass 11 §4):

* `Work.GW2.noQuaternionSectionProp` (`NoQuaternionSectionProp`, Step 1): a group with
  dihedral/cyclic Sylow `2`-subgroups has no section that is a noncyclic `2`-group with a
  unique involution;
* `Work.PSTAB.QuadPairIrrSection` (`QuadPairIrrSectionProp`, Step 2): a faithful irreducible
  `𝔽_p`-module for `L` with a quadratic nontrivial `p`-element forces such a section of `L`;
* `Work.PSTAB.StabPerFactorSection` (Step 3, per-chief-factor): each `M`-chief factor of the
  normal `p`-subgroup `K` is centralized by `A` when `⁅⁅K,A⁆,A⁆ = ⊥` — a contradiction is
  reached by applying the section-strength quadratic-pair lemma to
  `M ⧸ C_M(U/V)` acting on the chief factor, and pulling the resulting bad section back to `M`
  with `Work.PSTAB.BadSectionOfQuotient`;
* `Work.PSTAB.StabilityLift`: assembling the per-factor statement into
  `A·C_M(K)/C_M(K) ≤ O_p(M/C_M(K))` (the port of `OddOrder.BG.AppA.stabilityLiftAux` with the
  odd/solvable hypotheses replaced by `NoBadSection`);
* the final transport from the library's `opCore` to the contract's `pCore`
  (`Work.GLUE.pCore_eq_opCore`, area GLUE).

Variants: `Work.PSTAB.StabPerFactor` is the same per-chief-factor step stated with the *subgroup*
strength hypothesis `Work.PSTAB.QuadPairIrrProp` (that lemma is still open; see `NOTES.md`).
-/

namespace Work.GW2

/-- **The deliverable of area PSTAB**: every finite group with cyclic or dihedral Sylow
`2`-subgroups is `p`-stable for every odd prime `p`. -/
theorem pStable : PStableProp := by
  intro X _ _ p hp hp2 hD
  intro K A hKn hK hA hKAA
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : K.Normal := hKn
  rw [show Work.GW2.pCore p (X ⧸ Subgroup.centralizer (K : Set X))
      = OddOrder.Isaacs.Ch01.opCore p (X ⧸ Subgroup.centralizer (K : Set X)) from
    Work.GLUE.pCore_eq_opCore]
  exact Work.PSTAB.StabilityLift hp2 hK hA hKAA
    (fun i => Work.PSTAB.StabPerFactorSection hp2 Work.PSTAB.QuadPairIrrSection
      Work.PSTAB.BadSectionOfQuotient (noQuaternionSectionProp X hD) hK hA hKAA i)

/-- The deliverable in the area's own namespace, for convenience. -/
theorem pStable' : PStableProp := pStable

end Work.GW2

namespace Work.PSTAB

/-- The deliverable of area PSTAB, stated in the area's namespace. -/
theorem pStable : Work.GW2.PStableProp := Work.GW2.pStable

end Work.PSTAB
