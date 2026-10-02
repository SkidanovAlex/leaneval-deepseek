import Mathlib
import Submission.Work.Stems.oddSphereRange_of_rangeAcyclic
import Submission.Work.Stems.c2oddRange_of_c2evenRange
import Submission.Work.Stems.Engine.C2Even
import Submission.Work.Stems.Engine.C2EvenRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `C2` layer of the Serre blueprint: assembled

The `K(ℤ,n)` layer (`C2` of `Submission/Work/Drive/SERRE_BLUEPRINT.md` §2) is the component of the
stable-stems theorem owned by area STEMS.  `Submission/Work/Stems/EM_C2_RANGE_FINDING.md` records
that the two range-form statements `Work.Stems.Engine.C2evenRange` / `C2oddRange` have no producer
inside the range-form mutual induction, because the *odd* statement is used to feed the *even* one
and the ranges lose a constant number of degrees per level.

This module assembles the corrected chain, which **does** close.  The key input is that the odd
statement does not have to be proved from the even one: for `A = ℤ` and `k` **odd** it follows from
`Work.RatHurewicz.RangeModelRatAcyclic` (a range model of `K(A,k)` through `2k-1` has vanishing
rational homology above `k`) together with connectivity and the first-degree Hurewicz theorem —
`Work.Stems.oddSphereRange_of_rangeAcyclic`.  The chain is then

* `RangeModelRatAcyclic + SerreC1 ⟹ OddSphereRange (fun n => 2 * n)` — the odd model is rationally
  `Sⁿ` below `2n`;
* `... + SerreE3b ⟹ C2evenRange` — the path–loop fibration `ΩL → PL → L` with the Gysin/periodicity
  iso `⌣e : H^m(L) ≅ H^{m+2j}(L)` for `m ≤ 2j-2` (the fibre `ΩL` is a `K(ℤ,2j-1)` known as a
  rational sphere through `2(2j-1)-1 = 4j-3`); the descent from `H^0(L) ≅ ℚ` gives the sharp bound
  `4j-1`, and the field universal coefficient theorem
  (`Work.Stems.isZero_ratH_of_isZero_ratCoh`) transports the vanishing to homology;
* `... + SerreStableExact ⟹ C2oddRange` — the cover `Eₙ = hofib(Sⁿ → X)` is `n`-connected, the
  Serre exact sequence in the stable range gives `H_j(Eₙ, ΩX) ≅ H_j(Sⁿ,*) = 0`, and the long exact
  sequence of the pair plus `C2evenRange` on `ΩX = K(ℤ,n-1)` (whose bound `2n-3` matches exactly)
  kills `H_j(Eₙ;ℚ)`;

with the *same* bounds as the range-form statements, so nothing is lost.  Consequently the `C2`
statements are **not** independent gaps of the STEMS route: they follow from the four hypotheses
below, each of which is another area's contract (`RangeModelRatAcyclic`, `SerreC1`, `SerreE3b`,
`SerreStableExact`).

The second half of the file does the same for the *free-top* (range-model) form of the even step,
`Work.Stems.Engine.c2evenRangeModel`, which is what the free-top sphere route
(`Work.Stems.Engine.FreeTopAssembly`) consumes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.Engine

noncomputable section

/-- **The range-form even step, from the range-model computation of `K(ℤ,k)`.** -/
theorem c2evenRange_of_rangeAcyclic (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hC1 : Work.Serre.SerreC1) (hE3b : Work.Serre.SerreE3b) :
    Work.Stems.Engine.C2evenRange :=
  Work.Stems.Engine.c2evenRange_of_oddSphereRange
    (Work.Stems.oddSphereRange_of_rangeAcyclic h hC1) hE3b

/-- **The `C2` layer, both steps, from the four contracts.** -/
theorem c2evenRange_and_c2oddRange (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hC1 : Work.Serre.SerreC1) (hE3b : Work.Serre.SerreE3b) (hK5 : Work.Serre.SerreStableExact) :
    Work.Stems.Engine.C2evenRange ∧ Work.Stems.Engine.C2oddRange :=
  ⟨c2evenRange_of_rangeAcyclic h hC1 hE3b,
    Work.Stems.c2oddRange_of_c2evenRange (c2evenRange_of_rangeAcyclic h hC1 hE3b) hK5⟩

/-- **The free-top even step for range models, from the range-model computation.** -/
theorem c2evenRangeModelVanishing_of_rangeAcyclic
    (h : Work.RatHurewicz.RangeModelRatAcyclic) (hE3b : Work.Serre.SerreE3b) :
    Work.Stems.Engine.C2evenRangeModelVanishing :=
  Work.Stems.Engine.c2evenRangeModelVanishing h hE3b

end

end Work.Stems.Engine
