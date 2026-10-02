import Mathlib
import Submission.Work.RatHurewicz.transfer3
import Submission.Work.Stems.cycleLiftOfIso
import Submission.Work.Stems.cycleFiniteModelLocal
import Submission.Work.Stems.rangeModelRatAcyclicLocal
import Submission.Work.Stems.Engine.C2FreeTop
import Submission.Work.StemsB.C2_of_odd
import Submission.Work.StemsB.hfree_of_C2
import Submission.Work.StemsB.fgCase_of_free_and_C3_two
import Submission.Work.StemsB.RangeEMVanFinite
import Submission.Work.RatHurewicz.S3Inputs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `C2`/`C3` route to `Work.RatHurewicz.RangeModelRatAcyclic3`

`Work.RatHurewicz.RangeModelRatAcyclic3` (the second input of the STEMS contract, in its
*one-degree-short* form `k < j ≤ 2k-2`) is the restriction of
`Work.RatHurewicz.RangeModelRatAcyclic` (`k < j ≤ 2k-1`), which is produced from

* `Work.StemsB.C2RatSphereRange` — a range model of `K(ℤ,k)` is rationally `S^k` below `2k`
  (the `C2` layer of area STEMS: `K(ℤ,n)` rationally, the free part of the Eilenberg–MacLane
  computation; its free-top form `Work.Stems.Engine.C2oddFree c` is proved in
  `Submission/Work/Stems/c2FreeMain.lean` from `Work.Serre.SerreE3b`), and
* `Work.StemsB.C3FiniteTwo` — a range model of `K(A,k)`, `A` finite, is rationally acyclic
  (area SERRE, from `Work.Serre.serreC3FiniteOne`, the `K(A,1)` case for finite `A`).

## Why this file re-derives the reduction

The reduction `RangeModelRatAcyclic ⟸ (free f.g. case) + C3FiniteTwo` of area STEMS-B is the pair

* `Work.Stems.rangeModelRatAcyclicLocal` — the copy, in this area's namespace, of
  `Work.StemsB.rangeModelRatAcyclic_of_fgCase`, taking the *compactness* statement
  `Work.Stems.CycleFiniteModelLocal` as a hypothesis, and
* `Work.Stems.cycleFiniteModelLocal` — that compactness statement itself
  (`Work.Stems.CycleFiniteModelLocal`, a copy of `Work.StemsB.CycleFiniteModel`),

together with the *clean* modules `Work.StemsB.hfree_of_C2`, `Work.StemsB.fgCase_of_free_and_C3_two`
and `Work.StemsB.C3FiniteTwo_of_serreC3FiniteOne`.  The chain is used here instead of
`Work.StemsB.rangeModelRatAcyclic_of_C2_C3` because the latter's import closure contains
`Submission.Work.StemsB.cycleFiniteModel`, which does not build at present (the interface of
`Work.StemsB.cycleLift` was changed).  The statements are identical, so nothing is lost.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **`RangeModelRatAcyclic` from the `C2` and `C3` inputs.** -/
theorem rangeModelRatAcyclic_of_C2_C3 (hC2 : Work.StemsB.C2RatSphereRange)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.RatHurewicz.RangeModelRatAcyclic :=
  rangeModelRatAcyclicLocal cycleFiniteModelLocal
    (Work.StemsB.fgCase_of_free_and_C3_two (Work.StemsB.hfree_of_C2RatSphereRange hC2) hC3)

/-- **`RangeModelRatAcyclic` from the odd free-top `C2` interface and `C3`.** -/
theorem rangeModelRatAcyclic_of_C2odd_C3 (c : ℕ) (hC2 : Work.Stems.Engine.C2oddFree c)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.RatHurewicz.RangeModelRatAcyclic :=
  rangeModelRatAcyclic_of_C2_C3 (Work.StemsB.C2RatSphereRange_of_C2oddFree c hC2) hC3

/-- **`RangeModelRatAcyclic` from the odd free-top `C2` interface and `serreC3FiniteOne`.** -/
theorem rangeModelRatAcyclic_of_C2odd_C3one (c : ℕ) (hC2 : Work.Stems.Engine.C2oddFree c)
    (hC3one : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num : 0 < 1) X pt → Work.Serre.RatAcyclic X) :
    Work.RatHurewicz.RangeModelRatAcyclic :=
  rangeModelRatAcyclic_of_C2odd_C3 c hC2 (Work.StemsB.C3FiniteTwo_of_serreC3FiniteOne hC3one)

/-- **The one-degree-short form is a consequence of the full form.** -/
theorem rangeModelRatAcyclic3_of_rangeModelRatAcyclic
    (h : Work.RatHurewicz.RangeModelRatAcyclic) : Work.RatHurewicz.RangeModelRatAcyclic3 :=
  fun k hk Z _ z₀ hmodel j hj1 hj2 => h k hk Z z₀ hmodel j hj1 (by omega)

/-- **The one-degree-short form from the `C2` and `C3` inputs.** -/
theorem rangeModelRatAcyclic3_of_C2_C3 (hC2 : Work.StemsB.C2RatSphereRange)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.RatHurewicz.RangeModelRatAcyclic3 :=
  rangeModelRatAcyclic3_of_rangeModelRatAcyclic (rangeModelRatAcyclic_of_C2_C3 hC2 hC3)

/-- **The one-degree-short form from the odd free-top `C2` interface and `C3`.**  This is the
sharpest recorded reduction of the second input of the STEMS contract: no even-side `C2`
obligation appears (`Work.StemsB.C2RatSphereRange_of_C2oddFree`). -/
theorem rangeModelRatAcyclic3_of_C2oddFree (c : ℕ) (hC2 : Work.Stems.Engine.C2oddFree c)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.RatHurewicz.RangeModelRatAcyclic3 :=
  rangeModelRatAcyclic3_of_C2_C3 (Work.StemsB.C2RatSphereRange_of_C2oddFree c hC2) hC3

/-- **The one-degree-short form from the odd free-top `C2` interface and `serreC3FiniteOne`.** -/
theorem rangeModelRatAcyclic3_of_C2odd_C3one (c : ℕ) (hC2 : Work.Stems.Engine.C2oddFree c)
    (hC3one : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num : 0 < 1) X pt → Work.Serre.RatAcyclic X) :
    Work.RatHurewicz.RangeModelRatAcyclic3 :=
  rangeModelRatAcyclic3_of_rangeModelRatAcyclic (rangeModelRatAcyclic_of_C2odd_C3one c hC2 hC3one)

end

end Work.Stems
