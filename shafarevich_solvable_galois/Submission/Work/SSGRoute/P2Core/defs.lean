import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.H9.swHistKExists_proved
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` §4 recursion: the place set of a stage

`Work.SSGRoute.P2Core.recPlaceSet` is the place set `T_m` of Schmidt--Wingberg's §4 recursion at the
stage that follows the construction of the classes `b_0, …, b_{m-1}` with escape primes
`Q_0, …, Q_{m-1}` (`NOTE_node_s37_p2_assembly_plan.md` §1):

    `T_m := krep K (kleadReps K S ∪ ⋃_{l < m} kleadReps K {Q_l})`,

i.e. one representative per `K`-conjugacy class of places met by the `k`-classes of the places of `S`
and of the escape primes already constructed.

It is a definition rather than a `let` inside the statements of the recursion because the recursion's
statements mention it repeatedly, and because the `Finset` operations (`∪`, `Finset.biUnion`) need a
`DecidableEq (ValuationSubring Ω)` instance that one does not want as an explicit binder of every
statement.
-/

open scoped Pointwise

namespace Work.SSGRoute.P2Core

/-- **The place set `T_m` of the recursion at stage `m`.** -/
noncomputable def recPlaceSet {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) {m : ℕ} (Q : Fin m → ValuationSubring Ω) :
    Finset (ValuationSubring Ω) := by
  classical
  exact Work.SSGRoute.H9.krep K (Work.SSGRoute.ZDataMup.kleadReps K S ∪
    (Finset.univ.biUnion (fun l : Fin m => Work.SSGRoute.ZDataMup.kleadReps K {Q l})))

end Work.SSGRoute.P2Core
