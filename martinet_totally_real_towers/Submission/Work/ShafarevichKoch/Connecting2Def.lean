import Mathlib
import Submission.Work.ShafarevichKoch.connecting2

/-!
# `Work.ShafarevichKoch.Connecting2Def` -- the third connecting map, as a function

`connecting2.lean` proves the *existence* of the additive connecting map
`δ² : H²(G,C) →+ H³(G,A)` of a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules,
together with its computation on the class of a `2`-cocycle `z` of `C` from *any* cochain lift
`u` of `z`: the `A`-valued `3`-cocycle `w` with `f ∘ w = d²u` represents `δ²[z]`.

This module fixes a *name* for that map (`connecting2Map`) by choice, and records the computation
rule (`connecting2Map_spec`), so that the exactness statements in degrees `2` and `3`
(`Work.ShafarevichKoch.exact_H2_C`, `Work.ShafarevichKoch.exact_H3_A`) and the cardinality count of
the `ℤ`-power sequence (`Work.ShafarevichKoch.CountZ`) can be stated about it.

## Main declarations

* `Work.ShafarevichKoch.connecting2Map`;
* `Work.ShafarevichKoch.connecting2Map_spec`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-- **The third connecting map** `δ² : H²(G,C) →+ H³(G,A)` of a short exact sequence
`0 → A → B → C → 0` of discrete `G`-modules; `Work.ShafarevichKoch.connecting2` produces one. -/
noncomputable def connecting2Map (S : CoeffSES G A B C) : H2 G C →+ H3 G A :=
  Classical.choose (connecting2 S)

/-- **The computation rule for `δ²`**: if `u` is a cochain lift of the `2`-cocycle `z` (i.e.
`S.g ∘ u = z`), then `δ²[z]` is represented by the `3`-cocycle `w` with `S.f ∘ w = d²u`. -/
theorem connecting2Map_spec (S : CoeffSES G A B C) :
    ∀ (z : Z2 G C) (u : Cochain2 G B),
      (∀ p : G × G, S.g (u p) = (z : Cochain2 G C) p) →
      ∃ w : Z3 G A, H3.mk w = connecting2Map S (H2.mk z) ∧
        (∀ p : G × G × G, S.f ((w : G × G × G → A) p) = d2Fun (u : G × G → B) p) :=
  Classical.choose_spec (connecting2 S)

end Work.ShafarevichKoch
