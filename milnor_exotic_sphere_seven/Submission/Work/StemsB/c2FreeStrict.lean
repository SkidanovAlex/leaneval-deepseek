import Mathlib
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2OddStepLocal
import Submission.Work.Stems.c2FreeClauses
import Submission.Work.Stems.Engine.C2FreeTop
import Submission.Work.StemsB.gysinStrict

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free-top `C2` layer from the **strict** Gysin range

`Submission/Work/Stems/c2FreeMain.lean` runs the mutual induction of the free-top `C2` layer (the
even step `Work.Stems.evenStepLocal` from the odd clause, the odd step `Work.Stems.oddStepLocal`
from the even clause) from `SerreE3a`, `SerreE3b` and the level-`1` base clause.  By
`Submission/Work/StemsB/gysinStrict.lean` the even step consumes the Gysin isomorphism only in the
**strict** range `m + r + 1 ≤ N` for every allowance `c ≥ 1` (the boundary `m + r + 1 = N + 1` is
never reached; the hypothesis `1 ≤ c` is sharp).  This file mirrors that assembly with the *strict*
Gysin statement, so that

  `Work.StemsB.SerreE3bStrict → SerreE3a → (level-1 clause) → C2evenFree c ∧ C2oddFree c`

for every `c ≥ 1` — in particular for the `c = 3` used by `Work.Stems.c2oddFree_three`.

The even step is taken here as an explicit hypothesis `hStrict`, in exactly the shape of the port
`Work.StemsB.evenStepLocalStrict` (delegated to `Submission/Work/StemsB/evenStepLocalStrict.lean`);
instantiating it with that lemma (and `Work.StemsB.serreE3bStrict_of_serreE3b` for a full-range
proof) is a one-line change.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- **The free-top `C2` layer from the strict Gysin range.**  `hStrict` is the port of
`Work.Stems.evenStepLocal` to `SerreE3bStrict`. -/
theorem c2evenFree_and_c2oddFree_strict (c : ℕ) (hc : 1 ≤ c) (hE3a : Work.Serre.SerreE3a)
    (hStrict : ∀ (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : m = 2 * j - 1),
      (∀ M : ℕ, Work.Stems.OddClause c m (by omega) M) → ∀ N : ℕ, Work.Stems.EvenClause c j hj N)
    (hbase : ∀ N : ℕ, Work.Stems.OddClause c 1 (by norm_num) N) :
    Work.Stems.Engine.C2evenFree c ∧ Work.Stems.Engine.C2oddFree c := by
  have hE : ∀ (j : ℕ) (hj : 1 ≤ j), ∀ N : ℕ, Work.Stems.EvenClause c j hj N := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj N
      rcases eq_or_lt_of_le hj with h1 | h2
      · subst h1
        exact hStrict 1 (by omega) 1 (by omega) hbase N
      · have hjm1 : 1 ≤ j - 1 := by omega
        have hstep : ∀ M : ℕ, Work.Stems.OddClause c (2 * (j - 1) + 1) (by omega) M :=
          fun M => Work.Stems.oddStepLocal c hE3a (j - 1) hjm1 (ih (j - 1) (by omega) hjm1) M
        exact hStrict j hj (2 * (j - 1) + 1) (by omega) hstep N
  refine ⟨?_, ?_⟩
  · rw [Work.Stems.c2evenFree_iff]
    exact fun j hj N => hE j hj N
  · rw [Work.Stems.c2oddFree_iff]
    intro n hn hodd N
    obtain ⟨j, rfl⟩ := hodd
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      exact hbase N
    · exact Work.Stems.oddStepLocal c hE3a j hj1 (hE j hj1) N

#print axioms Work.StemsB.c2evenFree_and_c2oddFree_strict

end

end Work.StemsB
