import Mathlib
import Submission.Work.Stems.c2FreeClauses
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2OddStepLocal
import Submission.Work.Stems.c2OddBase
import Submission.Work.StemsB.C2_of_odd
import Submission.Work.Stems.rangeModelRatAcyclic3
import Submission.Work.Serre.serreE3a
import Submission.Work.StemsB.contractTwo
import Submission.Work.Drive.Interfaces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free-top `C2` layer, assembled

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md` and `C2ODD_STEP_STATE.md` §4.)*

`Work.Stems.Engine.C2oddFree c` — a range model of `K(ℤ,n)` (`n` odd) is rationally `Sⁿ` through
degree `N - c·n` — is proved here from

* `Work.Serre.SerreE3a` (the mapping theorem, **proved** in the tree),
* `Work.Serre.SerreE3b` (the Gysin/periodicity, a hypothesis of the `C2` layer: it is the one
  remaining SERRE-side input of the even step), and
* the level-`1` base clause (`Work.Stems.oddClauseOne` with `Work.Stems.bottomCellOne`).

## The mutual induction, run level by level

The even step (`Work.Stems.evenStepLocal`, from `c2evenFree_of_c2oddFree`) reads: the even clause at
level `j` follows from the odd clause at level `2j-1` (the loop space `ΩX` is a range model of
`K(ℤ,2j-1)`).  The odd step (`Work.Stems.oddStepLocal`, from `c2oddFree_of_c2evenFree`) reads: the
odd clause at level `2j+1` follows from the even clause at level `j`.  Composing, the even clause at
level `j` follows from the even clause at level `j-1`, so the two interfaces are proved by an
ordinary strong induction on the level, with the level-`1` clause as the base.

Both steps are *degree-lossless* in the allowance `c`, so the only loss of the whole induction is
the one in the base clause, where `d < N - c` is weakened to `d ≤ N`; `c = 3` absorbs it.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The mutual induction of the free-top `C2` layer.**  From the level-`1` clause (any allowance
`c`), the mapping theorem `SerreE3a` and the Gysin statement `SerreE3b`, both interfaces hold. -/
theorem c2evenFree_and_c2oddFree (c : ℕ) (hE3a : Work.Serre.SerreE3a)
    (hE3b : Work.Serre.SerreE3b) (hbase : ∀ N : ℕ, OddClause c 1 (by norm_num) N) :
    Work.Stems.Engine.C2evenFree c ∧ Work.Stems.Engine.C2oddFree c := by
  -- the even clauses, at every level `j ≥ 1`, by strong induction on the level
  have hE : ∀ (j : ℕ) (hj : 1 ≤ j), ∀ N : ℕ, EvenClause c j hj N := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj N
      rcases eq_or_lt_of_le hj with h1 | h2
      · subst h1
        exact evenStepLocal c hE3b 1 (by omega) 1 (by omega) hbase N
      · have hjm1 : 1 ≤ j - 1 := by omega
        have hstep : ∀ M : ℕ, OddClause c (2 * (j - 1) + 1) (by omega) M :=
          fun M => oddStepLocal c hE3a (j - 1) hjm1 (ih (j - 1) (by omega) hjm1) M
        exact evenStepLocal c hE3b j hj (2 * (j - 1) + 1) (by omega) hstep N
  refine ⟨?_, ?_⟩
  · rw [c2evenFree_iff]
    exact fun j hj N => hE j hj N
  · rw [c2oddFree_iff]
    intro n hn hodd N
    obtain ⟨j, rfl⟩ := hodd
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      exact hbase N
    · exact oddStepLocal c hE3a j hj1 (hE j hj1) N

/-- **The odd free-top `C2` interface**, from `SerreE3a`, `SerreE3b` and the level-`1` clause. -/
theorem c2oddFree_of_base (c : ℕ) (hE3a : Work.Serre.SerreE3a) (hE3b : Work.Serre.SerreE3b)
    (hbase : ∀ N : ℕ, OddClause c 1 (by norm_num) N) :
    Work.Stems.Engine.C2oddFree c :=
  (c2evenFree_and_c2oddFree c hE3a hE3b hbase).2

/-- **The odd free-top `C2` interface for the allowance `c = 3`**, from `SerreE3a` and `SerreE3b`
alone: the level-`1` clause is supplied by `Work.Stems.bottomCellOne` +
`Work.Stems.oddClauseOne`, whose sharp bound `d ≤ N` absorbs the `3`. -/
theorem c2oddFree_three (hE3a : Work.Serre.SerreE3a) (hE3b : Work.Serre.SerreE3b) :
    Work.Stems.Engine.C2oddFree 3 := by
  refine c2oddFree_of_base 3 hE3a hE3b (fun N => ?_)
  intro X tX pt hX
  letI : TopologicalSpace X := tX
  obtain ⟨hgen, hvan⟩ := oddClauseOne X pt N hX (bottomCellOne X pt N hX)
  exact ⟨hgen, fun d hd0 hdN hdn => hvan d hd0 (by omega) hdn⟩

/-- **`C2` in fixed-top form** (`Work.StemsB.C2RatSphereRange`): a range model of `K(ℤ,k)` through
degree `N ≥ 2k-1` is rationally `S^k` below degree `2k`. -/
theorem c2RatSphereRange (hE3a : Work.Serre.SerreE3a) (hE3b : Work.Serre.SerreE3b) :
    Work.StemsB.C2RatSphereRange :=
  Work.StemsB.C2RatSphereRange_of_C2oddFree 3 (c2oddFree_three hE3a hE3b)


/-- **`C2` in fixed-top form, from `SerreE3b` alone**: the mapping theorem `SerreE3a` is
`Work.Serre.serreE3a`, proved in the tree, so the only hypothesis is the Gysin/periodicity
statement. -/
theorem c2RatSphereRange_of_E3b (hE3b : Work.Serre.SerreE3b) : Work.StemsB.C2RatSphereRange :=
  c2RatSphereRange Work.Serre.serreE3a hE3b

/-- **The STEMS contract's second input, from `SerreE3b` and C3**: the rational homology of the
range models of `K(ℤ,k)` (`C2`, this area) together with the rational acyclicity of the range models
of `K(A,k)` for finite `A` (`C3`, area SERRE) give the one-degree-short form
`Work.RatHurewicz.RangeModelRatAcyclic3` consumed by `Work.Stems.stableStemsTorsion_of_serre3`. -/
theorem rangeModelRatAcyclic3_of_E3b_C3 (hE3b : Work.Serre.SerreE3b)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.RatHurewicz.RangeModelRatAcyclic3 :=
  rangeModelRatAcyclic3_of_C2_C3 (c2RatSphereRange_of_E3b hE3b) hC3

/-- **The STEMS contract from `SerreE3b` and C3** — the *sharpest* reduction, on the
**corrected K5** of area STEMSB (`Submission/Work/StemsB/contractTwo.lean`: the tree's
`Work.Serre.SerreExactRangeCorrected` carries the hypothesis `1 ≤ b`, which area STEMSB refutes with
the universal cover `ℝ → S¹`; the corrected `2 ≤ b` form is proved there and the S3 chain is ported
to it, so **K5 is not an input**).  The two genuine inputs left are

* `Work.Serre.SerreE3b` — the Gysin/periodicity of a rational spherical fibration in the range given
  by the fibre (area SERRE), and
* `Work.StemsB.C3FiniteTwo` — range models of `K(A,k)`, `A` finite, are rationally acyclic (area
  SERRE, through `Work.Serre.serreC3FiniteOne`),

and everything in between — this area's `C2` layer, `Work.Serre.serreE3a`, the corrected K5, the
rational Hurewicz machinary of area RATHUREWICZ — is proved. -/
theorem stableStemsTorsion_of_E3b_C3 (hE3b : Work.Serre.SerreE3b)
    (hC3 : Work.StemsB.C3FiniteTwo) : Work.Drive.StableStemsTorsion :=
  Work.StemsB.stableStemsTorsion_via_two
    (rangeModelRatAcyclic_of_C2odd_C3 3 (c2oddFree_three Work.Serre.serreE3a hE3b) hC3)

end

end Work.Stems
