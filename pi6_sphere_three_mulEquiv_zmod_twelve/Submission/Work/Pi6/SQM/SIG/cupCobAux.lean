import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
import Submission.Work.Pi6.SQM.SIG.cup1mZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup2ZeroLeft
import Submission.Work.Pi6.SQM.SIG.cup3ZeroLeft
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

/-!
# Coboundaries of the mixed terms `A ∪ᵢ s + s ∪_{i-1} s`

The cochain-level identity behind the compatibility of the cohomology suspension `σ` with the
Steenrod squares: if `A` is a mod-2 cocycle and `s` is a cochain with `δs = A`, then

  `δ((A ∪ᵢ s) + (s ∪_{i-1} s)) = A ∪ᵢ A`,

an immediate consequence of the coboundary formulas for `∪ᵢ` (`Cup1Cob`, `Cup2Cob`, `Cup3Cob`)
together with the Leibniz rule (`cupLeibniz`) in the `i = 1` case: in every case the "cross"
terms `A ∪_{i-1} s` and `s ∪_{i-1} A` come out twice, and `δA = 0` kills the remaining terms.

The degree identifications in the hypothesis Props are *definitionally* trivial at the numerals
used here, so each instance of a `Prop` is restated in "cast-free" form by a term-level
transcription (`:= H`), after which the computation is pure algebra over `𝔽₂`.
-/

noncomputable section

/-- In a module over `𝔽₂`, every element is its own additive inverse: `x + x = 0`. -/
theorem cochainAddSelf {X : SSet} {n : ℕ} (x : Cochain F2 X n) : x + x = 0 := by
  have h2 : (2 : F2) = 0 := by simpa using CharP.cast_eq_zero (ZMod 2) 2
  rw [← two_smul F2 x, h2, zero_smul]

/-- The algebraic cancellation at the end of each of the five conjuncts: in an `𝔽₂`-module,
`(a + b + 0 + c) + (z + z + a + b) = c`. -/
theorem cupCobAux_cancel4 {X : SSet} {n : ℕ} (a b c z : Cochain F2 X n) :
    (a + b + 0 + c) + (z + z + a + b) = c := by
  rw [show (a + b + 0 + c) + (z + z + a + b) = (a + a) + (b + b) + (z + z) + c from by abel]
  rw [cochainAddSelf a, cochainAddSelf b, cochainAddSelf z]
  abel

/-- The same cancellation without a `z`-term: `(a + b + 0 + c) + (a + b) = c`. -/
theorem cupCobAux_cancel3 {X : SSet} {n : ℕ} (a b c : Cochain F2 X n) :
    (a + b + 0 + c) + (a + b) = c := by
  rw [show (a + b + 0 + c) + (a + b) = (a + a) + (b + b) + c from by abel]
  rw [cochainAddSelf a, cochainAddSelf b]
  abel

/-- Each conjunct is a mod-2 cochain identity: with `δA = 0` and `δs = A`, the sum
`A ∪ᵢ s + s ∪_{i-1} s` has coboundary `A ∪ᵢ A`.  Derive from `Cup1Cob`/`Cup2Cob`/`Cup3Cob`
(instances of `h1`/`h2`/`h3`) together with the library Leibniz rule
`Work.Cohomology.cupLeibniz` for `Work.Cohomology.cup`. -/
theorem cupCobAux (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) :
    (∀ (X : SSet) (A : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3)
      (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2)
      (_hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X A = 0)
      (_hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X s = A),
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X
          (Work.Pi6.SQ.cup1m X 3 2 A s + Work.Cohomology.cup Work.Pi6.SQ.F2 X s s) =
        Work.Pi6.SQ.cup1m X 3 3 A A) ∧
    (∀ (X : SSet) (A : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3)
      (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2)
      (_hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X A = 0)
      (_hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X s = A),
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X
          (Work.Pi6.SQ.cup2 X 3 2 A s + Work.Pi6.SQ.cup1m X 2 2 s s) =
        Work.Pi6.SQ.cup2 X 3 3 A A) ∧
    (∀ (X : SSet) (A : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 4)
      (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3)
      (_hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X A = 0)
      (_hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X s = A),
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X
          (Work.Pi6.SQ.cup2 X 4 3 A s + Work.Pi6.SQ.cup1m X 3 3 s s) =
        Work.Pi6.SQ.cup2 X 4 4 A A) ∧
    (∀ (X : SSet) (A : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 4)
      (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3)
      (_hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X A = 0)
      (_hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X s = A),
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X
          (Work.Pi6.SQM.cup3 X 4 3 A s + Work.Pi6.SQ.cup2 X 3 3 s s) =
        Work.Pi6.SQM.cup3 X 4 4 A A) ∧
    (∀ (X : SSet) (A : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 5)
      (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 4)
      (_hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X A = 0)
      (_hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X s = A),
      Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X
          (Work.Pi6.SQM.cup3 X 5 4 A s + Work.Pi6.SQ.cup2 X 4 4 s s) =
        Work.Pi6.SQM.cup3 X 5 5 A A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `i = 1`, `A ∈ C³`, `s ∈ C²`: the Leibniz rule supplies `δ(s ⌣ s)`
    intro X A s hA hs
    have H1 := h1 X 3 2 A s (by norm_num) (by norm_num)
    have H1' : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 2 A s) =
        Work.Cohomology.cup F2 X A s + Work.Cohomology.cup F2 X s A +
        Work.Pi6.SQ.cup1m X 4 2 (cochainDiff F2 X A) s +
        Work.Pi6.SQ.cup1m X 3 3 A (cochainDiff F2 X s) := H1
    have HL' : cochainDiff F2 X (Work.Cohomology.cup F2 X s s) =
        Work.Cohomology.cup F2 X (cochainDiff F2 X s) s + Work.Cohomology.cup F2 X s (cochainDiff F2 X s) := by
      have := cupLeibniz F2 X s s
      simpa using this
    change (cochainDiffLM F2 X 4) (Work.Pi6.SQ.cup1m X 3 2 A s + Work.Cohomology.cup F2 X s s) =
      Work.Pi6.SQ.cup1m X 3 3 A A
    rw [map_add, cochainDiffLM_apply, cochainDiffLM_apply, H1', HL', hA, hs, cup1mZeroLeft]
    exact cupCobAux_cancel3 _ _ _
  · -- `i = 2`, `A ∈ C³`, `s ∈ C²`: both `∪₁` and `∪₂` coboundary formulas
    intro X A s hA hs
    have H2 := h2 X 3 2 A s (by norm_num) (by norm_num)
    have H2' : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 3 2 A s) =
        Work.Pi6.SQ.cup1m X 3 2 A s + Work.Pi6.SQ.cup1m X 2 3 s A +
        Work.Pi6.SQ.cup2 X 4 2 (cochainDiff F2 X A) s +
        Work.Pi6.SQ.cup2 X 3 3 A (cochainDiff F2 X s) := H2
    have H1b := h1 X 2 2 s s (by norm_num) (by norm_num)
    have H1b' : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 2 2 s s) =
        Work.Cohomology.cup F2 X s s + Work.Cohomology.cup F2 X s s +
        Work.Pi6.SQ.cup1m X 3 2 (cochainDiff F2 X s) s +
        Work.Pi6.SQ.cup1m X 2 3 s (cochainDiff F2 X s) := H1b
    change (cochainDiffLM F2 X 3) (Work.Pi6.SQ.cup2 X 3 2 A s + Work.Pi6.SQ.cup1m X 2 2 s s) =
      Work.Pi6.SQ.cup2 X 3 3 A A
    rw [map_add, cochainDiffLM_apply, cochainDiffLM_apply, H2', H1b', hA, hs, cup2ZeroLeft]
    exact cupCobAux_cancel4 _ _ _ _
  · -- `i = 2`, `A ∈ C⁴`, `s ∈ C³`
    intro X A s hA hs
    have H2 := h2 X 4 3 A s (by norm_num) (by norm_num)
    have H2' : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 3 A s) =
        Work.Pi6.SQ.cup1m X 4 3 A s + Work.Pi6.SQ.cup1m X 3 4 s A +
        Work.Pi6.SQ.cup2 X 5 3 (cochainDiff F2 X A) s +
        Work.Pi6.SQ.cup2 X 4 4 A (cochainDiff F2 X s) := H2
    have H1b := h1 X 3 3 s s (by norm_num) (by norm_num)
    have H1b' : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 3 s s) =
        Work.Cohomology.cup F2 X s s + Work.Cohomology.cup F2 X s s +
        Work.Pi6.SQ.cup1m X 4 3 (cochainDiff F2 X s) s +
        Work.Pi6.SQ.cup1m X 3 4 s (cochainDiff F2 X s) := H1b
    change (cochainDiffLM F2 X 5) (Work.Pi6.SQ.cup2 X 4 3 A s + Work.Pi6.SQ.cup1m X 3 3 s s) =
      Work.Pi6.SQ.cup2 X 4 4 A A
    rw [map_add, cochainDiffLM_apply, cochainDiffLM_apply, H2', H1b', hA, hs, cup2ZeroLeft]
    exact cupCobAux_cancel4 _ _ _ _
  · -- `i = 3`, `A ∈ C⁴`, `s ∈ C³`: here the `∪₂`-formula is used twice
    intro X A s hA hs
    have H3 := h3 X 4 3 A s (by norm_num) (by norm_num)
    have H3' : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 3 A s) =
        Work.Pi6.SQ.cup2 X 4 3 A s + Work.Pi6.SQ.cup2 X 3 4 s A +
        Work.Pi6.SQM.cup3 X 5 3 (cochainDiff F2 X A) s +
        Work.Pi6.SQM.cup3 X 4 4 A (cochainDiff F2 X s) := H3
    have H2b := h2 X 3 3 s s (by norm_num) (by norm_num)
    have H2b' : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 3 3 s s) =
        Work.Pi6.SQ.cup1m X 3 3 s s + Work.Pi6.SQ.cup1m X 3 3 s s +
        Work.Pi6.SQ.cup2 X 4 3 (cochainDiff F2 X s) s +
        Work.Pi6.SQ.cup2 X 3 4 s (cochainDiff F2 X s) := H2b
    change (cochainDiffLM F2 X 4) (Work.Pi6.SQM.cup3 X 4 3 A s + Work.Pi6.SQ.cup2 X 3 3 s s) =
      Work.Pi6.SQM.cup3 X 4 4 A A
    rw [map_add, cochainDiffLM_apply, cochainDiffLM_apply, H3', H2b', hA, hs, cup3ZeroLeft]
    exact cupCobAux_cancel4 _ _ _ _
  · -- `i = 3`, `A ∈ C⁵`, `s ∈ C⁴`
    intro X A s hA hs
    have H3 := h3 X 5 4 A s (by norm_num) (by norm_num)
    have H3' : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 4 A s) =
        Work.Pi6.SQ.cup2 X 5 4 A s + Work.Pi6.SQ.cup2 X 4 5 s A +
        Work.Pi6.SQM.cup3 X 6 4 (cochainDiff F2 X A) s +
        Work.Pi6.SQM.cup3 X 5 5 A (cochainDiff F2 X s) := H3
    have H2b := h2 X 4 4 s s (by norm_num) (by norm_num)
    have H2b' : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 4 s s) =
        Work.Pi6.SQ.cup1m X 4 4 s s + Work.Pi6.SQ.cup1m X 4 4 s s +
        Work.Pi6.SQ.cup2 X 5 4 (cochainDiff F2 X s) s +
        Work.Pi6.SQ.cup2 X 4 5 s (cochainDiff F2 X s) := H2b
    change (cochainDiffLM F2 X 6) (Work.Pi6.SQM.cup3 X 5 4 A s + Work.Pi6.SQ.cup2 X 4 4 s s) =
      Work.Pi6.SQM.cup3 X 5 5 A A
    rw [map_add, cochainDiffLM_apply, cochainDiffLM_apply, H3', H2b', hA, hs, cup3ZeroLeft]
    exact cupCobAux_cancel4 _ _ _ _

end

end Work.Pi6.SQM.SIG
