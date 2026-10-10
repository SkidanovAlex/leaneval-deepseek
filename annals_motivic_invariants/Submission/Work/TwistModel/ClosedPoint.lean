/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Corrected
import Submission.Work.TwistModel.closedPoint_resDeg_eq_one_of_hasRatPoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A closed point of residue degree `1` gives corrected rational divisors of every degree

The corrected predicate `Work.TwistModel.HasRatDivisorOfDegreeClosed` selects closed points, so a
single closed point of residue degree `1` produces a rational divisor of degree `1`
(`Finsupp.single x 1`) and, by additivity, of every degree `n`.  The hypothesis "a closed point of
residue degree `1`" is supplied by `Work.TwistModel.closedPoint_resDeg_eq_one_of_hasRatPoint` (the
image of a section of `C ↘ Spec 𝕜` is closed with residue field `𝕜`) or, for `ℙ¹_𝕜`, concretely by
`Work.TwistModel.closedPoint_resDeg_one_projectiveSpace_one`.  This is the corrected counterpart of
the (false) `Work.TwistModel.hasRatDivisorOfDegree_one_of_hasRatPoint`: a `𝕜`-rational point *does*
give rational divisors of all degrees, once the support condition is the intended one.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **A closed point of residue degree `1` gives corrected rational divisors of every degree.** -/
theorem hasRatDivisorOfDegreeClosed_of_closedPoint_resDeg_one {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))]
    (h : ∃ x : C, IsClosed ({x} : Set C) ∧ Work.Arithmetic.resDeg 𝕜 x = 1) (n : ℕ) :
    HasRatDivisorOfDegreeClosed 𝕜 C n := by
  obtain ⟨x, hx, hdeg⟩ := h
  have hone : HasRatDivisorOfDegreeClosed 𝕜 C 1 := by
    refine ⟨Finsupp.single x 1, ?_, ?_⟩
    · intro y hy
      have : y = x := Finset.mem_singleton.mp (Finsupp.support_single_subset hy)
      rwa [this]
    · rw [Finsupp.sum_single_index (by simp), hdeg]
      norm_num
  induction n with
  | zero => simpa using hasRatDivisorOfDegreeClosed_zero 𝕜 C
  | succ k ih =>
    have := ih.add hone
    simpa using this

/-- **A `𝕜`-rational point gives corrected rational divisors of every degree** — the corrected
counterpart of the (false) `Work.TwistModel.hasRatDivisorOfDegree_one_of_hasRatPoint`. -/
theorem hasRatDivisorOfDegreeClosed_of_hasRatPoint {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))] (h : Work.Arithmetic.HasRatPoint 𝕜 C) (n : ℕ) :
    HasRatDivisorOfDegreeClosed 𝕜 C n :=
  hasRatDivisorOfDegreeClosed_of_closedPoint_resDeg_one
    (closedPoint_resDeg_eq_one_of_hasRatPoint h) n

end

end Work.TwistModel
