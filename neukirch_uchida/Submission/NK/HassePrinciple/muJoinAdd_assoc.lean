/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Associativity of `muJoinAdd` on the `μ_p` colimit

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

`NK.HassePrinciple.muJoinAdd p V` is the addition on the colimit
`NK.HassePrinciple.MuColim p V = colim_L H²(LevelGroup V L, μ_p(L))` built in
`MuColimAdd.lean`: two classes represented at the levels `L` and `L'` are summed by inflating both
to the join `L ⊔ L'` and adding there (`muJoinAdd_ofLevel`).

This file proves that the operation is **associative**.  The two auxiliary lemmas evaluate a
left- and a right-associated three-fold sum of level classes at an *arbitrary* common upper bound
`M` of the three levels; associativity then follows by comparing both associations at
`M = (L₁ ⊔ L₂) ⊔ L₃` and using associativity of the addition *inside* the level
(`add_assoc`, available because each level carries an `AddCommGroup` structure).

The point that makes the computation run without any bookkeeping about the inclusion proofs is
that the transition maps of the level system are insensitive to the proof of the inclusion
(`NK.BrauerTwist.LevelSystem.map_congr`, `muLevelSystem_map_congr_apply`): in Lean's kernel any
two proofs of the same proposition are definitionally equal, so the composites
`le_sup_left.trans h` and the given `h'` are automatically identified by `rfl`.
-/

import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Evaluation of a left-associated three-fold sum of level classes at a common upper bound.**
For `M` dominating the three levels `L₁, L₂, L₃`, the left-associated sum of the three classes is
the class, at level `M`, of the sum of their inflations to `M`. -/
lemma muJoinAdd_three_left (p : ℕ) (V : Subgroup Gal(K'/K))
    {L₁ L₂ L₃ M : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ M) (h₂ : L₂ ≤ M) (h₃ : L₃ ≤ M)
    (a : (muLevelSystem p V).obj L₁) (b : (muLevelSystem p V).obj L₂)
    (c : (muLevelSystem p V).obj L₃) :
    muJoinAdd p V (muJoinAdd p V (MuColim.ofLevel p V L₁ a) (MuColim.ofLevel p V L₂ b))
        (MuColim.ofLevel p V L₃ c) =
      MuColim.ofLevel p V M
        ((muLevelSystem p V).map h₁ a + (muLevelSystem p V).map h₂ b
          + (muLevelSystem p V).map h₃ c) := by
  have h₁₂ : L₁ ⊔ L₂ ≤ M := sup_le h₁ h₂
  rw [muJoinAdd_ofLevel (p := p) (V := V) L₁ L₂ a b,
    muJoinAdd_ofLevel_le (p := p) (V := V) h₁₂ h₃]
  refine congrArg (MuColim.ofLevel p V M) ?_
  rw [muLevelSystem_map_add]
  rw [muLevelSystem_map_trans_apply, muLevelSystem_map_trans_apply]

/-- **Evaluation of a right-associated three-fold sum of level classes at a common upper bound.**
The right-associated counterpart of `muJoinAdd_three_left`. -/
lemma muJoinAdd_three_right (p : ℕ) (V : Subgroup Gal(K'/K))
    {L₁ L₂ L₃ M : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ M) (h₂ : L₂ ≤ M) (h₃ : L₃ ≤ M)
    (a : (muLevelSystem p V).obj L₁) (b : (muLevelSystem p V).obj L₂)
    (c : (muLevelSystem p V).obj L₃) :
    muJoinAdd p V (MuColim.ofLevel p V L₁ a)
        (muJoinAdd p V (MuColim.ofLevel p V L₂ b) (MuColim.ofLevel p V L₃ c)) =
      MuColim.ofLevel p V M
        ((muLevelSystem p V).map h₁ a
          + ((muLevelSystem p V).map h₂ b + (muLevelSystem p V).map h₃ c)) := by
  have h₂₃ : L₂ ⊔ L₃ ≤ M := sup_le h₂ h₃
  rw [muJoinAdd_ofLevel (p := p) (V := V) L₂ L₃ b c,
    muJoinAdd_ofLevel_le (p := p) (V := V) h₁ h₂₃]
  refine congrArg (MuColim.ofLevel p V M) ?_
  rw [muLevelSystem_map_add]
  rw [muLevelSystem_map_trans_apply, muLevelSystem_map_trans_apply]

/-- **Associativity of the joins `⊔` in the level lattice**, in the form the final comparison of
the two associations uses: `(L₁ ⊔ L₂) ⊔ L₃` dominates each of `L₁, L₂, L₃`. -/
lemma le_sup_sup_level {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} :
    L₁ ≤ (L₁ ⊔ L₂) ⊔ L₃ ∧ L₂ ≤ (L₁ ⊔ L₂) ⊔ L₃ ∧ L₃ ≤ (L₁ ⊔ L₂) ⊔ L₃ :=
  ⟨le_trans le_sup_left le_sup_left, le_trans le_sup_right le_sup_left, le_sup_right⟩

theorem muJoinAdd_assoc {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (x y z : NK.HassePrinciple.MuColim p V) :
    NK.HassePrinciple.muJoinAdd p V (NK.HassePrinciple.muJoinAdd p V x y) z =
      NK.HassePrinciple.muJoinAdd p V x (NK.HassePrinciple.muJoinAdd p V y z) := by
  obtain ⟨L₁, a, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  obtain ⟨L₂, b, rfl⟩ := (muLevelSystem p V).ofLevel_surjective y
  obtain ⟨L₃, c, rfl⟩ := (muLevelSystem p V).ofLevel_surjective z
  rw [muJoinAdd_three_left p V (le_trans le_sup_left le_sup_left)
      (le_trans le_sup_right le_sup_left) le_sup_right a b c,
    muJoinAdd_three_right p V (le_trans le_sup_left le_sup_left)
      (le_trans le_sup_right le_sup_left) le_sup_right a b c]
  rw [add_assoc]

end NK.HassePrinciple
