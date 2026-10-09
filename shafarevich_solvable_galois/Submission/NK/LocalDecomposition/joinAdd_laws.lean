/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelian group laws of the addition `H2Profinite.joinAdd`

`NK.BrauerHasse.H2Profinite p U` is the profinite cohomology `H²(U, Z/p)` of a closed subgroup
`U ≤ Gal(K'/K)`, defined as the filtered colimit of the finite levels `LevelH2 p U L` along the
inflation maps.  In `Submission/Work/BrauerHasse/exists_add.lean` the addition of two classes
living on different levels is constructed (`H2Profinite.joinAdd`): two classes represented at
levels `L` and `L'` are inflated to the join `L ⊔ L'` and added there
(`H2Profinite.joinAdd_ofLevel`), and the result is independent of the chosen dominating level
(`H2Profinite.joinAdd_ofLevel_le`).

The present file proves that this operation satisfies the laws of a commutative group:

* `joinAdd_comm` — commutativity;
* `joinAdd_assoc` — associativity;
* `joinAdd_zero` — the class `0` is a (left) unit;
* `joinAdd_neg` — every class has an additive inverse,

and packages them as the requested statement `NK.LocalDecomposition.joinAdd_laws`.

Since every element of the colimit is represented by a class of a finite level
(`H2Profinite.ofLevel_surjective`), all four laws are proved on representatives, where they are
the corresponding laws of the abelian group `LevelH2 p U M` of a suitable common dominating
finite Galois intermediate field `M` — for commutativity and associativity one takes
`M = L ⊔ L'` and `M = (L ⊔ L') ⊔ L''`, for the unit the bottom level `⊥` represents `0`, and for
the inverse the negation of the level class, lifted through `H2Profinite.lift`.

The two computation lemmas `joinAdd3_left` and `joinAdd3_right` express the value of a sum of
three classes on a common level `M`, with the two possible bracketings; they differ exactly by
the associativity of the addition of the level `M`.
-/

import Mathlib
import Submission.NK.BrauerHasse.exists_add
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.BrauerHasse.ofLevel_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

universe u

namespace NK.LocalDecomposition

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {p : ℕ} {U : Subgroup Gal(K'/K)}

/-! ## Sums of three classes on a common dominating level -/

/-- **A sum of three classes, bracketed on the left, computed on a common dominating level.**
For a finite Galois intermediate field `M` dominating the three levels `L`, `L'`, `L''`, the sum
`(x + y) + z` of the classes `x`, `y`, `z` is the class at level `M` of the sum of the three
inflations, bracketed on the left. -/
private lemma joinAdd3_left {L L' L'' M : FiniteGaloisIntermediateField K K'}
    (hL : L ≤ M) (hL' : L' ≤ M) (hL'' : L'' ≤ M)
    (x : LevelH2 p U L) (y : LevelH2 p U L') (z : LevelH2 p U L'') :
    H2Profinite.joinAdd p U
        (H2Profinite.joinAdd p U (H2Profinite.ofLevel L x) (H2Profinite.ofLevel L' y))
        (H2Profinite.ofLevel L'' z)
      = H2Profinite.ofLevel M
          (((levelMap p (U := U) hL) x + (levelMap p (U := U) hL') y)
            + (levelMap p (U := U) hL'') z) := by
  rw [H2Profinite.joinAdd_ofLevel (p := p) (U := U) (L := L) (L' := L') x y]
  rw [H2Profinite.joinAdd_ofLevel_le (M := M) (h₁ := sup_le hL hL') (h₂ := hL'')]
  congr 1
  rw [map_add]
  rw [levelMap_trans_apply (le_sup_left : L ≤ L ⊔ L') (sup_le hL hL') x,
      levelMap_trans_apply (le_sup_right : L' ≤ L ⊔ L') (sup_le hL hL') y]

/-- **A sum of three classes, bracketed on the right, computed on a common dominating level.**
For a finite Galois intermediate field `M` dominating the three levels `L`, `L'`, `L''`, the sum
`x + (y + z)` of the classes `x`, `y`, `z` is the class at level `M` of the sum of the three
inflations, bracketed on the right. -/
private lemma joinAdd3_right {L L' L'' M : FiniteGaloisIntermediateField K K'}
    (hL : L ≤ M) (hL' : L' ≤ M) (hL'' : L'' ≤ M)
    (x : LevelH2 p U L) (y : LevelH2 p U L') (z : LevelH2 p U L'') :
    H2Profinite.joinAdd p U (H2Profinite.ofLevel L x)
        (H2Profinite.joinAdd p U (H2Profinite.ofLevel L' y) (H2Profinite.ofLevel L'' z))
      = H2Profinite.ofLevel M
          ((levelMap p (U := U) hL) x
            + ((levelMap p (U := U) hL') y + (levelMap p (U := U) hL'') z)) := by
  rw [H2Profinite.joinAdd_ofLevel (p := p) (U := U) (L := L') (L' := L'') y z]
  rw [H2Profinite.joinAdd_ofLevel_le (M := M) (h₁ := hL) (h₂ := sup_le hL' hL'')]
  congr 1
  rw [map_add]
  rw [levelMap_trans_apply (le_sup_left : L' ≤ L' ⊔ L'') (sup_le hL' hL'') y,
      levelMap_trans_apply (le_sup_right : L'' ≤ L' ⊔ L'') (sup_le hL' hL'') z]

/-! ## The additive inverse -/

/-- **The additive inverse in `H²(U, Z/p)`.**  The compatible family
`L ↦ a ↦ ofLevel L (-a)` (compatible because the inflation maps are morphisms of `Z/p`-modules)
descends to the colimit: `joinNeg p U x` is represented by the negative of any level class
representing `x`. -/
private noncomputable def joinNeg (p : ℕ) (U : Subgroup Gal(K'/K)) :
    H2Profinite p U → H2Profinite p U :=
  H2Profinite.lift (p := p) (U := U) (fun L a => H2Profinite.ofLevel L (-a)) (by
    intro L L' h a
    rw [← map_neg]
    exact H2Profinite.ofLevel_levelMap (p := p) (U := U) h (-a))

/-! ## The group laws -/

/-- **`H²(U, Z/p)` is a commutative group under `H2Profinite.joinAdd`.**

All four laws are checked on representatives: an element of the colimit is a class `ofLevel L a`
of a finite level, and the value of a sum on representatives is computed on any common dominating
level (`H2Profinite.joinAdd_ofLevel_le`), where the corresponding law of the abelian group
`LevelH2 p U M` applies verbatim.

* commutativity: both sides are computed at the level `L ⊔ L'`, where they differ by
  `add_comm`;
* associativity: both sides are computed at the level `(L ⊔ L') ⊔ L''` (`joinAdd3_left`,
  `joinAdd3_right`), where they differ by `add_assoc`;
* the unit: `0` is the class of the bottom level `⊥`, and the sum with the zero class of a
  dominating level is computed at the level of the other summand;
* the inverse: `joinNeg p U x` is represented by the negative of any representative of `x`,
  and the sum of the two classes on the common level of the representative is `0`. -/
theorem joinAdd_laws {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) :
    (∀ a b : NK.BrauerHasse.H2Profinite p U,
        NK.BrauerHasse.H2Profinite.joinAdd p U a b = NK.BrauerHasse.H2Profinite.joinAdd p U b a) ∧
      (∀ a b c : NK.BrauerHasse.H2Profinite p U,
        NK.BrauerHasse.H2Profinite.joinAdd p U
            (NK.BrauerHasse.H2Profinite.joinAdd p U a b) c =
          NK.BrauerHasse.H2Profinite.joinAdd p U a
            (NK.BrauerHasse.H2Profinite.joinAdd p U b c)) ∧
      (∀ a : NK.BrauerHasse.H2Profinite p U,
        NK.BrauerHasse.H2Profinite.joinAdd p U a 0 = a) ∧
      (∀ a : NK.BrauerHasse.H2Profinite p U,
        ∃ b : NK.BrauerHasse.H2Profinite p U,
          NK.BrauerHasse.H2Profinite.joinAdd p U a b = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Commutativity: compute both sides on the join of the two levels.
    intro a b
    obtain ⟨L, x, rfl⟩ := H2Profinite.ofLevel_surjective a
    obtain ⟨L', y, rfl⟩ := H2Profinite.ofLevel_surjective b
    rw [H2Profinite.joinAdd_ofLevel_le (M := L ⊔ L') (h₁ := le_sup_left) (h₂ := le_sup_right),
      H2Profinite.joinAdd_ofLevel_le (M := L ⊔ L') (h₁ := le_sup_right) (h₂ := le_sup_left)]
    rw [add_comm]
  · -- Associativity: compute both sides on the common upper bound `(L ⊔ L') ⊔ L''`.
    intro a b c
    obtain ⟨L, x, rfl⟩ := H2Profinite.ofLevel_surjective a
    obtain ⟨L', y, rfl⟩ := H2Profinite.ofLevel_surjective b
    obtain ⟨L'', z, rfl⟩ := H2Profinite.ofLevel_surjective c
    rw [joinAdd3_left (M := (L ⊔ L') ⊔ L'')
          (hL := (le_sup_left : L ≤ L ⊔ L').trans le_sup_left)
          (hL' := (le_sup_right : L' ≤ L ⊔ L').trans le_sup_left)
          (hL'' := le_sup_right) x y z,
      joinAdd3_right (M := (L ⊔ L') ⊔ L'')
          (hL := (le_sup_left : L ≤ L ⊔ L').trans le_sup_left)
          (hL' := (le_sup_right : L' ≤ L ⊔ L').trans le_sup_left)
          (hL'' := le_sup_right) x y z]
    rw [add_assoc]
  · -- The unit: `0` is the class of the bottom level, which every level dominates.
    intro a
    obtain ⟨L, x, rfl⟩ := H2Profinite.ofLevel_surjective a
    rw [show (0 : H2Profinite p U) = H2Profinite.ofLevel ⊥ (0 : LevelH2 p U ⊥) from rfl]
    rw [H2Profinite.joinAdd_ofLevel_le (M := L) (h₁ := (le_rfl : L ≤ L)) (h₂ := (bot_le : ⊥ ≤ L))]
    rw [map_zero, add_zero]
    exact H2Profinite.ofLevel_levelMap (p := p) (U := U) (le_rfl : L ≤ L) x
  · -- The inverse: the lift of the level-wise negation.
    intro a
    obtain ⟨L, x, rfl⟩ := H2Profinite.ofLevel_surjective a
    refine ⟨joinNeg p U (H2Profinite.ofLevel L x), ?_⟩
    show H2Profinite.joinAdd p U (H2Profinite.ofLevel L x) (H2Profinite.ofLevel L (-x)) = 0
    rw [H2Profinite.joinAdd_ofLevel_self, add_neg_cancel]
    exact ofLevel_zero L

end NK.LocalDecomposition
