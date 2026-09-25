/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# When does the structure map `ofLevel` of the colimit vanish?

Umbrella development: `Submission/Work/HassePrinciple/` (README §20).

Both `NK.BrauerHasse.H2Profinite` and the local colimit `NK.BrauerHasse.LocalH2` are
*quotients* of the disjoint union of the level cohomologies by the equivalence relation generated
by the inflation maps.  Consequently the structure map `ofLevel L` is **not** injective: a level
class can be non-zero at its own level and still be zero as a class of the colimit, because it may
be killed by inflation to a larger level.

This is the mechanism which resolves the apparent contradiction recorded in the chapter's notes
between the two facts

* `locLevel` (and hence the localisation of a *level* class) can be an isomorphism at a level
  (e.g. when the local level group happens to be the whole level group), so that a non-zero level
  class has non-zero level-wise localisation, while
* the classical localisation of the corresponding global class vanishes at that place
  (e.g. the quaternion class of `(-1,-1)` over `ℚ(√2)` at the place over `2`).

There is no contradiction: the localisation in the colimit is the class of the level-wise
localisation modulo the *local* inflation maps, and those are not injective either.  The two
statements below make this precise; they are the exact level-wise description of the vanishing of
`ofLevel`, and they are the tool which shows that "the class dies locally at some level"
(`levelLocVanishing`) is strictly weaker than "the level class is locally trivial at its own level"
(`levelLocTrivial`).

## Main results

* `NK.HassePrinciple.H2Profinite.ofLevel_eq_zero_iff` — a class of the colimit vanishes if and
  only if it is killed by inflation to some larger level;
* `NK.HassePrinciple.LocalH2.ofLevel_eq_zero_iff` — the same for the local colimits;
* `NK.HassePrinciple.levelLocVanishing_of_ofLevel_eq_zero` — the level-wise translation.
-/

import Submission.NK.HassePrinciple.Defs

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {p : ℕ} {U : Subgroup Gal(K'/K)}

/-- **The structure map of the colimit `H²(U, Z/p)` vanishes exactly on the classes killed by
inflation.**  A level class `a` represents the zero class of the colimit if and only if it dies
after inflation to some larger finite Galois level. -/
theorem H2Profinite.ofLevel_eq_zero_iff (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) :
    H2Profinite.ofLevel L a = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        (levelMap p (U := U) h) a = 0 := by
  constructor
  · intro h
    have h0 : H2Profinite.ofLevel L a =
        H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
          (0 : LevelH2 p U ⊥) := by
      rw [ofLevel_zero (K := K) (K' := K') (p := p) (U := U)
        (⊥ : FiniteGaloisIntermediateField K K')]
      exact h
    obtain ⟨M, h₁, _h₂, he⟩ :=
      (ofLevel_eq_iff (p := p) (U := U) a (0 : LevelH2 p U ⊥)).mp h0
    refine ⟨M, h₁, ?_⟩
    rw [he]
    simp
  · rintro ⟨M, h, he⟩
    rw [← H2Profinite.ofLevel_levelMap (p := p) (U := U) h a, he,
      ofLevel_zero (K := K) (K' := K') (p := p) (U := U) M]

/-- **The structure map of the local colimit vanishes exactly on the classes killed by the local
inflation.** -/
theorem LocalH2.ofLevel_eq_zero_iff (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (a : LocalLevelH2 p U A L) :
    LocalH2.ofLevel p U A L a = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        (localLevelMap p U A h) a = 0 := by
  constructor
  · intro h
    have h0 : LocalH2.ofLevel p U A L a =
        LocalH2.ofLevel p U A (⊥ : FiniteGaloisIntermediateField K K')
          (0 : LocalLevelH2 p U A ⊥) := by
      rw [local_ofLevel_zero (K := K) (K' := K') p (U := U) A
        (⊥ : FiniteGaloisIntermediateField K K')]
      exact h
    obtain ⟨M, h₁, _h₂, he⟩ :=
      (local_ofLevel_eq_iff (K := K) (K' := K') p (U := U) (A := A) (L := L)
        (L' := ⊥) a (0 : LocalLevelH2 p U A ⊥)).mp h0
    refine ⟨M, h₁, ?_⟩
    rw [he]
    simp
  · rintro ⟨M, h, he⟩
    rw [← LocalH2.ofLevel_levelMap (p := p) (U := U) (A := A) h a, he,
      local_ofLevel_zero (K := K) (K' := K') p (U := U) A M]

/-- **A level class represents the zero class of the colimit as soon as its localisations die at
every place.**  This is the direction of `levelLocVanishing_iff` which does not use the local
vanishing at the level itself: the local colimit kills the level-wise localisation at any level at
which the level class has been killed by inflation. -/
theorem levelLocVanishing_of_ofLevel_eq_zero (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) (h : H2Profinite.ofLevel L a = 0) :
    levelLocVanishing p U L a := by
  obtain ⟨M, hLM, hM⟩ := (H2Profinite.ofLevel_eq_zero_iff L a).mp h
  intro A
  refine ⟨M, hLM, ?_⟩
  show (localLevelMap p U A.1 hLM) ((locLevel p U A.1 L) a) = 0
  rw [← levelMap_locLevel_apply p U A.1 hLM a, hM, map_zero]

end NK.HassePrinciple
