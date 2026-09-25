/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle for `H²(·, Z/p)`: local triviality and its level-wise form

This is the first module of the `NK.HassePrinciple` chapter, the part of the
Neukirch–Uchida development that discharges the *Hasse principle* input
`NK.BrauerHasse.Sha2Vanishing`.

The object of study is the localisation map

`H2Profinite.loc p U : H²(U, Z/p) ⟶ ∏_{A} LocalH2 p U A`

(`NK.BrauerHasse.Profinite.H2Profinite.loc`), the product running over the places `A` of `K'`
over the finite primes of `K`.  The Hasse principle is the statement that this map has trivial
kernel:

`NK.BrauerHasse.Sha2Vanishing p K K' κ κ'`.

Since `H2Profinite p U` and `LocalH2 p U A` are *filtered colimits* (over the finite Galois
intermediate fields `L` of `K'/K`), the statement can be checked level by level, and that is what
this module sets up:

* `locTrivial p U x` — `x` has vanishing localisation at every place;
* `levelLocTrivial p U L a` — the level class `a` has vanishing level-wise localisation
  `locLevel p U A L a` at every place;
* `levelLocVanishing p U L a` — at every place, the level class `a` dies after inflation to a
  (place-dependent) larger finite level; this is the exact translation of `locTrivial` into level
  language (the localisation in the colimit `LocalH2` is `ofLevel`-then-inflate, so its vanishing
  is witnessed at some finite level);
* `LevelForm p K K' κ κ'` — the *level-wise Hasse principle*: a level class that dies locally at
  every place is already the zero class of the colimit.

## Main results

* `NK.HassePrinciple.loc_ofLevel_eq_zero_iff` — the localisation of a level class vanishes at
  the place `A` if and only if the level class dies after inflation to a larger level;
* `NK.HassePrinciple.levelLocVanishing_iff` — the above, uniformly in the places;
* `NK.HassePrinciple.sha2Vanishing_of_levelForm`,
  `NK.HassePrinciple.levelForm_of_sha2Vanishing` — the two directions of the equivalence of
  `Sha2Vanishing` with `LevelForm`.
-/

import Submission.NK.BrauerHasse.Hasse
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.BrauerHasse.local_ofLevel_eq_iff
import Submission.NK.BrauerHasse.ofLevel_zero
import Submission.NK.BrauerHasse.local_ofLevel_zero

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

section Trivial

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Local triviality -/

/-- **Local triviality of a class of `H²(U, Z/p)`.**  The class `x` has vanishing localisation at
every place of `K'` over a finite prime of `K`. -/
def locTrivial (p : ℕ) (U : Subgroup Gal(K'/K)) (x : H2Profinite p U) : Prop :=
  ∀ A : OverFinitePrime K K', H2Profinite.loc p U x A = 0

/-- **Level-wise local triviality.**  A class of the finite level `L` has vanishing level-wise
localisation `locLevel` at every place of `K'` over a finite prime of `K`. -/
def levelLocTrivial (p : ℕ) (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : Prop :=
  ∀ A : OverFinitePrime K K', (locLevel p U A.1 L) a = 0

/-- **Level-wise vanishing of the localisations, in the local colimit.**  For every place `A`, the
level class `a` dies after inflation `localLevelMap` to some larger finite Galois level (which may
depend on `A`).  This is the exact level-wise translation of `locTrivial` of the corresponding
class of the colimit `H2Profinite`. -/
def levelLocVanishing (p : ℕ) (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : Prop :=
  ∀ A : OverFinitePrime K K', ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
    (localLevelMap p U A.1 h) ((locLevel p U A.1 L) a) = 0

variable (p : ℕ) {U : Subgroup Gal(K'/K)}

lemma locTrivial_zero : locTrivial p U (0 : H2Profinite p U) :=
  fun A => H2Profinite.loc_zero p U A

lemma levelLocTrivial_zero (L : FiniteGaloisIntermediateField K K') :
    levelLocTrivial p U L (0 : LevelH2 p U L) :=
  fun _ => map_zero _

/-- Local triviality at level `L` implies the colimit form of local vanishing. -/
lemma levelLocVanishing_of_levelLocTrivial {L : FiniteGaloisIntermediateField K K'}
    {a : LevelH2 p U L} (h : levelLocTrivial p U L a) : levelLocVanishing p U L a :=
  fun A => ⟨L, le_rfl, by rw [h A, map_zero]⟩

/-! ## The level-wise criterion for the vanishing of the localisation -/

/-- **The localisation of a level class vanishes iff the class dies after inflation.**  This is the
working form of the definition of `H2Profinite.loc` as a map of filtered colimits: the target of
the localisation is the local colimit `LocalH2`, in which two classes are equal exactly when they
agree after inflation to a common finite level (`local_ofLevel_eq_iff`), and the class coming from
the bottom level is the zero class (`local_ofLevel_zero`). -/
lemma loc_ofLevel_eq_zero_iff (A : OverFinitePrime K K')
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    H2Profinite.loc p U (H2Profinite.ofLevel L a) A = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        (localLevelMap p U A.1 h) ((locLevel p U A.1 L) a) = 0 := by
  rw [H2Profinite.loc_ofLevel_apply]
  constructor
  · intro h
    have h0 : LocalH2.ofLevel p U A.1 L ((locLevel p U A.1 L) a) =
        LocalH2.ofLevel p U A.1 (⊥ : FiniteGaloisIntermediateField K K')
          (0 : LocalLevelH2 p U A.1 ⊥) := by
      rw [local_ofLevel_zero (K := K) (K' := K') p A.1 ⊥]
      exact h
    obtain ⟨M, h₁, h₂, he⟩ :=
      (local_ofLevel_eq_iff p (U := U) (A := A.1) (L := L) (L' := ⊥)
        ((locLevel p U A.1 L) a) (0 : LocalLevelH2 p U A.1 ⊥)).mp h0
    refine ⟨M, h₁, ?_⟩
    rw [he]
    simp
  · rintro ⟨M, h, he⟩
    rw [← LocalH2.ofLevel_levelMap (p := p) (U := U) (A := A.1) h ((locLevel p U A.1 L) a),
      he, local_ofLevel_zero (K := K) (K' := K') p A.1 M]

/-- **The level-wise criterion, uniformly in the places.** -/
lemma levelLocVanishing_iff (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    levelLocVanishing p U L a ↔
      ∀ A : OverFinitePrime K K', H2Profinite.loc p U (H2Profinite.ofLevel L a) A = 0 :=
  forall_congr' fun A => (loc_ofLevel_eq_zero_iff (K := K) (K' := K') p (U := U) A L a).symm

lemma levelLocTrivial_iff (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    levelLocTrivial p U L a ↔
      ∀ A : OverFinitePrime K K', (locLevel p U A.1 L) a = 0 :=
  Iff.rfl

end Trivial

section LevelForm

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The level-wise Hasse principle.**  A finite-level class of `H²(U, Z/p)` whose localisations
vanish at every place of `K'` over a finite prime of `K` is already zero as a class of the colimit
`H²(U, Z/p)`.  This is the assertion that the filtered colimit of the localisation maps has
trivial kernel, formulated at the level of the finite levels. -/
def LevelForm (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      levelLocVanishing p U L a → H2Profinite.ofLevel L a = 0

/-- **The level-wise Hasse principle implies `Sha2Vanishing`.**  A locally trivial class `x` of
`H²(U, Z/p)` is represented at a finite level, and at that level its localisations vanish by
`loc_ofLevel_eq_zero_iff`. -/
theorem sha2Vanishing_of_levelForm (p : ℕ)
    (h : LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U _hU _hκ x hx
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective (p := p) (U := U) x
  exact h U _hU _hκ L a ((levelLocVanishing_iff (K := K) (K' := K') p (U := U) L a).mpr hx)

/-- **`Sha2Vanishing` implies the level-wise Hasse principle.**  This is the direction in which the
colimit description is used: the localisations of the level class `a` vanish, hence the class of
`a` in the colimit is locally trivial, hence zero by `Sha2Vanishing`. -/
theorem levelForm_of_sha2Vanishing (p : ℕ)
    (h : Sha2Vanishing (K := K) (K' := K') p κ κ') :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  exact h U hU hκ (H2Profinite.ofLevel L a)
    ((levelLocVanishing_iff (K := K) (K' := K') p (U := U) L a).mp ha)

/-- **`Sha2Vanishing` is exactly the level-wise Hasse principle.** -/
theorem sha2Vanishing_iff_levelForm (p : ℕ) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' ↔
      LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  ⟨levelForm_of_sha2Vanishing p, sha2Vanishing_of_levelForm p⟩

end LevelForm

end NK.HassePrinciple
