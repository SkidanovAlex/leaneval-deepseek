/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle for `H²(·, μ_p)`: local triviality and its level-wise form

This is the first module of the `NK.HasseTwist` chapter, the part of the Neukirch–Uchida
development that discharges the *Hasse principle* input

`NK.BrauerTwist.Sha2Vanishing p K K' κ κ'`

in the coefficient-correct (`μ_p`-twisted) form.  It is the twisted counterpart of
`Submission/Work/HassePrinciple/Defs.lean`, which does the same for the *trivial* coefficient
module `Z/p` (the form that is false for odd `p`, see `Submission/Work/BrauerHasse/README.md`).

The object of study is the localisation map

`H2Twist.loc p U : H²(U, μ_p) ⟶ ∏_A LocalH2Twist p U A`

(`Submission/Work/BrauerTwist/Profinite.lean`), the product running over the places `A` of `K'`
over the finite primes of `K`.  The Hasse principle is the statement that this map has trivial
kernel:

`NK.BrauerTwist.Sha2Vanishing p K K' κ κ'`.

Since `H2Twist p U` and `LocalH2Twist p U A` are *filtered colimits* (over the finite Galois
intermediate fields `L` of `K'/K`), the statement can be checked level by level, and that is what
this module sets up:

* `locTrivial p U x` — `x` has vanishing localisation at every place;
* `levelLocTrivial p U L a` — the level class `a` has vanishing level-wise localisation
  `locLevel p U A L a` at every place;
* `levelLocVanishing p U L a` — at every place, the level class `a` dies after inflation to a
  (place-dependent) larger finite level; this is the exact translation of `locTrivial` into level
  language;
* `LevelForm p K K' κ κ'` — the *level-wise Hasse principle*: a level class that dies locally at
  every place is already the zero class of the colimit.

## Main results

* `NK.HasseTwist.loc_ofLevel_eq_zero_iff` — the localisation of a level class vanishes at
  the place `A` if and only if the level class dies after inflation to a larger level;
* `NK.HasseTwist.levelLocVanishing_iff` — the above, uniformly in the places;
* `NK.HasseTwist.sha2Vanishing_of_levelForm`,
  `NK.HasseTwist.levelForm_of_sha2Vanishing` — the two directions of the equivalence of
  `Sha2Vanishing` with `LevelForm`.
-/

import Submission.NK.BrauerTwist.Profinite
import Submission.NK.BrauerTwist.Hasse

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

section Trivial

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Local triviality -/

/-- **Local triviality of a class of `H²(U, μ_p)`.**  The class `x` has vanishing localisation at
every place of `K'` over a finite prime of `K`. -/
def locTrivial (p : ℕ) (U : Subgroup Gal(K'/K)) (x : H2Twist p U) : Prop :=
  ∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0

/-- **Level-wise local triviality.**  A class of the finite level `L` has vanishing level-wise
localisation `locLevel` at every place of `K'` over a finite prime of `K`. -/
def levelLocTrivial (p : ℕ) (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : Prop :=
  ∀ A : OverFinitePrime K K', (locLevel p U A.1 L) a = 0

/-- **Level-wise vanishing of the localisations, in the local colimit.**  For every place `A`, the
level class `a` dies after inflation `localLevelMap` to some larger finite Galois level (which may
depend on `A`).  This is the exact level-wise translation of `locTrivial` of the corresponding
class of the colimit `H2Twist`. -/
def levelLocVanishing (p : ℕ) (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : Prop :=
  ∀ A : OverFinitePrime K K', ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
    (localLevelMap p U A.1 h) ((locLevel p U A.1 L) a) = 0

variable (p : ℕ) {U : Subgroup Gal(K'/K)}

/-- The zero class of a local cumlimit is represented at the bottom level. -/
lemma LocalH2Twist.ofLevel_zero (A : ValuationSubring K')
    (M : FiniteGaloisIntermediateField K K') :
    LocalH2Twist.ofLevel p U A M (0 : LocalLevelH2 p U A M) = 0 := by
  have h := LocalH2Twist.ofLevel_localLevelMap (p := p) (U := U) (A := A)
    (h := (bot_le : (⊥ : FiniteGaloisIntermediateField K K') ≤ M))
    (a := (0 : LocalLevelH2 p U A ⊥))
  rw [map_zero] at h
  exact h

/-- **The zero class of the twisted colimit** is represented by the zero class of any level. -/
lemma H2Twist.ofLevel_zero (M : FiniteGaloisIntermediateField K K') :
    H2Twist.ofLevel p U M (0 : LevelH2 p U M) = 0 := by
  show H2Twist.ofLevel p U M (0 : LevelH2 p U M) = H2Twist.ofLevel p U ⊥ (0 : LevelH2 p U ⊥)
  rw [← H2Twist.ofLevel_levelMap (p := p) (U := U)
    (h := (bot_le : (⊥ : FiniteGaloisIntermediateField K K') ≤ M))
    (0 : LevelH2 p U ⊥), map_zero]

lemma locTrivial_zero : locTrivial p U (0 : H2Twist p U) :=
  fun A => H2Twist.loc_zero p U A

lemma levelLocTrivial_zero (L : FiniteGaloisIntermediateField K K') :
    levelLocTrivial p U L (0 : LevelH2 p U L) :=
  fun _ => map_zero _

/-- Local triviality at level `L` implies the colimit form of local vanishing. -/
lemma levelLocVanishing_of_levelLocTrivial {L : FiniteGaloisIntermediateField K K'}
    {a : LevelH2 p U L} (h : levelLocTrivial p U L a) : levelLocVanishing p U L a :=
  fun A => ⟨L, le_rfl, by rw [h A, map_zero]⟩

/-! ## The level-wise criterion for the vanishing of the localisation -/

/-- **The localisation of a level class vanishes iff the class dies after inflation.**  This is the
working form of the definition of `H2Twist.loc` as a map of filtered colimits: the target of the
localisation is the local colimit `LocalH2Twist`, in which two classes are equal exactly when they
agree after inflation to a common finite level (`LocalH2Twist.ofLevel_eq_iff`), and the class
represented at the bottom level is the zero class (`LocalH2Twist.ofLevel_zero`). -/
lemma loc_ofLevel_eq_zero_iff (A : OverFinitePrime K K')
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    H2Twist.loc p U (H2Twist.ofLevel p U L a) A = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        (localLevelMap p U A.1 h) ((locLevel p U A.1 L) a) = 0 := by
  rw [H2Twist.loc_ofLevel_apply]
  constructor
  · intro h
    have h0 : LocalH2Twist.ofLevel p U A.1 L ((locLevel p U A.1 L) a) =
        LocalH2Twist.ofLevel p U A.1 (⊥ : FiniteGaloisIntermediateField K K')
          (0 : LocalLevelH2 p U A.1 ⊥) := h
    obtain ⟨M, h₁, h₂, he⟩ :=
      (LocalH2Twist.ofLevel_eq_iff (p := p) (K := K) (K' := K') (U := U) (A := A.1)
        (L := L) (L' := ⊥) ((locLevel p U A.1 L) a) (0 : LocalLevelH2 p U A.1 ⊥)).mp h0
    refine ⟨M, h₁, ?_⟩
    rw [he]
    simp
  · rintro ⟨M, h, he⟩
    rw [← LocalH2Twist.ofLevel_localLevelMap (p := p) (U := U) (A := A.1) h
      ((locLevel p U A.1 L) a), he]
    exact LocalH2Twist.ofLevel_zero (p := p) (U := U) A.1 M

/-- **The level-wise criterion, uniformly in the places.** -/
lemma levelLocVanishing_iff (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    levelLocVanishing p U L a ↔
      ∀ A : OverFinitePrime K K', H2Twist.loc p U (H2Twist.ofLevel p U L a) A = 0 :=
  forall_congr' fun A => (loc_ofLevel_eq_zero_iff (p := p) (U := U) A L a).symm

end Trivial

section LevelForm

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The level-wise Hasse principle.**  A finite-level class of `H²(U, μ_p)` whose localisations
vanish at every place of `K'` over a finite prime of `K` is already zero as a class of the colimit
`H²(U, μ_p)`.  This is the assertion that the filtered colimit of the localisation maps has trivial
kernel, formulated at the level of the finite levels. -/
def LevelForm (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      levelLocVanishing p U L a → H2Twist.ofLevel p U L a = 0

/-- **The level-wise Hasse principle implies `Sha2Vanishing`.**  A locally trivial class `x` of
`H²(U, μ_p)` is represented at a finite level, and at that level its localisations vanish by
`loc_ofLevel_eq_zero_iff`. -/
theorem sha2Vanishing_of_levelForm (p : ℕ)
    (h : LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U _hU _hκ x hx
  obtain ⟨L, a, rfl⟩ := H2Twist.ofLevel_surjective (p := p) (U := U) x
  exact h U _hU _hκ L a ((levelLocVanishing_iff (p := p) (U := U) L a).mpr hx)

/-- **`Sha2Vanishing` implies the level-wise Hasse principle.**  This is the direction in which the
colimit description is used: the localisations of the level class `a` vanish, hence the class of
`a` in the colimit is locally trivial, hence zero by `Sha2Vanishing`. -/
theorem levelForm_of_sha2Vanishing (p : ℕ)
    (h : Sha2Vanishing (K := K) (K' := K') p κ κ') :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  intro U hU hκ L a ha
  exact h U hU hκ (H2Twist.ofLevel p U L a)
    ((levelLocVanishing_iff (p := p) (U := U) L a).mp ha)

/-- **`Sha2Vanishing` is exactly the level-wise Hasse principle.** -/
theorem sha2Vanishing_iff_levelForm (p : ℕ) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' ↔
      LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  ⟨levelForm_of_sha2Vanishing p, sha2Vanishing_of_levelForm p⟩

end LevelForm

end NK.HasseTwist
