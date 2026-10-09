/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twisted profinite cohomology `H²(U, μ_p)`

This file instantiates the generic filtered-colimit machinery of
`Submission/Work/BrauerTwist/System.lean` with the twisted coefficient system of
`Submission/Work/BrauerTwist/Basic.lean`: for a closed subgroup `U ≤ Gal(K'/K)` of an absolute
Galois group, `H²(U, μ_p)` is the filtered colimit of the *level* cohomologies

`NK.BrauerTwist.LevelH2 p U L = H²(U ⧸ (U ∩ Gal(K'/L)), μ_p(L))`

along the transition maps `levelMap`.  This is the classical presentation of the continuous
cohomology `H²(U, μ_p) = colim_L H²(U ⧸ (U ∩ Gal(K'/L)), μ_p(L))` (Serre, *Galois Cohomology*,
I.2.2, Prop. 8); that the cohomology has to be taken over the level *group* and not over the
profinite group `U` is explained in the module docstring of `Basic.lean` and in `README.md` §1.
In contrast to
`Submission/Work/BrauerHasse/Profinite.lean` — which computes `H²(U, Z/p)` with the *trivial*
module — the coefficients here are the `p`-th roots of unity, acted on through the cyclotomic
character.

## Main definitions

* `NK.BrauerTwist.twistSystem p U` — the level system of the twisted theory;
* `NK.BrauerTwist.H2Twist p U` — `H²(U, μ_p)`, with `ofLevel`, `lift`, `ofLevel_surjective`,
  `ofLevel_eq_iff`;
* `NK.BrauerTwist.OverFinitePrime`, `NK.BrauerTwist.LocalH2Twist`,
  `NK.BrauerTwist.LocalProduct` — the places over the finite primes and the local cohomologies;
* `NK.BrauerTwist.H2Twist.loc` — the localisation map `H²(U, μ_p) → ∏_A H²(U ⊓ D_A, μ_p)`.
-/

import Submission.NK.BrauerTwist.Basic
import Submission.NK.BrauerTwist.System
import Submission.NK.BrauerTwist.levelMap_comp
import Submission.NK.BrauerTwist.levelMap_refl
import Submission.NK.BrauerTwist.localLevelMap_comp
import Submission.NK.BrauerTwist.localLevelMap_refl
import Submission.NK.BrauerTwist.levelMap_locLevel_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option autoImplicit false

universe u

namespace NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level system of the twisted coefficients -/

/-- **The level system of the twisted theory**: at the level `L` the datum is the level cohomology
`H²(U, μ_p(L))`, and the transition map is the map induced by the coefficient inclusion
`μ_p(L) ↪ μ_p(L')`. -/
noncomputable def twistSystem (p : ℕ) (U : Subgroup Gal(K'/K)) : LevelSystem.{u} K K' where
  obj L := LevelH2 p U L
  map := fun L L' h a => levelMap p U h a
  map_refl L x := by
    rw [levelMap_refl p U L, ModuleCat.id_apply]
  map_comp h₁ h₂ x := by
    have h := congrArg (fun (f : LevelH2 p U _ ⟶ LevelH2 p U _) => f x)
      (levelMap_comp p U h₁ h₂)
    simpa [CategoryTheory.comp_apply] using h

/-- **The twisted profinite cohomology `H²(U, μ_p)`** of a closed subgroup `U ≤ Gal(K'/K)`. -/
noncomputable abbrev H2Twist (p : ℕ) (U : Subgroup Gal(K'/K)) : Type u :=
  (twistSystem (K := K) (K' := K') p U).Colim

/-- The structure map from a finite level into `H²(U, μ_p)`. -/
noncomputable abbrev H2Twist.ofLevel (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) : H2Twist (K := K) (K' := K') p U :=
  (twistSystem (K := K) (K' := K') p U).ofLevel L a

/-- **Every element of `H²(U, μ_p)` comes from a finite level.** -/
lemma H2Twist.ofLevel_surjective (p : ℕ) (U : Subgroup Gal(K'/K))
    (x : H2Twist (K := K) (K' := K') p U) :
    ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      H2Twist.ofLevel p U L a = x :=
  (twistSystem (K := K) (K' := K') p U).ofLevel_surjective x

/-- An element of a smaller level and its inflation to a larger level define the same class. -/
lemma H2Twist.ofLevel_levelMap (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (a : LevelH2 p U L) :
    H2Twist.ofLevel p U L' (levelMap p U h a) = H2Twist.ofLevel p U L a :=
  (twistSystem (K := K) (K' := K') p U).ofLevel_map h a

/-- **The universal property of `H²(U, μ_p)`.** -/
noncomputable abbrev H2Twist.lift (p : ℕ) (U : Subgroup Gal(K'/K)) {β : Sort*}
    (f : ∀ L : FiniteGaloisIntermediateField K K', LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' (levelMap p U h a) = f L a) :
    H2Twist (K := K) (K' := K') p U → β :=
  (twistSystem (K := K) (K' := K') p U).lift f hf

@[simp]
lemma H2Twist.lift_ofLevel (p : ℕ) (U : Subgroup Gal(K'/K)) {β : Sort*}
    (f : ∀ L : FiniteGaloisIntermediateField K K', LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' (levelMap p U h a) = f L a)
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    H2Twist.lift p U f hf (H2Twist.ofLevel p U L a) = f L a := rfl

/-- Two maps out of `H²(U, μ_p)` agreeing on all levels are equal. -/
lemma H2Twist.lift_unique (p : ℕ) (U : Subgroup Gal(K'/K)) {β : Sort*}
    (f : ∀ L : FiniteGaloisIntermediateField K K', LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' (levelMap p U h a) = f L a)
    (g : H2Twist (K := K) (K' := K') p U → β)
    (hg : ∀ L a, g (H2Twist.ofLevel p U L a) = f L a) :
    g = H2Twist.lift p U f hf :=
  (twistSystem (K := K) (K' := K') p U).lift_unique f hf g hg

/-- **Two classes of `H²(U, μ_p)` coincide if and only if they already coincide on a common
dominating finite level.** -/
theorem H2Twist.ofLevel_eq_iff (p : ℕ) (U : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (a : LevelH2 p U L) (b : LevelH2 p U L') :
    H2Twist.ofLevel p U L a = H2Twist.ofLevel p U L' b ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h₁ : L ≤ M) (h₂ : L' ≤ M),
        levelMap p U h₁ a = levelMap p U h₂ b :=
  (twistSystem (K := K) (K' := K') p U).ofLevel_eq_iff a b

/-! ## The local cohomology and the localisation map -/

/-- The places of `K'` over a finite prime of `K`: the valuation subrings of `K'` whose restriction
to `K` is not everything.  (This is the `FinitePlace` vocabulary of
`Submission.NeukirchUchida.PlaceSystem`; it coincides with the definition of the sibling area
`Submission/Work/BrauerHasse/Profinite.lean`.) -/
def OverFinitePrime (K : Type u) (K' : Type u) [Field K] [Field K'] [Algebra K K'] : Type u :=
  {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤}

/-- The local level system at a place: the level cohomologies `H²(U ⊓ D_A, μ_p(L))` with the local
transition maps. -/
noncomputable def localTwistSystem (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    LevelSystem.{u} K K' where
  obj L := LocalLevelH2 p U A L
  map := fun L L' h a => localLevelMap p U A h a
  map_refl L x := by
    rw [localLevelMap_refl p U A L, ModuleCat.id_apply]
  map_comp h₁ h₂ x := by
    have h := congrArg (fun (f : LocalLevelH2 p U A _ ⟶ LocalLevelH2 p U A _) => f x)
      (localLevelMap_comp p U A h₁ h₂)
    simpa [CategoryTheory.comp_apply] using h

/-- **The local cohomology `H²(U ⊓ D_A, μ_p)`** at a place `A`: the colimit of the local level
cohomologies. -/
noncomputable abbrev LocalH2Twist (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    Type u :=
  (localTwistSystem (K := K) (K' := K') p U A).Colim

/-- The structure map from a local level into the local colimit. -/
noncomputable abbrev LocalH2Twist.ofLevel (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (a : LocalLevelH2 p U A L) : LocalH2Twist (K := K) (K' := K') p U A :=
  (localTwistSystem (K := K) (K' := K') p U A).ofLevel L a

/-- An element of a smaller local level and its inflation define the same class. -/
lemma LocalH2Twist.ofLevel_localLevelMap (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (a : LocalLevelH2 p U A L) :
    LocalH2Twist.ofLevel p U A L' (localLevelMap p U A h a) =
      LocalH2Twist.ofLevel p U A L a :=
  (localTwistSystem (K := K) (K' := K') p U A).ofLevel_map h a

/-- **Every element of a local cohomology comes from a finite local level.** -/
lemma LocalH2Twist.ofLevel_surjective (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (x : LocalH2Twist (K := K) (K' := K') p U A) :
    ∃ (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L),
      LocalH2Twist.ofLevel p U A L a = x :=
  (localTwistSystem (K := K) (K' := K') p U A).ofLevel_surjective x

/-- **Two classes of a local cohomology coincide if and only if they coincide on a common
dominating finite level.** -/
theorem LocalH2Twist.ofLevel_eq_iff (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (a : LocalLevelH2 p U A L)
    (b : LocalLevelH2 p U A L') :
    LocalH2Twist.ofLevel p U A L a = LocalH2Twist.ofLevel p U A L' b ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h₁ : L ≤ M) (h₂ : L' ≤ M),
        localLevelMap p U A h₁ a = localLevelMap p U A h₂ b :=
  (localTwistSystem (K := K) (K' := K') p U A).ofLevel_eq_iff a b

/-- The product of the local cohomologies over all places of `K'` above the finite primes of
`K`. -/
def LocalProduct (p : ℕ) (K K' : Type u) [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (U : Subgroup Gal(K'/K)) : Type u :=
  ∀ A : OverFinitePrime K K', LocalH2Twist p U A.1

/-- **The localisation map** `H²(U, μ_p) → ∏_A H²(U ⊓ D_A, μ_p)`, from the twisted profinite
cohomology to the product of the local cohomologies at all places over the finite primes of `K`.

It is defined through the universal property of the colimit: on the class of a finite level it is
the level-wise restriction map `locLevel`, which is compatible with the transition maps by
`NK.BrauerTwist.levelMap_locLevel_apply`. -/
noncomputable def H2Twist.loc (p : ℕ) (U : Subgroup Gal(K'/K)) :
    H2Twist p U → LocalProduct p K K' U :=
  H2Twist.lift p U
    (fun L a A => LocalH2Twist.ofLevel p U A.1 L (locLevel p U A.1 L a))
    (by
      intro L L' h a
      funext A
      rw [levelMap_locLevel_apply]
      exact LocalH2Twist.ofLevel_localLevelMap p U A.1 h (locLevel p U A.1 L a))

/-- The computation rule for the localisation map: the localisation of a class represented at a
finite level is the colimit class of its level-wise localisation. -/
@[simp]
lemma H2Twist.loc_ofLevel_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) (A : OverFinitePrime K K') :
    H2Twist.loc p U (H2Twist.ofLevel p U L a) A =
      LocalH2Twist.ofLevel p U A.1 L (locLevel p U A.1 L a) := rfl

noncomputable instance instZeroH2Twist (p : ℕ) (U : Subgroup Gal(K'/K)) :
    Zero (H2Twist (K := K) (K' := K') p U) :=
  ⟨H2Twist.ofLevel p U ⊥ 0⟩

noncomputable instance instZeroLocalH2Twist (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') : Zero (LocalH2Twist (K := K) (K' := K') p U A) :=
  ⟨LocalH2Twist.ofLevel p U A ⊥ 0⟩

/-- The distinguished zero of the twisted colimit is localised to the distinguished zero. -/
lemma H2Twist.loc_zero (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K') :
    H2Twist.loc p U (0 : H2Twist (K := K) (K' := K') p U) A = 0 := by
  show H2Twist.loc p U (H2Twist.ofLevel p U ⊥ (0 : LevelH2 p U ⊥)) A = 0
  rw [H2Twist.loc_ofLevel_apply, map_zero]
  rfl

end NK.BrauerTwist
