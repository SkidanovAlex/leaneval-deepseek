/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `H²(⊥, μ_p)` is a point

The twisted cohomology `NK.BrauerTwist.H2Twist p U = H²(U, μ_p)` of a closed subgroup
`U ≤ Gal(K'/K)` is defined (`Submission/Work/BrauerTwist/Profinite.lean`) as the filtered colimit of
the *level* cohomologies

`NK.BrauerTwist.LevelH2 p U L = H²(U ⧸ (U ⊓ Gal(K'/L)), μ_p(L))`.

For `U = ⊥` the level *group* is `⊥ ⧸ (Gal(K'/L) ⊓ ⊥)`, a quotient of the trivial group, hence
itself trivial; the higher cohomology of the trivial group vanishes
(`isZero_groupCohomology_succ_of_subsingleton`), so every level is a point and therefore so is the
colimit:

`NK.Indecomposed.subsingleton_h2Twist_bot : Subsingleton (H2Twist p ⊥)`.

This is the reason why the cardinality hypothesis `p ≤ Nat.card (H2Twist p V)` in
`NK.Indecomposed.RankData` has to be restricted to the *non-trivial* local groups
`V = H ⊓ D_A`: for `V = ⊥` — which happens exactly when the prime is decomposed in `K'/K` — the
twisted cohomology is a point and the hypothesis `p ≤ Nat.card (H2Twist p ⊥)` fails.  See
`Submission/Work/Indecomposed/Defs.lean` and the README of the chapter.

## Contents

* `NK.Indecomposed.subsingleton_colim_of_subsingleton_objs` — a level system whose level data are
  all singletons has a singleton colimit (the bookkeeping half of the argument, independent of
  cohomology);
* `NK.Indecomposed.subsingleton_h2Twist_of_subsingleton_carrier` — the cohomological half, in the
  general form for a subgroup `U` with `Subsingleton ↥U`, of which the requested statement is the
  case `U = ⊥`;
* `NK.Indecomposed.subsingleton_h2Twist_bot` — the requested statement.
-/

import Mathlib
import Submission.NK.BrauerTwist.Profinite

universe u

open CategoryTheory

namespace NK.Indecomposed

/-- **A level system all of whose level data are singletons has a singleton colimit.**

This is the bookkeeping half of `NK.Indecomposed.subsingleton_h2Twist_bot`: it is a statement
about `NK.BrauerTwist.LevelSystem` alone, with no cohomology in it.

Given `x = ofLevel L a` and `y = ofLevel L' b`, the two classes are equal as soon as
`map le_sup_left a = map le_sup_right b` on the common dominating level `L ⊔ L'`, which holds
because the level data are singletons (`LevelSystem.ofLevel_eq_iff`). -/
lemma subsingleton_colim_of_subsingleton_objs {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] {S : NK.BrauerTwist.LevelSystem K K'}
    (h : ∀ L, Subsingleton (S.obj L)) : Subsingleton S.Colim := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨L, a, rfl⟩ := S.ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := S.ofLevel_surjective y
  rw [S.ofLevel_eq_iff]
  exact ⟨L ⊔ L', le_sup_left, le_sup_right, Subsingleton.elim _ _⟩

/-- **The twisted cohomology of a trivial subgroup is a point.**  If `U ≤ Gal(K'/K)` is trivial
(`Subsingleton ↥U`), then `H²(U, μ_p)` is a point.

The level group `U ⧸ (U ⊓ Gal(K'/L))` is then a quotient of a trivial group, hence trivial, and
the second cohomology of the trivial group vanishes
(`isZero_groupCohomology_succ_of_subsingleton`); so every level is a point, and the colimit of
points is a point (`subsingleton_colim_of_subsingleton_objs`). -/
lemma subsingleton_h2Twist_of_subsingleton_carrier {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} [Subsingleton ↥U] :
    Subsingleton (NK.BrauerTwist.H2Twist (K := K) (K' := K') p U) := by
  refine subsingleton_colim_of_subsingleton_objs
    (S := NK.BrauerTwist.twistSystem (K := K) (K' := K') p U) ?_
  intro L
  change Subsingleton (NK.BrauerTwist.LevelH2 (K := K) (K' := K') p U L)
  rw [NK.BrauerTwist.LevelH2]
  exact ModuleCat.subsingleton_of_isZero
    (isZero_groupCohomology_succ_of_subsingleton
      (NK.BrauerTwist.levelRep (K := K) (K' := K') p U L) 1)

theorem subsingleton_h2Twist_bot {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) :
    Subsingleton (NK.BrauerTwist.H2Twist (K := K) (K' := K') p (⊥ : Subgroup Gal(K'/K))) :=
  subsingleton_h2Twist_of_subsingleton_carrier (K := K) (K' := K') p

end NK.Indecomposed
