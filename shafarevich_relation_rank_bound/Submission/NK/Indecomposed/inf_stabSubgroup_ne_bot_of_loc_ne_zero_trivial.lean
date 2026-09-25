/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A non-zero local component forces a non-trivial local group (trivial coefficients)

In the vocabulary of `Submission/Work/BrauerHasse/Profinite.lean` — the second cohomology
`H2Profinite p U = colim_L H²(U/(U ∩ Gal(K'/L)), Z/p)` with *trivial* coefficients — the
localisation `H2Profinite.loc p U x A` of a class at a place `A` over a finite prime of `K`
factors through the local group `U ⊓ D_A`, `D_A = stabSubgroup A.1` being the decomposition group
of `A`.

Here we record the trivial, but indispensable, consequence: **if the local group `U ⊓ D_A` is
trivial, then the whole local component of `x` vanishes.**  The reason is purely formal — every
local finite level group `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` is then a quotient of the trivial
group, so `H²(·, Z/p)` of it is a zero module (Mathlib's
`isZero_groupCohomology_succ_of_subsingleton`), and the local cohomology, being the filtered
colimit of the local levels, collapses to a point.

Consequently the *contrapositive* is what the assembly of Neukirch's local characterisation of
decomposition groups consumes: a non-zero local component at `A` witnesses that the place `A` is
*indecomposed* in `U`, i.e. `U ⊓ D_A ≠ ⊥` — Neukirch's "the prime is indecomposed" step.
-/

import Mathlib
import Submission.NK.BrauerHasse.Profinite

universe u

open CategoryTheory
open NK.BrauerHasse

namespace NK.Indecomposed

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local finite levels of a trivial local group have vanishing cohomology.**

If `U ⊓ D_A = ⊥` then the level group `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` is a quotient of the
trivial group, hence a subsingleton, so that `H²(·, Z/p)` of it is a zero module. -/
lemma subsingleton_localLevelH2_of_inf_stabSubgroup_eq_bot (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (h : U ⊓ stabSubgroup A = ⊥) :
    Subsingleton (LocalLevelH2 p U A L) := by
  have : Subsingleton ↥(U ⊓ stabSubgroup A) := by rw [h]; infer_instance
  exact ModuleCat.subsingleton_of_isZero
    (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial (Coeff p) (LocalLevelGroup U A L) (Coeff p)) 1)

/-- **A trivial local group has vanishing local cohomology.**

The local cohomology `LocalH2 p U A` is the filtered colimit of the local level cohomologies
`LocalLevelH2 p U A L` along the inflation maps.  If `U ⊓ D_A = ⊥`, every level is a subsingleton,
and every element of the colimit agrees with the class of `0` at the bottom level `⊥` (since the
transition map from `⊥` is the only place to send it, and the level at `L` is a subsingleton). -/
lemma subsingleton_localH2_of_inf_stabSubgroup_eq_bot (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (h : U ⊓ stabSubgroup A = ⊥) :
    Subsingleton (LocalH2 p U A) := by
  have hsub : ∀ (L : FiniteGaloisIntermediateField K K'), Subsingleton (LocalLevelH2 p U A L) :=
    fun L => subsingleton_localLevelH2_of_inf_stabSubgroup_eq_bot p U A L h
  -- every class is the class of `0` at the bottom level
  have key : ∀ (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L),
      LocalH2.ofLevel p U A L a = 0 := by
    intro L a
    have := hsub L
    have h0 : a = localLevelMap p U A (bot_le : (⊥ : FiniteGaloisIntermediateField K K') ≤ L)
        (0 : LocalLevelH2 p U A ⊥) := Subsingleton.elim _ _
    rw [h0, LocalH2.ofLevel_levelMap (U := U) (A := A)
      (h := (bot_le : (⊥ : FiniteGaloisIntermediateField K K') ≤ L))]
    rfl
  refine ⟨fun x y => ?_⟩
  induction x using Quot.ind with
  | _ xv =>
    induction y using Quot.ind with
    | _ yv => exact (key xv.1 xv.2).trans (key yv.1 yv.2).symm

/-- **A non-zero local component forces a non-trivial local group (trivial coefficients).**

For `A` a place of `K'` over a finite prime of `K`, the localisation
`H2Profinite.loc p U x A` lives in `LocalH2 p U A.1`, which only sees the local group
`U ⊓ stabSubgroup A.1`.  If that local group were trivial, `LocalH2 p U A.1` would be a point
(`subsingleton_localH2_of_inf_stabSubgroup_eq_bot`), so no class could have a non-zero local
component.  Taking the contrapositive: a non-zero local component at `A` forces `U ⊓ D_A ≠ ⊥`. -/
theorem inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : NK.BrauerHasse.OverFinitePrime K K')
    {x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U}
    (hx : NK.BrauerHasse.H2Profinite.loc p U x A ≠ 0) :
    U ⊓ NK.BrauerHasse.stabSubgroup A.1 ≠ ⊥ := by
  intro hcon
  exact hx (by
    have : Subsingleton (LocalH2 p U A.1) :=
      subsingleton_localH2_of_inf_stabSubgroup_eq_bot p U A.1 hcon
    exact Subsingleton.elim _ _)

end NK.Indecomposed
