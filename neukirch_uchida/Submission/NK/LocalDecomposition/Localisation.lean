/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The localisation map *is* the restriction map to the decomposition group

For a closed subgroup `U ≤ Gal(K'/K)` and a place `A` of `K'` over a finite prime of `K`, the local
cohomology `NK.BrauerHasse.LocalH2 p U A` is by definition the filtered colimit

`colim_L H²((U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L)), Z/p)`

which is *literally* the profinite cohomology `NK.BrauerHasse.H2Profinite p (U ∩ D_A)` of the
closed subgroup `U ∩ D_A`; and the level-wise localisation `NK.BrauerHasse.locLevel` is literally
the level-wise *restriction* `H2.map (levelInclHom inf_le_left L)`.  Both identifications are
definitional (`rfl`), and this file records them, together with the resulting description of the
localisation map as the restriction map:

* `NK.LocalDecomposition.LocalH2.eq_profinite` — `LocalH2 p U A = H2Profinite p (U ⊓ D_A)`;
* `NK.LocalDecomposition.locLevel_eq_map_levelInclHom` — the level-wise statement;
* `NK.LocalDecomposition.H2Profinite.res` — the restriction map, with its computation rule
  `res_ofLevel`;
* `NK.LocalDecomposition.loc_eq_res` — **the localisation at a place is the restriction to the
  decomposition group**, `loc p U x A = res x`;
* `NK.LocalDecomposition.loc_eq_zero_iff_res_eq_zero` — the resulting criterion for the vanishing
  of the local component.

This is the bridge between the cohomological vocabulary of `Submission/Work/BrauerHasse/` and the
group-theoretic vocabulary in which the classical arguments (Neukirch's rank count, Neukirch's
Korollar 1) are stated: "the local component of `x` at `A` is non-zero" means exactly "the
restriction of `x` to `H ∩ D_A` is non-zero".
-/
import Submission.NK.LocalDecomposition.Reduction
import Submission.NK.BrauerHasse.exists_restriction_map
import Submission.NK.HassePrinciple.Inert

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


open scoped Classical Pointwise

universe u

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local cohomology at a place is the profinite cohomology of the decomposition group.**
Both sides are the filtered colimit of the same levelwise cohomology, so the identification is
definitional. -/
theorem LocalH2.eq_profinite (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    LocalH2 p U A = H2Profinite p (U ⊓ stabSubgroup A) := rfl

/-- The level-wise localisation is the level-wise restriction to the decomposition group. -/
theorem locLevel_eq_map_levelInclHom (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    locLevel p U A L =
      H2.map (levelInclHom (inf_le_left : U ⊓ stabSubgroup A ≤ U) L) := rfl

/-- **The restriction map** `H²(U, Z/p) → H²(V, Z/p)` for an inclusion `V ≤ U` of closed
subgroups, defined from `NK.BrauerHasse.exists_restriction_map`. -/
noncomputable def H2Profinite.res (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    H2Profinite p U → H2Profinite p V :=
  Classical.choose (exists_restriction_map p h)

/-- The computation rule for the restriction map on the finite levels. -/
theorem H2Profinite.res_ofLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    H2Profinite.res p h (H2Profinite.ofLevel L a) =
      H2Profinite.ofLevel L ((H2.map (levelInclHom h L)) a) :=
  Classical.choose_spec (exists_restriction_map p h) L a

/-- **The localisation map at a place *is* the restriction map to the decomposition group.**

After the definitional identification `LocalH2 p U A = H2Profinite p (U ⊓ D_A)`
(`LocalH2.eq_profinite`), the localisation of a class at `A` is its restriction to `U ∩ D_A`. -/
theorem loc_eq_res (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K')
    (x : H2Profinite p U) :
    (H2Profinite.loc p U x A : H2Profinite p (U ⊓ stabSubgroup A.1)) =
      H2Profinite.res p (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) x := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [H2Profinite.loc_ofLevel_apply, H2Profinite.res_ofLevel]
  rfl

/-- **The local component at `A` vanishes if and only if the restriction to `H ∩ D_A` vanishes.** -/
theorem loc_eq_zero_iff_res_eq_zero (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K')
    (x : H2Profinite p U) :
    H2Profinite.loc p U x A = 0 ↔
      H2Profinite.res p (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) x = 0 := by
  rw [← loc_eq_res p U A x]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact h

/-- A non-zero class has a non-zero local component at every *inert* place, i.e. every place whose
decomposition group contains `U`: in the identification of `loc_eq_res` this is the statement that
the restriction map to `U ⊓ D_A = U` is the identity. -/
theorem loc_ne_zero_of_le_stabSubgroup_res (p : ℕ) {U : Subgroup Gal(K'/K)} (A : OverFinitePrime K K')
    (h : U ≤ stabSubgroup A.1) {x : H2Profinite p U} (hx : x ≠ 0) :
    H2Profinite.loc p U x A ≠ 0 :=
  NK.HassePrinciple.loc_ne_zero_of_le_stabSubgroup p A h hx

end

end NK.LocalDecomposition
