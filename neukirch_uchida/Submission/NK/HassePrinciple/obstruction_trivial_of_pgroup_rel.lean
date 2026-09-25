/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Sylow reduction, in the labelled (relative) form

This is the form of the Sylow reduction that the input structure of the chapter uses: the level-wise
Hasse principle in strong form, asserted only at the `p`-primary levels and only for the subgroups of
a *labelled* closed subgroup `U ≤ Gal(K'/K)` (a subgroup isomorphic to `Gal(κ'/κ)`), implies it for
all levels of `U`.

The labelled restriction is what confines the archimedean obstruction to the situation in which the
Hasse principle is true (README §5.7, §5.9); the `p`-primary restriction is what makes the input
small, and the reduction is the proved content: a Sylow `p`-subgroup of the level group has preimage
inside the subgroup under consideration, so the hypothesis applies.
-/

import Mathlib
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.levelInclHom_mem_levelObstruction

namespace NK.HassePrinciple

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The labelled Sylow reduction.**  Let `U ≤ Gal(K'/K)` and suppose that at every level of every
subgroup `V ≤ U` whose level group `V/(V ⊓ Gal(K'/L))` is a `p`-group, every class of the level
obstruction is zero.  Then the same holds at *every* level of every subgroup of `U`. -/
theorem obstruction_trivial_of_pgroup_rel {p : ℕ} (hp : p.Prime)
    (U : Subgroup Gal(K'/K))
    (h : ∀ (V : Subgroup Gal(K'/K)), V ≤ U → ∀ (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p V L), IsPGroup p (LevelGroup V L) → a ∈ levelObstruction p V L → a = 0) :
    ∀ (V : Subgroup Gal(K'/K)), V ≤ U → ∀ (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p V L), a ∈ levelObstruction p V L → a = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro V hV L a ha
  -- A Sylow `p`-subgroup `Q` of the finite level group of `V`, and its preimage `V' ≤ V ≤ U`.
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := LevelGroup V L)
  obtain ⟨V', hV', ⟨iso⟩, hrange⟩ := exists_subgroup_levelGroup_equiv_sylow V L Q
  have hVU : V' ≤ U := hV'.trans hV
  -- The level group of `V'` is a `p`-group, being isomorphic to the Sylow subgroup `Q`.
  have hP : IsPGroup p (LevelGroup V' L) := IsPGroup.of_equiv Q.isPGroup' iso.symm
  -- Restriction carries the level obstruction of `(V,L)` into that of `(V',L)`.
  have hres : (H2.map (levelInclHom hV' L)).hom a ∈ levelObstruction p V' L :=
    levelInclHom_mem_levelObstruction p hV' L ha
  -- Hence the labelled `p`-primary input kills the restriction of `a`.
  have hzero : (H2.map (levelInclHom hV' L)).hom a = 0 := h V' hVU L _ hP hres
  -- The index of the Sylow subgroup is prime to `p`, so restriction is injective here.
  have hcop : Nat.Coprime (Subgroup.index (MonoidHom.range (levelInclHom hV' L))) p := by
    rw [hrange, Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr Q.not_dvd_index
  exact H2_map_injective_of_coprime_index (p := p) (levelInclHom hV' L)
    (levelInclHom_injective hV' L) hcop
    (hzero.trans (map_zero ((H2.map (levelInclHom hV' L)).hom)).symm)

end NK.HassePrinciple
