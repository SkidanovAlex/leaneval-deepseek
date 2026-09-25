/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p`-primary input catalogue and the Sylow reduction

This module contains the `p`-primary form of the input catalogue of
`Submission/Work/HasseTwist/Inputs.lean` — the labelled level-wise Hasse principle in strong form
asserted only at the levels whose level group is a `p`-group and only for the subgroups `V ≤ U` of a
labelled `U` — together with the *proved* Sylow reduction to the form at all levels.  It is the
twisted counterpart of the pair `NK.HassePrinciple.Sha2Input.pgroup_level` +
`NK.HassePrinciple.obstruction_trivial_of_pgroup_rel`.

The reduction is the same one as in the sibling chapter: a Sylow `p`-subgroup `Q` of the (finite)
level group `Γ_L = V/(V ⊓ Gal(K'/L))` has a preimage `V' ≤ V ≤ U` (the group-theoretic input
`NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow`, coefficient-generic and reused
verbatim), the level group of `V'` is a `p`-group, restriction carries the level obstruction of
`(V,L)` into that of `(V',L)` (`NK.HasseTwist.levelRes_mem_levelObstruction`), the `p`-primary
input kills the restriction of `a`, and the index of `Q` in `Γ_L` is prime to `p`, so the transfer
`NK.HasseTwist.levelRes_injective_of_coprime_index` concludes `a = 0`.

## Main results

* `NK.HasseTwist.obstruction_trivial_of_pgroupLevel` — the Sylow reduction;
* `NK.HasseTwist.locLevel_eq_levelRes` and
  `NK.HasseTwist.obstruction_trivial_of_coprime_index` — the unconditional instance of the input at
  every level at which some place has local level group of index prime to `p`;
* `NK.HasseTwist.Sha2InputPgroup`, `NK.HasseTwist.sha2Vanishing_of_pgroupInput` — the smaller
  input catalogue and the resulting Hasse principle;
* `NK.HasseTwist.sha2InputPgroup_of_sha2Input` — the implication between the two catalogues.
-/

import Submission.NK.HasseTwist.Restrict
import Submission.NK.HasseTwist.Obstruction
import Submission.NK.HasseTwist.Hasse
import Submission.NK.HasseTwist.Inputs
import Submission.NK.HasseTwist.levelRes_mem_levelObstruction
import Submission.NK.HasseTwist.levelRes_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The localisation is the restriction to the local subgroup -/

/-- **The level-wise localisation at a place is the restriction to the local subgroup**: the local
level group `(U ⊓ D_A)/((U ⊓ D_A) ⊓ Gal(K'/L))` is *definitionally* the level group of the subgroup
`U ⊓ D_A`, and both maps are the restriction along the inclusion. -/
lemma locLevel_eq_levelRes (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    locLevel p U A L =
      levelRes p (inf_le_left : U ⊓ stabSubgroup A ≤ U) L := by
  rw [locLevel, levelRes]
  refine groupCohomology.map_congr rfl ?_ 2
  apply LinearMap.ext
  intro x
  rfl

/-- **The level-wise Hasse principle holds at every level at which some place has local level group
of index prime to `p`.**  This is an *unconditional instance* of the input field
`NK.Sha2Input.level_obstruction`. -/
theorem obstruction_trivial_of_coprime_index (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (hcop : Nat.Coprime (Subgroup.index (MonoidHom.range
      (NK.BrauerHasse.levelInclHom (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) L))) p)
    {a : LevelH2 p U L} (ha : a ∈ levelObstruction p U L) : a = 0 := by
  have hmem : a ∈ (⨅ A' : OverFinitePrime K K', (locLevel p U A'.1 L).hom.ker) := ha
  rw [Submodule.mem_iInf] at hmem
  have h0 : (levelRes p (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) L) a = 0 := by
    rw [← locLevel_eq_levelRes]
    exact hmem A
  exact levelRes_injective_of_coprime_index (K := K) (K' := K') p _ L hcop
    (h0.trans (map_zero ((levelRes p (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) L)).hom).symm)

/-! ## The Sylow reduction -/

/-- **The Sylow reduction, in the twisted setting.**  If every class of the level obstruction at
every `p`-primary level of every subgroup `V ≤ U` is zero, then the same holds at *all* levels of
every subgroup of `U`. -/
theorem obstruction_trivial_of_pgroupLevel (p : ℕ) (hp : p.Prime) (U : Subgroup Gal(K'/K))
    (h : ∀ (V : Subgroup Gal(K'/K)), V ≤ U → ∀ (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p V L), IsPGroup p (NK.BrauerHasse.LevelGroup V L) →
        a ∈ levelObstruction p V L → a = 0) :
    ∀ (V : Subgroup Gal(K'/K)), V ≤ U → ∀ (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p V L), a ∈ levelObstruction p V L → a = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro V hV L a ha
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := NK.BrauerHasse.LevelGroup V L)
  obtain ⟨V', hV', ⟨iso⟩, hrange⟩ :=
    NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow (K := K) (K' := K') (p := p) V L Q
  have hVU : V' ≤ U := hV'.trans hV
  have hP : IsPGroup p (NK.BrauerHasse.LevelGroup V' L) :=
    IsPGroup.of_equiv Q.isPGroup' iso.symm
  have hres : (levelRes p hV' L) a ∈ levelObstruction p V' L :=
    levelRes_mem_levelObstruction p hV' ha
  have hzero : (levelRes p hV' L) a = 0 := h V' hVU L _ hP hres
  have hcop : Nat.Coprime
      (Subgroup.index (MonoidHom.range (NK.BrauerHasse.levelInclHom hV' L))) p := by
    rw [hrange, Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr Q.not_dvd_index
  exact levelRes_injective_of_coprime_index (K := K) (K' := K') p hV' L hcop
    (hzero.trans (map_zero ((levelRes p hV' L)).hom).symm)

/-! ## The `p`-primary input catalogue -/

variable {κ κ' : Type u} [NumberField K] [Field κ] [Field κ'] [Algebra κ κ']
  [IsSepClosure κ κ']

/-- **The inputs of the twisted Hasse principle, in `p`-primary form**: the licensed
number-theoretic input, the labelled level-wise Hasse principle at the `p`-primary levels in the
strong form, and the exhaustion of the kernel of the localisation.  This is the twisted counterpart
of `NK.HassePrinciple.Sha2Input`; by the Sylow reduction
`NK.HasseTwist.obstruction_trivial_of_pgroupLevel` it implies the catalogue `Sha2Input` of
`Submission/Work/HasseTwist/Inputs.lean`. -/
structure Sha2InputPgroup (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- the Hasse norm theorem for cyclic extensions of number fields. -/
  hasse_norm : NK.HassePrinciple.HasseNormTheorem.{u}
  /-- **The labelled `p`-primary level-wise Hasse principle** (strong form): for every closed
  `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, every subgroup `V ≤ U` and every finite level at which
  the level group `V/(V ⊓ Gal(K'/L))` is a `p`-group, a class of the level obstruction is zero. -/
  pgroup_level : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ (V : Subgroup Gal(K'/K)), V ≤ U →
      ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L),
        IsPGroup p (NK.BrauerHasse.LevelGroup V L) → a ∈ levelObstruction p V L → a = 0
  /-- the exhaustion of the kernel of the localisation by the finite levels. -/
  kernel_exhausted : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Twist p U,
      (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) →
        ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
          x = H2Twist.ofLevel p U L a ∧ a ∈ levelObstruction p U L

/-- **The all-levels catalogue implies the `p`-primary one**, in the form in which its level field
is stated for all subgroups `V ≤ U` (the classical shape of the field, cf.
`NK.HassePrinciple.Sha2Input.pgroup_level`).  When the level field is only required for the
labelled `U` itself — the shape used in `NK.HasseTwist.Sha2Input`, which makes for the *weakest*
hypothesis of `NK.HasseTwist.sha2Vanishing` — the implication requires the labelled Sylow-reduced
form, which is provided by `NK.HasseTwist.obstruction_trivial_of_pgroupInput` in the reverse
direction. -/
theorem sha2InputPgroup_of_allLevels (p : ℕ) (hp : p.Prime)
    (hnorm : NK.HassePrinciple.HasseNormTheorem.{u})
    (hlevel : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (V : Subgroup Gal(K'/K)), V ≤ U →
        ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L),
          a ∈ levelObstruction p V L → a = 0)
    (hkernel : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Twist p U,
        (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) →
          ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
            x = H2Twist.ofLevel p U L a ∧ a ∈ levelObstruction p U L) :
    Sha2InputPgroup (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := hp
  hasse_norm := hnorm
  pgroup_level := fun U hU hκ V hV L a _ ha => hlevel U hU hκ V hV L a ha
  kernel_exhausted := hkernel

/-- **The labelled level-wise Hasse principle at all levels, from the `p`-primary input.** -/
theorem obstruction_trivial_of_pgroupInput (p : ℕ)
    (h : Sha2InputPgroup (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
        (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0 :=
  fun U hU hκ L a ha =>
    obstruction_trivial_of_pgroupLevel (K := K) (K' := K') p h.hp U
      (h.pgroup_level U hU hκ) U le_rfl L a ha

/-- **`LevelForm` from the `p`-primary inputs.** -/
theorem levelForm_of_pgroupInput (p : ℕ)
    (h : Sha2InputPgroup (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  levelForm_of_labelledObstruction (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (obstruction_trivial_of_pgroupInput (K := K) (K' := K') (κ := κ) (κ' := κ') p h)
    h.kernel_exhausted

/-- **The Hasse principle `NK.BrauerTwist.Sha2Vanishing` from the `p`-primary inputs.** -/
theorem sha2Vanishing_of_pgroupInput (p : ℕ)
    (h : Sha2InputPgroup (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_levelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (levelForm_of_pgroupInput (K := K) (K' := K') (κ := κ) (κ' := κ') p h)

/-- The same instance in the form of local triviality at the level. -/
theorem levelLocTrivial_eq_zero_of_coprime_index (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : OverFinitePrime K K') (L : FiniteGaloisIntermediateField K K')
    (hcop : Nat.Coprime (Subgroup.index (MonoidHom.range
      (NK.BrauerHasse.levelInclHom (inf_le_left : U ⊓ stabSubgroup A.1 ≤ U) L))) p)
    {a : LevelH2 p U L} (ha : levelLocTrivial p U L a) : a = 0 :=
  obstruction_trivial_of_coprime_index p A L hcop ((mem_levelObstruction_iff p U L a).mpr ha)

end NK.HasseTwist
