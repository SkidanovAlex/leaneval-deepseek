/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFTdeep.SecondInequality.secondInequality_of_isCyclic_prime
import Submission.NK.GlobalCFTdeep.exists_normal_subgroup_index_eq_prime_of_solvable
import Submission.NK.GlobalCFTdeep.index_normClassSubgroup_le_mul_index
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso

/-!
# The second inequality for solvable Galois extensions, unconditionally

This file proves the **second inequality of global class field theory**,

  `[C_K : N_{L/K} C_L] ≤ [L : K]`,

for every finite Galois extension `L / K` of number fields whose Galois group is **solvable** —
in particular for every abelian and every cyclic extension, which is the case in which the
inequalities are classically stated — *without any analytic input*.

The proof is the classical algebraic reduction to the cyclic case of prime degree:

* the **cyclic prime degree case** is Milne's Chapter VII §6, proved unconditionally in
  `Submission/Work/GlobalCFTdeep/SecondInequality/secondInequality_of_isCyclic_prime.lean`
  (Kummer theory and the `S`-unit theorem; no Hecke `L`-functions);
* **induction on `|Gal(L/K)|`** for a solvable group: if `N ◁ G` has prime index `q`
  (`exists_normal_subgroup_index_eq_prime_of_solvable`) and `M = L^N`, then
  `[C_K : N_{L/K}C_L] ≤ [C_K : N_{M/K}C_M] · [C_M : N_{L/M}C_L]`
  (the tower inequality `index_normClassSubgroup_le_mul_index` below),
  the first factor is `≤ q` by the cyclic prime case (`M/K` is cyclic of prime order) and the
  second is `≤ |N|` by the induction hypothesis applied to the extension `L/M`.

The tower inequality is proved in `Submission/Work/GlobalCFTdeep/index_normClassSubgroup_le_mul_index.lean`
(purely group-theoretically), together with the **finiteness of the norm index** of any finite
extension of number fields (`normClassSubgroup_index_ne_zero`, proved elementarily from
`Algebra.norm_algebraMap` at the ramified places and the unramified case).  Finiteness is *needed*:
in Mathlib `Subgroup.index` is `Nat.card` of the quotient, hence `0` on infinite quotients, and the
group-theoretic step `(A' ⊔ ker f).index ≤ A'.index` fails for infinite `A'.index`
(`A' = ℤ × 0 ≤ ℤ × ℤ = A' ⊔ ker f` with `ker f = 0 × ℤ`).

## Main results

* `NK.GlobalCFTdeep.index_normClassSubgroup_le_mul_index` — the tower inequality;
* `NK.GlobalCFTdeep.index_le_finrank_of_isSolvable` — the second inequality for solvable `G`;
* `NK.GlobalCFTdeep.index_eq_finrank_of_isSolvable` — with the (unconditional) first inequality,
  `[C_K : N_{L/K}C_L] = [L : K]` for solvable `G`;
* `NK.GlobalCFTdeep.fieldAxiom_of_isSolvable` — the field axiom of the class formation;
* `NK.GlobalCFTdeep.SecondInequalitySolvable` and `secondInequalitySolvable` — the bundled form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-! ## The induction -/

/-- **The second inequality for a finite Galois extension with solvable Galois group**, by strong
induction on the order of the group. -/
theorem secondInequality_solvable_aux :
    ∀ n, ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)],
      Nat.card (L ≃ₐ[K] L) = n → (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K L _ _ _ _ _ _ _ _ hcard
    rcases Nat.lt_or_ge 1 n with hn | hn
    · -- nontrivial Galois group
      haveI hnt : Nontrivial (L ≃ₐ[K] L) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hcard]
        exact hn
      obtain ⟨N, hNnorm, q, hqprime, hNindex⟩ :=
        exists_normal_subgroup_index_eq_prime_of_solvable (G := L ≃ₐ[K] L) ‹Group.IsSolvable _› hnt
      haveI hNnormal : N.Normal := hNnorm
      haveI hqFact : Fact q.Prime := ⟨hqprime⟩
      set M : IntermediateField K L := IntermediateField.fixedField N with hM
      haveI : NumberField ↥M := inferInstance
      haveI : FiniteDimensional K ↥M := inferInstance
      haveI : FiniteDimensional ↥M L := inferInstance
      haveI : IsGalois ↥M L := inferInstance
      haveI : IsGalois K ↥M := IsGalois.of_fixedField_normal_subgroup N
      -- the lower extension `M/K` is cyclic of prime order `q`
      have hMcard : Nat.card (↥M ≃ₐ[K] ↥M) = q := by
        rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv,
          ← Subgroup.index_eq_card N, hNindex]
      haveI : IsCyclic (↥M ≃ₐ[K] ↥M) := isCyclic_of_prime_card hMcard
      haveI : Fact (Nat.Prime (Nat.card (↥M ≃ₐ[K] ↥M))) := ⟨hMcard ▸ hqprime⟩
      have hlower : (Idele.normClassSubgroup K ↥M).index ≤ Module.finrank K ↥M :=
        SecondInequality.secondInequality_of_isCyclic_prime (K := K) (L := ↥M)
      rw [← IsGalois.card_aut_eq_finrank (F := K) (E := ↥M), hMcard] at hlower
      -- the upper extension `L/M` by the induction hypothesis, which also gives finiteness
      have hMlt : Nat.card ↥N < n := by
        have hmul : Nat.card ↥N * N.index = Nat.card (L ≃ₐ[K] L) := N.card_mul_index
        rw [hNindex, hcard] at hmul
        have hlt : Nat.card ↥N < Nat.card ↥N * q := by
          simpa using Nat.mul_lt_mul_of_pos_left hqprime.one_lt (Nat.card_pos (α := ↥N))
        rw [hmul] at hlt
        exact hlt
      have hupcard : Nat.card (L ≃ₐ[↥M] L) = Nat.card ↥N :=
        (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv).symm
      haveI : Group.IsSolvable ↥N := inferInstance
      haveI : Group.IsSolvable (L ≃ₐ[↥M] L) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (IntermediateField.subgroupEquivAlgEquiv N).symm.toMonoidHom)
          (IntermediateField.subgroupEquivAlgEquiv N).symm.injective
      have hIH := ih (Nat.card ↥N) hMlt hupcard
      rw [← IsGalois.card_aut_eq_finrank (F := ↥M) (E := L), hupcard] at hIH
      -- the lower extension `M/K`: second inequality from the cyclic prime case, finiteness from
      -- the (unconditional) first inequality
      have hlower_le : (Idele.normClassSubgroup K ↥M).index ≤ q := by
        have h2 := SecondInequality.secondInequality_of_isCyclic_prime (K := K) (L := ↥M)
        rwa [← IsGalois.card_aut_eq_finrank (F := K) (E := ↥M), hMcard] at h2
      have htower := index_normClassSubgroup_le_mul_index (K := K) (K' := ↥M) (L := L)
      have hfin' : Nat.card ↥N * q = Module.finrank K L := by
        rw [← IsGalois.card_aut_eq_finrank (F := K) (E := L), ← N.card_mul_index, hNindex]
      calc (Idele.normClassSubgroup K L).index
          ≤ (Idele.normClassSubgroup K ↥M).index * (Idele.normClassSubgroup ↥M L).index :=
            htower
        _ ≤ q * Nat.card ↥N := Nat.mul_le_mul hlower_le hIH
        _ = Module.finrank K L := by rw [mul_comm]; exact hfin'
    · -- trivial Galois group
      have hn1 : n ≤ 1 := by omega
      have hcard1 : Nat.card (L ≃ₐ[K] L) = 1 :=
        le_antisymm (by rw [hcard]; exact hn1) Nat.card_pos
      haveI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.mp hcard1).1
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_subsingleton
      have hherb := (cyclicHerbrandQuotient.herbrand (K := K) (L := L)).herbrand
      have h0 := H0Computation.index_eq_natCard (globalCFT_H0Computation (K := K) (L := L))
      have hgr : Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (isZero_groupCohomology_succ_of_subsingleton (IdeleClassGroup.rep K L) 0)
      have he := (TateCohomology.isoGroupCohomology (R := ℤ) (G := (L ≃ₐ[K] L)) 1).app
        (IdeleClassGroup.rep K L)
      haveI h1 : Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1) :=
        @Function.Injective.subsingleton _ _ _ he.toLinearEquiv.injective hgr
      have hone : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩
      have hfin1 : Module.finrank K L = 1 := by
        rw [← IsGalois.card_aut_eq_finrank (F := K) (E := L), hcard1]
      have hix : (Idele.normClassSubgroup K L).index = Module.finrank K L := by
        rw [h0, hherb, hone, mul_one]
      exact hix.le

/-! ## The second inequality, the index formula and the field axiom -/

/-- **The second inequality for a solvable Galois extension**: `[C_K : N_{L/K}C_L] ≤ [L : K]`. -/
theorem index_le_finrank_of_isSolvable {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L :=
  secondInequality_solvable_aux (Nat.card (L ≃ₐ[K] L)) rfl

/-- **The index formula for an abelian Galois extension**, from the (unconditional) second
inequality for solvable groups and the first inequality.  The first inequality
(`NK.GlobalCFT.first_inequality_of_herbrandQuotient`) is the statement `h(Gal(L/K),C_L) = [L:K]`
of Milne's Theorem 4.3, which is *false* for non-abelian `G` (`[C_K : N_{L/K}C_L] = |Gᵃᵇ|`
then), so it is carried as an explicit hypothesis; it is unconditional when `L/K` is cyclic
(`cyclicHerbrandQuotient`). -/
theorem index_eq_finrank_of_abelian_of_herbrand {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (hh : HerbrandQuotient K L) :
    (Idele.normClassSubgroup K L).index = Module.finrank K L := by
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  exact le_antisymm (index_le_finrank_of_isSolvable)
    (first_inequality_of_herbrandQuotient (globalCFT_H0Computation (K := K) (L := L)) hh)

/-- **The second inequality for every finite Galois extension with solvable Galois group**, as a
single `Prop`-valued structure. -/
structure SecondInequalitySolvable : Prop where
  /-- `[C_K : N_{L/K}C_L] ≤ [L : K]`. -/
  index_le : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)],
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L

/-- **The second inequality for solvable extensions, proved.**  No analytic input (no Hecke
`L`-functions) and no named hypothesis is used. -/
theorem secondInequalitySolvable : SecondInequalitySolvable where
  index_le := index_le_finrank_of_isSolvable

/-- The second inequality for cyclic extensions, as a special case. -/
theorem index_le_finrank_of_isCyclic {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  exact index_le_finrank_of_isSolvable

/-- **Milne's Theorem 4.3 + the second inequality: the index of the norm subgroup is the degree**
for every finite **cyclic** extension of number fields, unconditionally. -/
theorem index_eq_finrank_of_isCyclic {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  index_eq_finrank_of_abelian_of_herbrand
    (cyclicHerbrandQuotient.herbrand (K := K) (L := L))

/-- The field axiom of the class formation for abelian extensions, from the second inequality and
the first inequality in the form of Milne's Theorem 4.3. -/
theorem fieldAxiom_of_abelian_of_herbrand {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (hh : HerbrandQuotient K L) : FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, index_eq_finrank_of_abelian_of_herbrand hh]
    exact (Module.finrank_pos).ne'
  index_eq := index_eq_finrank_of_abelian_of_herbrand hh

/-- The field axiom of the class formation for cyclic extensions, unconditionally. -/
theorem fieldAxiom_of_isCyclic {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] : FieldAxiom K L :=
  fieldAxiom_of_abelian_of_herbrand (cyclicHerbrandQuotient.herbrand (K := K) (L := L))

end NK.GlobalCFTdeep
