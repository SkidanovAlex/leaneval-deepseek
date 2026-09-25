import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient

/-!
# The target theorem from its cyclic case

`NK.CFTLib.ArtinReciprocityIdeal` for abelian `L/K` is reduced here to its cyclic case
(Lang, *Algebraic Number Theory*, Ch. X, Theorem 3): the conductor of `L/K` is the product of the
conductors of the cyclic quotients `L^H/K` times the absolute norm of the relative different
(which takes care of the ramification condition), and the Artin symbol of a principal ideal is
trivial because its restrictions to all those cyclic quotients are.

The two inputs are stated as hypotheses so that they can be supplied by the corresponding
developments:

* `NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient` (the group theory);
* the cyclic case of the conductor theorem (`artinConductor` for cyclic `L/K`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.CFTLib

open NK.Chebotarev
open NumberField
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The abelian case from the cyclic case.**  If every cyclic subquotient `L^H/K` of the abelian
extension `L/K` has a conductor, then `L/K` has one: the product of a conductor of each of them
with the absolute norm of the relative different. -/
theorem exists_artinConductor_of_cyclic_quotients [IsMulCommutative (Gal(L/K))]
    (hgrp : ∀ g : Gal(L/K), g ≠ 1 →
      ∃ H : Subgroup Gal(L/K), IsCyclic (Gal(L/K) ⧸ H) ∧ g ∉ H)
    (hcyc : ∀ (H : Subgroup Gal(L/K)), IsCyclic (Gal(L/K) ⧸ H) →
      ∃ m, artinConductor K ↥(IntermediateField.fixedField H) m) :
    ∃ m, artinConductor K L m := by
  classical
  letI : Fintype (Subgroup Gal(L/K)) := Fintype.ofFinite _
  -- a positive conductor for each cyclic quotient, and `1` for the others
  have hH' : ∀ H : Subgroup Gal(L/K), ∃ m : ℕ, 0 < m ∧
      (IsCyclic (Gal(L/K) ⧸ H) → artinConductor K ↥(IntermediateField.fixedField H) m) := by
    intro H
    by_cases h : IsCyclic (Gal(L/K) ⧸ H)
    · obtain ⟨m, hm⟩ := hcyc H h
      exact ⟨m, hm.1, fun _ => hm⟩
    · exact ⟨1, Nat.one_pos, fun hc => absurd hc h⟩
  choose mh hmh_pos hmh using hH'
  -- the different of `L/K`
  have hdiff_ne : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
  set m : ℕ := (∏ H : Subgroup Gal(L/K), mh H) *
    Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) with hm
  refine ⟨m, ?_⟩
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.mul_pos (Finset.prod_pos fun H _ => hmh_pos H) (Nat.pos_of_ne_zero hdiff_ne)
  have hram : ∀ p : PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1 := by
    intro p hp
    refine ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem p ?_
    intro hmem
    apply hp
    rw [hm]
    push_cast
    exact p.asIdeal.mul_mem_left _ hmem
  refine artinConductor_of_cyclic_quotients (K := K) (L := L) hgrp hmpos hram ?_
  intro H hH
  refine (hmh H hH).mono ?_ hmpos
  rw [hm]
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun H => mh H) (Finset.mem_univ H)) _

/-- **The target theorem from its cyclic case.**  `NK.CFTLib.ArtinReciprocityIdeal` follows from
the cyclic case of the conductor theorem together with the group-theoretic fact
`⨅ {H : G/H cyclic} H = ⊥` for finite abelian groups. -/
theorem ArtinReciprocityIdeal_of_cyclic
    (hgrp : ∀ (G : Type) [Group G] [IsMulCommutative G] [Finite G],
      (⨅ H : {H : Subgroup G // IsCyclic (G ⧸ H)}, (H.1 : Subgroup G)) = ⊥)
    (hcyc : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))],
      ∃ m, artinConductor K L m) :
    ArtinReciprocityIdeal := by
  refine artinReciprocityIdeal_of_forall_exists_artinConductor ?_
  intro K L _ _ _ _ _ _ _ hcomm
  haveI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm hcomm
  have hgrp' : ∀ g : Gal(L/K), g ≠ 1 →
      ∃ H : Subgroup Gal(L/K), IsCyclic (Gal(L/K) ⧸ H) ∧ g ∉ H := by
    intro g hg
    have hmem : g ∉ (⨅ H : {H : Subgroup Gal(L/K) // IsCyclic (Gal(L/K) ⧸ H)},
        (H.1 : Subgroup Gal(L/K))) := by
      rw [hgrp]
      exact hg
    rw [Subgroup.mem_iInf] at hmem
    simp only [not_forall, not_not] at hmem
    obtain ⟨H, hH⟩ := hmem
    exact ⟨H.1, H.2, hH⟩
  refine exists_artinConductor_of_cyclic_quotients hgrp' ?_
  intro H hH
  haveI : IsCyclic (Gal(↥(IntermediateField.fixedField H)/K)) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H)).mp hH
  exact hcyc K ↥(IntermediateField.fixedField H)

/-- **The target theorem from its cyclic case**, with the group-theoretic input discharged by
`NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient`. -/
theorem ArtinReciprocityIdeal_of_cyclicCase
    (hcyc : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))],
      ∃ m, artinConductor K L m) :
    ArtinReciprocityIdeal := by
  refine ArtinReciprocityIdeal_of_cyclic (fun G _ _ _ => ?_) hcyc
  letI : CommGroup G := { (inferInstance : Group G) with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  haveI : Finite G := ‹Finite G›
  exact NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient

end NK.CFTLib
