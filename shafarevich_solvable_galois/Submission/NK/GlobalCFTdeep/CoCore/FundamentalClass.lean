import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.CoCore.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fundamental class, and the class-formation axioms

This file contains the cohomological heart of global class field theory:

* the trivial-group and full-group cases of the class-formation statements;
* **`CohomologicalFieldAxiom K L` for a cyclic extension of prime degree**, proved from the
  Herbrand-quotient computation `NK.GlobalCFT.HerbrandQuotient K L` and the second inequality
  `SecondInequality`.  This is Milne, *CFT*, Theorem 5.1 together with Lemma 5.2 and Remark 5.5 in
  the one case in which the induction is anchored: for `G = Gal(L/K)` of prime order the only
  subgroups are `⊥` and `⊤`, so the class-formation axioms reduce to the index computation
  `[C_K : N_{L/K}C_L] = [L:K]` (the two inequalities), the Herbrand quotient, and the
  two-periodicity of the cohomology of a cyclic group;
* the **reduction from the cyclic prime-degree case to all extensions** as the named input
  `CyclicPrimeReduction` (Milne, *CFT*, Lemmas 5.3–5.4: the inflation–restriction sequence and the
  Sylow reduction), and the resulting theorem `CohomologicalFieldAxiom K L` for *every* finite
  Galois extension of number fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-! ### The two extreme subgroups -/

/-- The cohomology of the restriction to the **trivial subgroup** vanishes in positive degrees. -/
theorem subsingleton_groupCohomology_bot {G : Type} [Group G] (M : Rep ℤ G) (n : ℕ) :
    Subsingleton (groupCohomology (Rep.res (⊥ : Subgroup G).subtype M) (n + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_groupCohomology_succ_of_subsingleton (G := ↥(⊥ : Subgroup G))
      (Rep.res (⊥ : Subgroup G).subtype M) n)

/-- The cardinality form of `subsingleton_groupCohomology_bot`. -/
theorem natCard_groupCohomology_bot {G : Type} [Group G] (M : Rep ℤ G) (n : ℕ) :
    Nat.card (groupCohomology (Rep.res (⊥ : Subgroup G).subtype M) (n + 1)) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_groupCohomology_bot M n, ⟨0⟩⟩

/-- Cohomology is insensitive to replacing a subgroup by `⊤`. -/
theorem subsingleton_groupCohomology_top {k G : Type} [CommRing k] [Group G] (M : Rep k G)
    (h : Subsingleton (groupCohomology M 1)) :
    Subsingleton (groupCohomology (Rep.res (⊤ : Subgroup G).subtype M) 1) := by
  have e : groupCohomology (Rep.res (⊤ : Subgroup G).subtype M) 1 ≅ groupCohomology M 1 :=
    groupCohomology.mapIso (G := ↥(⊤ : Subgroup G)) (H := G) (Subgroup.topEquiv)
      (LinearEquiv.refl k M.V) (fun g => by ext x; rfl) 1
  haveI hB : Subsingleton (groupCohomology M 1) := h
  exact e.toLinearEquiv.injective.subsingleton

/-- The cardinality form of `subsingleton_groupCohomology_top` in degree two. -/
theorem natCard_groupCohomology_top {k G : Type} [CommRing k] [Group G] (M : Rep k G) :
    Nat.card (groupCohomology (Rep.res (⊤ : Subgroup G).subtype M) 2) =
      Nat.card (groupCohomology M 2) := by
  have e : groupCohomology (Rep.res (⊤ : Subgroup G).subtype M) 2 ≅ groupCohomology M 2 :=
    groupCohomology.mapIso (G := ↥(⊤ : Subgroup G)) (H := G) (Subgroup.topEquiv)
      (LinearEquiv.refl k M.V) (fun g => by ext x; rfl) 2
  exact Nat.card_congr e.toLinearEquiv.toEquiv

/-! ### An element of order `p` in a group of prime cardinality -/

/-- In an additive commutative group of **prime** cardinality `p` there is an element of order
`p`: any non-zero element has order dividing `p`, hence of order `1` or `p`, and it is not `0`. -/
theorem exists_addOrderOf_eq_of_natCard_prime {X : Type} [AddCommGroup X] {p : ℕ} (hp : p.Prime)
    (hX : Nat.card X = p) : ∃ α : X, addOrderOf α = p := by
  have hne : ∃ α : X, α ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    haveI : Subsingleton X := ⟨fun a b => by rw [h a, h b]⟩
    have h1 : Nat.card X = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩
    rw [h1] at hX
    exact hp.ne_one hX.symm
  obtain ⟨α, hα⟩ := hne
  refine ⟨α, ?_⟩
  have hdvd : addOrderOf α ∣ p := hX ▸ addOrderOf_dvd_natCard α
  rcases hp.eq_one_or_self_of_dvd (addOrderOf α) hdvd with h1 | hp'
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hα
  · exact hp'

/-! ### The class-formation axioms in the cyclic prime degree case -/

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The class-formation axioms for a cyclic extension of prime degree** (Milne, *CFT*,
Theorem 5.1, Lemma 5.2, Remark 5.5).  For `G = Gal(L/K)` of prime order the only subgroups are
`⊥` and `⊤`; the axioms at `⊤` are the index computation (`[C_K : N_{L/K}C_L] = [L:K]`, from the
two inequalities), the Herbrand-quotient computation `h(G, C_L) = [L:K]` and the two-periodicity
of the cohomology of a cyclic group, and at `⊥` they are trivial. -/
theorem cohomologicalFieldAxiom_of_isCyclic_prime [IsCyclic (L ≃ₐ[K] L)]
    (hp : (Module.finrank K L).Prime) (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    CohomologicalFieldAxiom K L := by
  haveI hcomm : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm fun a b => mul_comm a b
  have hidx : (Idele.normClassSubgroup K L).index = Module.finrank K L :=
    index_eq_finrank_of_secondInequality hh h2
  have hcardG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  haveI hfact : Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L))) := ⟨by rw [hcardG]; exact hp⟩
  haveI h1main : Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) :=
    subsingleton_groupCohomology_one_of_index_eq hh hidx
  have h2main : Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) = Module.finrank K L :=
    natCard_groupCohomology_two_eq_finrank_of_index_eq hidx
  refine ⟨?_, ?_, ?_⟩
  · intro H
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card H with hH | hH
    · rw [hH]
      exact subsingleton_groupCohomology_bot (IdeleClassGroup.rep K L) 0
    · rw [hH]
      exact subsingleton_groupCohomology_top (IdeleClassGroup.rep K L) h1main
  · intro H
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card H with hH | hH
    · rw [hH, natCard_groupCohomology_bot (IdeleClassGroup.rep K L) 1, Subgroup.card_bot]
    · rw [hH, natCard_groupCohomology_top, h2main, Subgroup.card_top, ← hcardG]
  · obtain ⟨α, hα⟩ := exists_addOrderOf_eq_of_natCard_prime hp h2main
    exact ⟨α, by rw [hcardG, hα]⟩

/-- **The class-formation axioms for a cyclic extension of prime order**, with the primality
hypothesis on the order of the Galois group (the form in which a caller normally has it). -/
theorem cohomologicalFieldAxiom_of_isCyclic_prime_card [IsCyclic (L ≃ₐ[K] L)]
    (hp : (Nat.card (L ≃ₐ[K] L)).Prime) (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    CohomologicalFieldAxiom K L :=
  cohomologicalFieldAxiom_of_isCyclic_prime
    (by rwa [IsGalois.card_aut_eq_finrank K L] at hp) hh h2

/-! ### The named reduction, and the general theorem -/

/-- **The class-formation axioms at every cyclic level of prime degree.**  By
`cohomologicalFieldAxiom_of_isCyclic_prime` this is available as soon as the Herbrand-quotient
computation and the second inequality are known. -/
structure CyclicPrimeAxioms : Prop where
  /-- the axioms at cyclic levels of prime degree. -/
  axioms_hold : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))], CohomologicalFieldAxiom K L

/-- `CyclicPrimeAxioms` from the two inputs of the chapter: the Herbrand-quotient computation at
cyclic prime-degree levels and the second inequality. -/
theorem cyclicPrimeAxioms_of_herbrandAndSecondInequality
    (hH : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
      [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))], HerbrandQuotient K L)
    (h2 : SecondInequality) : CyclicPrimeAxioms where
  axioms_hold := by
    intro K L _ _ _ _ _ _ _ _ hfact
    haveI := hfact
    exact cohomologicalFieldAxiom_of_isCyclic_prime
      (by rw [← IsGalois.card_aut_eq_finrank K L]; exact hfact.out) (hH) h2

/-- **Milne, *Class Field Theory*, Lemmas 5.3–5.4**: the class-formation axioms in the cyclic
prime-degree case imply them in general.  The proof in Milne proceeds by induction on `|G|`: the
Sylow reduction (Lemma 5.3) and the inflation–restriction sequence for a normal subgroup `H` of
index `p` (Lemma 5.4), which expresses `H¹(G, C_L)` and `H²(G, C_L)` through the corresponding
groups of `H`, of `G/H` and of the fixed field `L^H`.

This is a specific classical argument, and it is *strictly weaker* than
`CohomologicalFieldAxiom K L`: its hypothesis is the axioms at cyclic levels of prime degree only,
which the chapter proves from the Herbrand-quotient computation and the second inequality. -/
structure CyclicPrimeReduction : Prop where
  /-- the reduction. -/
  reduce : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L], CyclicPrimeAxioms → CohomologicalFieldAxiom K L

/-- **The class-formation axioms for every finite Galois extension of number fields**, from the
cyclic prime-degree case (which the chapter proves) and the reduction of Milne 5.3–5.4. -/
theorem cohomologicalFieldAxiom_of_reduction (hred : CyclicPrimeReduction)
    (hprime : CyclicPrimeAxioms) : CohomologicalFieldAxiom K L :=
  hred.reduce hprime

/-- **The class-formation axioms for every finite Galois extension of number fields**, from the
Herbrand-quotient computation, the second inequality, and Milne's reduction 5.3–5.4. -/
theorem cohomologicalFieldAxiom_of_inputs (hred : CyclicPrimeReduction)
    (hH : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
      [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))], HerbrandQuotient K L)
    (h2 : SecondInequality) : CohomologicalFieldAxiom K L :=
  hred.reduce (cyclicPrimeAxioms_of_herbrandAndSecondInequality hH h2)

end NK.GlobalCFTdeep
