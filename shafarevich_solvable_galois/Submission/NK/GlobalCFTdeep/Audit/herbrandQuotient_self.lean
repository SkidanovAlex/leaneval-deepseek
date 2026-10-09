/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Herbrand quotient of the trivial extension `K / K`

The Herbrand-quotient computation `NK.GlobalCFT.HerbrandQuotient K L` for a finite Galois
extension `L / K` says that `Ĥ¹(Gal(L/K), C_L)` is finite (indeed non-trivial as a cardinal) and
that `|Ĥ⁰(Gal(L/K), C_L)| = [L : K] · |Ĥ¹(Gal(L/K), C_L)|`.

For the **trivial extension** `L = K` the Galois group `K ≃ₐ[K] K` is trivial, so *all* of its
Tate cohomology vanishes for any coefficient module; in particular

* `|Ĥ⁰(K ≃ₐ[K] K, C_K)| = 1` and `|Ĥ¹(K ≃ₐ[K] K, C_K)| = 1`, while
* `[K : K] = 1`,

so the Herbrand quotient computation holds, `1 = 1 · 1`.  This is the satisfiability witness for
`HerbrandQuotient`, in the same spirit as
`NK.GlobalCFTdeep.Audit.cohomologicalFieldAxiom_self` for the cohomological field axiom.

## The mathematics used

* the Galois group of `K / K` is trivial: a `K`-algebra automorphism of the field `K` fixes `K`
  pointwise and `algebraMap K K` is the identity;
* for a **trivial** group `G` the norm map `N = ∑_{g : G} ρ(g)` is the identity (the sum has a
  single term, `ρ 1 = 1`), hence in degree zero the Tate complex `M --N--> M --d--> ...` has
  `Ĥ⁰(G, M) = M^G / N(M) = M / M = 0` (`tateCohomology_zero_iso` of the commons computes
  `Ĥ⁰` as the quotient of the invariants by the norm image);
* in positive degree the Tate cohomology agrees with group cohomology
  (`TateCohomology.isoGroupCohomology`), which vanishes because `G` has only one element
  (`isZero_groupCohomology_succ_of_subsingleton`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace NK.GlobalCFTdeep.Audit

open CategoryTheory

/-- The `K`-algebra automorphism group of `K` is trivial: a `K`-algebra automorphism of `K` fixes
`K` pointwise, and `algebraMap K K` is the identity. -/
theorem subsingleton_algEquiv_self (K : Type) [Field K] : Subsingleton (K ≃ₐ[K] K) :=
  ⟨fun σ τ => AlgEquiv.ext fun x => by
    have hσ : σ x = x := by simpa using σ.commutes x
    have hτ : τ x = x := by simpa using τ.commutes x
    rw [hσ, hτ]⟩

/-- **The zeroth Tate cohomology of a representation of a trivial group vanishes.**  For a group
`G` with a single element the norm map `N = ∑_{g : G} ρ(g)` is `ρ 1 = 1`, hence the quotient
`Ĥ⁰(G, M) = M^G ⧸ N(M)` computed by `tateCohomology_zero_iso` is `M ⧸ M = 0`. -/
theorem subsingleton_tateCohomology_zero_of_subsingleton {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton (tateCohomology M 0) := by
  classical
  letI : Module ℤ M.V := M.hV2
  let nrm := M.ρ.norm
  have hnorm : nrm = 1 := by
    have h : nrm = ∑ g : G, M.ρ g := rfl
    rw [h]
    have h2 : (∑ g : G, M.ρ g) = ∑ g : G, (1 : Module.End ℤ M.V) :=
      Finset.sum_congr rfl (fun g _ => by rw [Subsingleton.elim g 1, map_one])
    rw [h2, Finset.sum_const]
    have hcard : (Finset.univ : Finset G).card = 1 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hcard, one_smul]
  let inv := M.ρ.invariants
  letI : Module ℤ ↥inv := inv.module
  obtain ⟨e⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
    G M.V _ _ M.hV1 M.hV2 M.ρ
  let p := Submodule.comap inv.subtype (LinearMap.range nrm)
  have htop : p = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_comap, LinearMap.mem_range]
    exact ⟨(x : M.V), by rw [hnorm]; rfl⟩
  rw [Equiv.subsingleton_congr (LinearEquiv.toEquiv e)]
  rw [Submodule.Quotient.subsingleton_iff]
  exact htop

/-- **The first Tate cohomology of a representation of a trivial group vanishes.**  In positive
degree the Tate cohomology agrees with group cohomology, and the group cohomology of the trivial
group vanishes in positive degrees. -/
theorem subsingleton_tateCohomology_one_of_subsingleton {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton (tateCohomology M 1) := by
  haveI : Subsingleton (groupCohomology M 1) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_groupCohomology_succ_of_subsingleton M 0)
  have e : tateCohomology M (1 : ℤ) ≅ groupCohomology M 1 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M
  exact e.toLinearEquiv.injective.subsingleton

/-- **The Herbrand quotient computation for the trivial extension `K / K`.**

The Galois group `Gal(K/K)` is trivial, so `Ĥ⁰` and `Ĥ¹` of `C_K` are both of cardinality `1`,
while `[K : K] = 1`; the Herbrand quotient computation `|Ĥ⁰| = [K : K] · |Ĥ¹|` is therefore
`1 = 1 · 1`. -/
theorem herbrandQuotient_self (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFT.HerbrandQuotient K K := by
  haveI hsub : Subsingleton (K ≃ₐ[K] K) := subsingleton_algEquiv_self K
  have h1 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K K) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨subsingleton_tateCohomology_one_of_subsingleton _, ⟨0⟩⟩
  have h0 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K K) 0) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨subsingleton_tateCohomology_zero_of_subsingleton _, ⟨0⟩⟩
  refine ⟨?_, ?_⟩
  · rw [h1]
    norm_num
  · rw [h0, h1, Module.finrank_self]

end NK.GlobalCFTdeep.Audit

end
