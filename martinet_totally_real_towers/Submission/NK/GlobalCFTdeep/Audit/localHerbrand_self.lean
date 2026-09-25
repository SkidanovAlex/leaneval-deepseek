/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Basic

/-!
# The local Herbrand quotient at the trivial extension `F / F`

`NK.GlobalCFTdeep.LocalHerbrandQuotient` (`Herbrand/Local.lean`) isolates the local input of
Milne's Herbrand-quotient computation, namely

  `|Ĥ⁰(Gal(E/F), Eˣ)| = [E : F] · |Ĥ¹(Gal(E/F), Eˣ)|`

for a finite Galois extension `E/F` of nonarchimedean local fields.  This file is the
*satisfiability witness* for that input: the degenerate case `E = F`, where it must reduce to
`1 = 1 · 1`.

The point is that the group `F ≃ₐ[F] F` is **trivial** for every field `F`: an `F`-algebra
automorphism of `F` is `F`-linear and `algebraMap F F = id`, so it fixes every element, and
moreover `algebraMap F F = id`.  Hence:

* the norm map `N = ∑_{g : F ≃ₐ[F] F} ρ(g)` is `ρ 1 = 1`, so the Tate complex in degree zero
  computes `Ĥ⁰ = M^G ⧸ N(M) = M ⧸ M = 0`;
* in positive degrees the Tate cohomology agrees with group cohomology, which vanishes for a
  trivial group.

Both groups are therefore singletons, and the Herbrand quotient identity holds with
`[F : F] = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace NK.GlobalCFTdeep.Audit

/-- The `F`-algebra automorphism group of `F` is trivial: a `F`-algebra automorphism of `F` fixes
`F` pointwise, and `algebraMap F F` is the identity. -/
theorem subsingleton_algEquiv_self_of_field {F : Type} [Field F] : Subsingleton (F ≃ₐ[F] F) :=
  ⟨fun σ τ => AlgEquiv.ext fun x => by
    have hσ : σ x = x := by simpa using σ.commutes x
    have hτ : τ x = x := by simpa using τ.commutes x
    rw [hσ, hτ]⟩

/-- **The zeroth Tate cohomology of a representation of a trivial group vanishes.**  For a group
`G` with a single element the norm map `N = ∑_{g : G} ρ(g)` is `ρ 1 = 1`, hence the quotient
`Ĥ⁰(G, M) = M^G ⧸ N(M)` computed by `tateCohomology_zero_iso` is `M ⧸ M = 0`. -/
theorem subsingleton_tateCohomology_zero_of_subsingleton' {G : Type} [Group G] [Fintype G]
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
theorem subsingleton_tateCohomology_one_of_subsingleton' {G : Type} [Group G] [Fintype G]
    [Subsingleton G] (M : Rep ℤ G) : Subsingleton (tateCohomology M 1) := by
  haveI : Subsingleton (groupCohomology M 1) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_groupCohomology_succ_of_subsingleton M 0)
  have e : tateCohomology M (1 : ℤ) ≅ groupCohomology M 1 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M
  exact e.toLinearEquiv.injective.subsingleton

/-- **The local Herbrand quotient at the trivial extension `F / F`.**

The Galois group `F ≃ₐ[F] F` is trivial, so `Ĥ⁰(F ≃ₐ[F] F, Fˣ)` and `Ĥ¹(F ≃ₐ[F] F, Fˣ)` are both
of cardinality `1`, while `[F : F] = 1`; the local Herbrand quotient identity
`|Ĥ⁰| = [F : F] · |Ĥ¹|` is therefore `1 = 1 · 1`.  This shows that the input
`NK.GlobalCFTdeep.LocalHerbrandQuotient` is not vacuous. -/
theorem localHerbrand_self {F : Type} [Field F] :
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 0) =
      Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 1) := by
  haveI hsub : Subsingleton (F ≃ₐ[F] F) := subsingleton_algEquiv_self_of_field
  have h0 : Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 0) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_tateCohomology_zero_of_subsingleton' _, ⟨0⟩⟩
  have h1 : Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_tateCohomology_one_of_subsingleton' _, ⟨0⟩⟩
  rw [h0, h1]

end NK.GlobalCFTdeep.Audit
