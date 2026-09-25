/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `H¹(Gal(E/F), C_E) = 0` for `p`-group level groups, from the cyclic input

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 4, §11).

This module proves the **`p`-group case of the vanishing of `H¹` of the idèle class group**:

  for a finite Galois extension `E / F` of number fields whose Galois group is a `p`-group,
  `H¹(Gal(E/F), C_E) = 0`,

from the *cyclic* input `NK.HassePrinciple.CyclicInput` — the Hasse norm theorem
(`NK.HassePrinciple.HasseNormTheorem`) together with the Herbrand quotient of `C_L` for cyclic
extensions (`NK.GlobalCFT.HerbrandQuotient`).  The cyclic case itself is the proved
`NK.HassePrinciple.subsingleton_tateCohomology_one_of_cyclic`.

## Why this is the right statement

With Shapiro's lemma for the idèles (`H²(Γ, 𝕀_L) ≅ ∏_w H²(Γ_w, L_wˣ)`) the long exact sequence of
`0 → Lˣ → 𝕀_L → C_L → 0` identifies `H¹(Γ, C_L)` with the kernel of the relative localisation
`H²(Γ, Lˣ) → ∏_w H²(Γ_w, L_wˣ)`, i.e. the *relative Hasse–Brauer–Noether theorem* for `L/K`.
So the theorem of this file is exactly the classical "second inequality / Hasse principle" input at
the `p`-primary levels, and it is what the classical proof (Milne, *CFT*, VII.7.1) supplies.

## The proof

Strong induction on `Nat.card (E ≃ₐ[F] E)`.

* If the group is trivial, `H¹` of the trivial group vanishes.
* Otherwise choose `N ◁ Γ` with `Γ / N ≅ ℤ/p`, `M = E^N`
  (`NK.HassePrinciple.exists_normal_subgroup_index_eq_prime`).  The
  inflation–restriction sequence in degree one,
  `H¹(Γ/N, C_E^N) → H¹(Γ, C_E) → H¹(N, C_E)`, has vanishing ends:

  - the right end is the induction hypothesis applied to the extension `E / M` (whose group is
    `N ≅ Gal(E/M)`, a `p`-group of smaller order);
  - the left end, `H¹(Γ/N, C_E^N) = H¹(Γ/N, C_M)`, vanishes by the *cyclic* case, transported
    along the equivariant identification `C_E^N ≅ C_M`
    (`NK.HassePrinciple.repIso_quotientToInvariants_fixedField`).

  Hence `H¹(Γ, C_E) = 0`.

Everything is over `Type 0` because Mathlib's Tate cohomology ties the universes of the coefficient
ring and of the group.
-/

import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.HassePrinciple.subsingleton_tateCohomology_one_of_cyclic
import Submission.NK.HassePrinciple.exists_normal_subgroup_index_eq_prime
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField

open CategoryTheory
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace NK.HassePrinciple

universe u

structure CyclicInput (p : ℕ) : Prop where
  hp : p.Prime
  hasse_norm : HasseNormTheorem.{0}
  herbrand : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L], IsCyclic (L ≃ₐ[K] L) → HerbrandQuotient K L

variable {p : ℕ}

theorem subsingleton_groupCohomology_one_of_ends {Γ : Type} [Group Γ] [Finite Γ]
    (A : Rep ℤ Γ) (N : Subgroup Γ) [N.Normal]
    (h1 : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (h2 : Subsingleton (groupCohomology (A.quotientToInvariants N) 1)) :
    Subsingleton (groupCohomology A 1) := by
  haveI h1' : Subsingleton ↥(groupCohomology.H1InfRes A N).X₃ := h1
  haveI h2' : Subsingleton ↥(groupCohomology.H1InfRes A N).X₁ := h2
  have hex : LinearMap.ker (groupCohomology.H1InfRes A N).g.hom ≤
      LinearMap.range (groupCohomology.H1InfRes A N).f.hom := by
    have h := groupCohomology.H1InfRes_exact A N
    rwa [ShortComplex.moduleCat_exact_iff_ker_sub_range] at h
  have hzero : ∀ x : ↥(groupCohomology.H1InfRes A N).X₂, x = 0 := by
    intro x
    have hx : x ∈ LinearMap.ker (groupCohomology.H1InfRes A N).g.hom := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (hex hx)
    rw [← hz, show z = 0 from Subsingleton.elim _ _, map_zero]
  haveI : Subsingleton ↥(groupCohomology.H1InfRes A N).X₂ := ⟨fun x y => by rw [hzero x, hzero y]⟩
  exact ‹Subsingleton ↥(groupCohomology.H1InfRes A N).X₂›

/-- **`H¹` of the idèle class group vanishes for `p`-group level groups.**  For a finite Galois
extension `E / F` of number fields whose Galois group is a `p`-group, `H¹(Gal(E/F), C_E) = 0`,
from the cyclic input `CyclicInput p` (the Hasse norm theorem together with the Herbrand quotient
of `C_L` for cyclic `L/K`).  The proof is the strong induction on the order of the group described
in the module docstring: for `N ◁ Γ` with `Γ ⧸ N ≅ ℤ/p`, the right end
`H¹(N, C_E) = 0` of the inflation–restriction sequence is the induction hypothesis at the extension
`E / E^N`, and the left end `H¹(Γ ⧸ N, C_E^N) = H¹(Γ ⧸ N, C_{E^N}) = 0` is the cyclic case. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup (hin : CyclicInput p)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hG : IsPGroup p (E ≃ₐ[F] E)) :
    Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) := by
  haveI : Fact p.Prime := ⟨hin.hp⟩
  have key : ∀ n, ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      Nat.card (E ≃ₐ[F] E) = n → IsPGroup p (E ≃ₐ[F] E) →
      Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F E _ _ _ _ _ _ _ hcard hG
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · -- nontrivial
        haveI hnt : Nontrivial (E ≃ₐ[F] E) := by
          rw [← not_subsingleton_iff_nontrivial]
          intro hsub
          rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩] at hcard
          omega
        obtain ⟨N, hNnorm, hNindex⟩ := exists_normal_subgroup_index_eq_prime hG hnt
        haveI := hNnorm
        have hNtop : N ≠ ⊤ := by
          intro htop
          rw [htop, Subgroup.index_top] at hNindex
          exact hin.hp.ne_one hNindex.symm
        have hNlt : Nat.card ↥N < n := by
          have hmul : Nat.card ↥N * N.index = Nat.card (E ≃ₐ[F] E) := N.card_mul_index
          rw [hNindex, hcard] at hmul
          have hlt : Nat.card ↥N < Nat.card ↥N * p := by
            calc Nat.card ↥N = Nat.card ↥N * 1 := (mul_one _).symm
              _ < Nat.card ↥N * p := Nat.mul_lt_mul_of_pos_left hin.hp.one_lt Nat.card_pos
          rw [hmul] at hlt
          exact hlt
        -- the intermediate field
        set M : IntermediateField F E := IntermediateField.fixedField N with hM
        -- (1) the `N`-side, by the induction hypothesis at the extension `E / M`
        have hMcard : Nat.card (E ≃ₐ[↥M] E) = Nat.card ↥N :=
          (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv).symm
        have hMN : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥M E) 1) :=
          ih (Nat.card ↥N) hNlt hMcard
            ((hG.to_subgroup N).of_equiv (IntermediateField.subgroupEquivAlgEquiv N))
        have h1' : Subsingleton (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 1) := by
          haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥M E) 1) := hMN
          exact ((groupCohomology.mapIso (G := ↥N) (H := (E ≃ₐ[↥M] E))
            (A := IdeleClassGroup.rep ↥M E)
            (B := Rep.res N.subtype (IdeleClassGroup.rep F E))
            (IntermediateField.subgroupEquivAlgEquiv N) (LinearEquiv.refl ℤ _)
            (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton
        -- (2) the quotient side, from the cyclic case for `M / F`
        haveI : IsGalois F ↥M := IsGalois.of_fixedField_normal_subgroup N
        have hQcard : Nat.card ((E ≃ₐ[F] E) ⧸ N) = p := by
          rw [← Subgroup.index_eq_card]; exact hNindex
        have hcyc : IsCyclic (↥M ≃ₐ[F] ↥M) := by
          have h2 : Nat.card (↥M ≃ₐ[F] ↥M) = p := by
            rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv, hQcard]
          exact isCyclic_of_card_dvd_prime (p := p) (by rw [h2])
        have hcycT : Subsingleton (tateCohomology (IdeleClassGroup.rep F ↥M) 1) :=
          subsingleton_tateCohomology_one_of_cyclic hin.hasse_norm (hin.herbrand hcyc)
        have hMq : Subsingleton (groupCohomology (IdeleClassGroup.rep F ↥M) 1) := by
          haveI : Subsingleton (tateCohomology (IdeleClassGroup.rep F ↥M) 1) := hcycT
          exact (((TateCohomology.isoGroupCohomology (R := ℤ)
            (G := (↥M ≃ₐ[F] ↥M)) 1).app (IdeleClassGroup.rep F ↥M)).toLinearEquiv).symm.injective.subsingleton
        obtain ⟨hiso⟩ := repIso_quotientToInvariants_fixedField (K := F) (L := E) N
        have hB : Subsingleton (groupCohomology
            (Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
              (IdeleClassGroup.rep F ↥M)) 1) := by
          haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep F ↥M) 1) := hMq
          exact ((groupCohomology.mapIso
            (G := (E ≃ₐ[F] E) ⧸ N) (H := (↥M ≃ₐ[F] ↥M))
            (A := IdeleClassGroup.rep F ↥M)
            (B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
              (IdeleClassGroup.rep F ↥M))
            (IsGalois.normalAutEquivQuotient N) (LinearEquiv.refl ℤ _)
            (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton
        have h2' : Subsingleton (groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 1) := by
          refine @Function.Injective.subsingleton _ _ _
            (((groupCohomology.functor ℤ ((E ≃ₐ[F] E) ⧸ N) 1).mapIso hiso).toLinearEquiv).injective ?_
          exact hB
        exact subsingleton_groupCohomology_one_of_ends (IdeleClassGroup.rep F E) N h1' h2'
      · -- trivial
        have hle : n ≤ 1 := by omega
        have hle' : Nat.card (E ≃ₐ[F] E) ≤ 1 := by rw [hcard]; exact hle
        have hcard1 : Nat.card (E ≃ₐ[F] E) = 1 := le_antisymm hle' Nat.card_pos
        haveI : Subsingleton (E ≃ₐ[F] E) := (Nat.card_eq_one_iff_unique.mp hcard1).1
        have h : CategoryTheory.Limits.IsZero
            (groupCohomology (IdeleClassGroup.rep F E) (0+1)) :=
          isZero_groupCohomology_succ_of_subsingleton _ 0
        exact ModuleCat.isZero_iff_subsingleton.mp h
  exact key (Nat.card (E ≃ₐ[F] E)) rfl hG

end NK.HassePrinciple
