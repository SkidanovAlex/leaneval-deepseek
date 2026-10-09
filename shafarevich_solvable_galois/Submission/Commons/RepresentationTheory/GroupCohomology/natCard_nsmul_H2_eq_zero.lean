import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.RepresentationTheory.GroupCohomology.isZero_iff_subsingleton_moduleCat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The order of a finite group annihilates the positive-degree cohomology

For a finite group `G` of order `n` and any `G`-module `A`, the integer `n` acts as zero on the
group cohomology `Hᵏ(G, A)` for every `k ≥ 1` (the classical proof composes restriction to the
trivial subgroup, which vanishes in positive degrees, with corestriction, using
`cor ∘ res = [G : H]` for `H = 1`).

This file proves the case `k = 2` by an explicit computation with the standard complex of
inhomogeneous cochains, and deduces the general case `k = n + 1` from the corestriction identity
`res ≫ cor = index • 𝟙` of the commons.

For `k = 2`, if `f : G × G → A` is a `2`-cocycle, i.e.

`f (g * h, j) + f (g, h) = g • f (h, j) + f (g, h * j)`,

then `Nat.card G • f` is a `2`-coboundary, namely the differential `d¹` of the `1`-cochain

`g ↦ ∑ s : G, f (g, s)`.

Indeed, summing the cocycle identity over `s : G` turns the `g`-action into a telescoping sum,

`g • ∑ s, f (h, s) = ∑ s, f (g * h, s) + Nat.card G • f (g, h) - ∑ s, f (g, s)`,

because `s ↦ h * s` is a bijection of `G`.  Consequently `Nat.card G` kills `H²(G, A)` — and, more
generally, `(Nat.card G : k) • x = 0` for representations over an arbitrary commutative ring `k`,
since the same computation shows that `(Nat.card G : k) • f` is a coboundary in that setting.

## Main results

* `natCard_nsmul_H2_eq_zero`: `Nat.card G • x = 0` for every `x : H²(G, A)`, `A : Rep ℤ G`.
* `natCard_cast_smul_H2_eq_zero`: the coefficient-general form `(Nat.card G : k) • x = 0`,
  `A : Rep k G`.
* `natCard_nsmul_groupCohomology_succ_eq_zero`: `Nat.card G • x = 0` for every `x : Hⁿ⁺¹(G, A)`,
  deduced from corestriction.
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

/-- **The crucial cochain identity.**  If `f` is a `2`-cocycle of the `G`-representation `A`, then
the `1`-cochain `g ↦ ∑ s : G, f (g, s)` has differential `d¹` equal to `Nat.card G • f`; that is,
`Nat.card G • f` is a `2`-coboundary.

The proof is the standard telescoping-sum argument: sum the cocycle identity
`f (g * h, s) + f (g, h) = g • f (h, s) + f (g, h * s)` over `s : G`, and use that `s ↦ h * s` is a
bijection of `G` (with `Finset` cardinality `Nat.card G`). -/
lemma d₁₂_sum_eq_natCard_nsmul {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (f : groupCohomology.cocycles₂ A) (g₀ g₁ : G) :
    (groupCohomology.d₁₂ A (fun g => ∑ s : G, f (g, s)) : G × G → A) (g₀, g₁)
      = Nat.card G • f (g₀, g₁) := by
  change A.ρ g₀ (∑ s : G, f (g₁, s)) - (∑ s : G, f (g₀ * g₁, s)) + (∑ s : G, f (g₀, s))
      = Nat.card G • f (g₀, g₁)
  have key : A.ρ g₀ (∑ s : G, f (g₁, s))
      = (∑ s : G, f (g₀ * g₁, s)) + Nat.card G • f (g₀, g₁) - ∑ s : G, f (g₀, s) := by
    rw [map_sum]
    rw [show (∑ s : G, A.ρ g₀ (f (g₁, s)))
        = ∑ s : G, (f (g₀ * g₁, s) + f (g₀, g₁) - f (g₀, g₁ * s)) from
      Finset.sum_congr rfl (fun s _ => by
        have hf := (groupCohomology.mem_cocycles₂_iff (A := A) (⇑f)).1 f.2 g₀ g₁ s
        rw [hf]; abel)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    rw [show (∑ s : G, f (g₀, g₁ * s)) = ∑ t : G, f (g₀, t) from
      Equiv.sum_comp (Equiv.mulLeft g₁) (fun t => f (g₀, t)), Nat.card_eq_fintype_card]
  rw [key]; abel

/-- **`Nat.card G • y` is a coboundary for every `2`-cocycle `y`.**  This is the cochain-level form
of the vanishing of multiplication by the group order on `H²`. -/
lemma mem_coboundaries₂_natCard_nsmul {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (y : groupCohomology.cocycles₂ A) :
    ⇑(Nat.card G • y) ∈ groupCohomology.coboundaries₂ A := by
  refine ⟨fun g => ∑ s : G, y (g, s), ?_⟩
  show ((groupCohomology.d₁₂ A) (fun g => ∑ s : G, y (g, s)) : G × G → A) = ⇑(Nat.card G • y)
  funext p
  obtain ⟨g₀, g₁⟩ := p
  rw [show (⇑(Nat.card G • y) : G × G → A) (g₀, g₁) = Nat.card G • y (g₀, g₁) from rfl]
  exact d₁₂_sum_eq_natCard_nsmul A y g₀ g₁

/-- **The order of a finite group kills `H²`, with arbitrary coefficients.**  For a finite group `G`
and a `k[G]`-module `A` (`k` any commutative ring), every element of `H²(G, A)` is annihilated by
the order of `G`. -/
theorem natCard_cast_smul_H2_eq_zero {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (x : groupCohomology A 2) : (Nat.card G : k) • x = 0 := by
  refine groupCohomology.H2_induction_on x ?_
  intro y
  have hmap : Nat.card G • (groupCohomology.H2π A y) = groupCohomology.H2π A (Nat.card G • y) :=
    (map_nsmul (groupCohomology.H2π A).hom (Nat.card G) y).symm
  have hcast : (Nat.card G : k) • (groupCohomology.H2π A y) =
      Nat.card G • (groupCohomology.H2π A y) :=
    Nat.cast_smul_eq_nsmul k (Nat.card G) _
  rw [hcast, hmap, groupCohomology.H2π_eq_zero_iff]
  exact mem_coboundaries₂_natCard_nsmul A y

/-- The group order kills `H²`: for a finite group `G` and any `ℤ[G]`-module `A`, every element of
the second group cohomology is annihilated by the order of `G`. -/
theorem natCard_nsmul_H2_eq_zero {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (x : groupCohomology A 2) : Nat.card G • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℤ (Nat.card G) x]
  exact natCard_cast_smul_H2_eq_zero A x

section GeneralDegree

set_option backward.isDefEq.respectTransparency false

/-- **The order of a finite group annihilates all positive-degree group cohomology.**
For a finite group `G` and a `ℤ[G]`-module `A`, every element of `H^{n+1}(G, A)` is annihilated by
the order of `G`.

This is derived from the corestriction identity of the shared commons, applied to the trivial
subgroup: `res ≫ cor = 1 • 𝟙` on `H^{n+1}(G, A)`, while `H^{n+1}(1, A) = 0`. -/
theorem natCard_nsmul_groupCohomology_succ_eq_zero {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (n : ℕ) (x : groupCohomology A (n + 1)) : Nat.card G • x = 0 := by
  have hsub : Subsingleton (groupCohomology (Rep.res (⊥ : Subgroup G).subtype A) (n + 1)) :=
    (isZero_iff_subsingleton_moduleCat _).1
      (isZero_groupCohomology_succ_of_subsingleton (Rep.res (⊥ : Subgroup G).subtype A) n)
  have h := NU.cor_resNatTrans_comp_apply (⊥ : Subgroup G) A (n + 1) x
  have h0 : (ConcreteCategory.hom
      ((groupCohomology.resNatTrans ℤ (⊥ : Subgroup G).subtype (n + 1)).app A)) x = 0 :=
    Subsingleton.elim (α := ↥(groupCohomology (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))) _ _
  rw [show (ConcreteCategory.hom
        ((groupCohomology.resNatTrans ℤ (⊥ : Subgroup G).subtype (n + 1)).app A ≫
          NU.cor (⊥ : Subgroup G) A (n + 1))) x
      = (ConcreteCategory.hom (NU.cor (⊥ : Subgroup G) A (n + 1)))
          ((ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (⊥ : Subgroup G).subtype (n + 1)).app A)) x)
      from ConcreteCategory.comp_apply _ _ x,
    h0, Subgroup.index_bot, map_zero] at h
  exact h.symm

end GeneralDegree

end Commons.RepresentationTheory.GroupCohomology
