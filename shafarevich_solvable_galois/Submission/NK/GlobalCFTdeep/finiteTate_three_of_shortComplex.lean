import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the Tate cohomology of the quotient term

Let `G` be a finite **cyclic** group and `0 → X₁ → X₂ → X₃ → 0` a short exact sequence of
`ℤ[G]`-modules.  If the two Tate cohomology groups `Ĥ⁰(G, X₁)`, `Ĥ¹(G, X₁)` and `Ĥ⁰(G, X₂)`,
`Ĥ¹(G, X₂)` are finite, then so are `Ĥ⁰(G, X₃)` and `Ĥ¹(G, X₃)`.

This is the "finiteness propagates to the quotient" half of the standard long exact sequence in
Tate cohomology.  Writing out the relevant part of the long exact sequence
(`TateCohomology.exact₃`, the exactness at the middle term of a short exact sequence of
representations, transported to the Tate complex):

  `Ĥⁿ(X₂) --→ Ĥⁿ(X₃) --δₙ→ Ĥⁿ⁺¹(X₁)`

one has `ker δₙ = im(gₙ)` (an image of a finite module, hence finite) and
`Ĥⁿ(X₃) ⧸ ker δₙ ≃ im(δₙ) ⊆ Ĥⁿ⁺¹(X₁)` (a submodule of a finite module, hence finite); an
extension of two finite modules is finite (the two lemmas below).  For `n = 1` the target of `δ₁`
is `Ĥ²(G, X₁)`, which is finite because `G` is cyclic: two-periodicity gives
`|Ĥ²(G, X₁)| = |H²(G, X₁)| = |Ĥ⁰(G, X₁)|` (the degree-two case of the periodicity of the
cohomology of a cyclic group, `natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic`),
and `Ĥ⁰(G, X₁)` is finite by hypothesis.

No periodicity isomorphism is needed in degree `0`: there `δ₀` lands in `Ĥ¹(G, X₁)` directly.

## Main result

* `finiteTate_three_of_shortComplex`: `FiniteTate X₁ → FiniteTate X₂ → FiniteTate X₃`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

/-- **The image of a linear map with finite domain is finite.** -/
lemma finite_range_of_finite_domain {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (φ : M →ₗ[ℤ] N) [Finite M] :
    Finite ↥(LinearMap.range φ) :=
  Finite.of_surjective (fun x : M => (⟨φ x, ⟨x, rfl⟩⟩ : LinearMap.range φ))
    (fun y => by obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩)

/-- **An extension of finite modules is finite**: a `ℤ`-module `M` whose kernel and image under a
linear map into another module are both finite is itself finite.  Indeed the quotient
`M ⧸ ker φ` is isomorphic to `range φ`, so `Nat.card M = Nat.card (ker φ) * Nat.card (M ⧸ ker φ)`
is non-zero, and a type with non-zero `Nat.card` is finite (`Nat.finite_of_card_ne_zero`). -/
lemma finite_of_finite_ker_of_finite_range {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (φ : M →ₗ[ℤ] N)
    (hk : Finite ↥(LinearMap.ker φ)) (hr : Finite ↥(LinearMap.range φ)) : Finite M := by
  have hq : Finite (M ⧸ LinearMap.ker φ) :=
    Finite.of_equiv _ (LinearMap.quotKerEquivRange φ).symm.toEquiv
  have hcard : Nat.card M = Nat.card ↥(LinearMap.ker φ) * Nat.card (M ⧸ LinearMap.ker φ) :=
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard]
  exact Nat.mul_ne_zero
    (Nat.card_ne_zero.2 ⟨⟨0, (LinearMap.mem_ker).2 (map_zero φ)⟩, hk⟩)
    (Nat.card_ne_zero.2 ⟨⟨0⟩, hq⟩)

/-- **Finiteness of the Tate cohomology of the quotient term.**  For a finite cyclic group `G` and
a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `ℤ[G]`-modules whose first two terms have finite
Tate cohomology in degrees `0` and `1`, the third term does as well. -/
theorem finiteTate_three_of_shortComplex {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h1 : NK.GlobalCFTdeep.FiniteTate S.X₁) (h2 : NK.GlobalCFTdeep.FiniteTate S.X₂) :
    NK.GlobalCFTdeep.FiniteTate S.X₃ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- `Ĥ²(G, X₁)` is finite: two-periodicity of the cohomology of a cyclic group.
  have h1two : Finite ↥(tateCohomology S.X₁ 2) := by
    refine Nat.finite_of_card_ne_zero ?_
    have hcard : Nat.card ↥(tateCohomology S.X₁ 2) = Nat.card ↥(tateCohomology S.X₁ 0) := by
      have e := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app S.X₁
      refine (Nat.card_congr e.toLinearEquiv.toEquiv).trans ?_
      exact Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
        g hg S.X₁
    rw [hcard]
    exact Nat.card_ne_zero.2 ⟨⟨0⟩, h1.zero⟩
  refine ⟨?_, ?_⟩
  · -- `Ĥ⁰(G, X₃)`: the connecting map lands in `Ĥ¹(G, X₁)`, which is finite.
    have hker : LinearMap.ker (TateCohomology.δ hS 0).hom
        = LinearMap.range ((tateCohomologyFunctor (R := ℤ) (G := G) 0).map S.g).hom :=
      (TateCohomology.exact₃ hS 0).moduleCat_range_eq_ker.symm
    refine finite_of_finite_ker_of_finite_range (φ := (TateCohomology.δ hS 0).hom) ?_ ?_
    · rw [hker]
      haveI : Finite ↥(tateCohomology S.X₂ 0) := h2.zero
      exact finite_range_of_finite_domain _
    · haveI : Finite ↥(tateCohomology S.X₁ (0 + 1)) := h1.one
      exact inferInstance
  · -- `Ĥ¹(G, X₃)`: the connecting map lands in `Ĥ²(G, X₁)`, which is finite by periodicity.
    have hker : LinearMap.ker (TateCohomology.δ hS 1).hom
        = LinearMap.range ((tateCohomologyFunctor (R := ℤ) (G := G) 1).map S.g).hom :=
      (TateCohomology.exact₃ hS 1).moduleCat_range_eq_ker.symm
    refine finite_of_finite_ker_of_finite_range (φ := (TateCohomology.δ hS 1).hom) ?_ ?_
    · rw [hker]
      haveI : Finite ↥(tateCohomology S.X₂ 1) := h2.one
      exact finite_range_of_finite_domain _
    · haveI : Finite ↥(tateCohomology S.X₁ (1 + 1)) := h1two
      exact inferInstance

end NK.GlobalCFTdeep
