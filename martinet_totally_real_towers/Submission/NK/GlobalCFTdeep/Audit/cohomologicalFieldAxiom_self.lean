/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass

/-!
# The cohomological field axiom for the trivial extension `K / K`

The cohomological form of the class-formation axioms
(`NK.GlobalCFT.CohomologicalFieldAxiom K L`) asks, for a finite Galois extension `L / K`,
that `H¹(H, C_L) = 0` and `|H²(H, C_L)| = |H|` for every subgroup `H ≤ Gal(L/K)`, and that
`H²(Gal(L/K), C_L)` contain a fundamental class of order `[L : K]`.

For the **trivial extension** `L = K` all of this is a formal triviality, and this file proves it
unconditionally (it is the satisfiability witness for the axiom: the axioms are not vacuous):

* the Galois group `K ≃ₐ[K] K` is trivial — every `K`-algebra automorphism of `K` fixes `K`
  pointwise and `algebraMap K K` is the identity — so its only subgroup is `⊥` and its cardinality
  is `1`;
* the restriction of the Galois module `C_K` to the trivial subgroup `⊥` has vanishing cohomology
  in every positive degree (`NK.GlobalCFTdeep.subsingleton_groupCohomology_bot`, resp. its
  cardinality form `NK.GlobalCFTdeep.natCard_groupCohomology_bot`);
* `H²(K ≃ₐ[K] K, C_K) = 0`, so `α = 0` is a fundamental class of order `1 = [K : K]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.GlobalCFTdeep.Audit

open NK.GlobalCFT

/-- The `K`-algebra automorphism group of `K` is trivial: a `K`-algebra automorphism of `K` fixes
`K` pointwise, and `algebraMap K K` is the identity. -/
theorem subsingleton_algEquiv_self (K : Type) [Field K] : Subsingleton (K ≃ₐ[K] K) :=
  ⟨fun σ τ => AlgEquiv.ext fun x => by
    have hσ : σ x = x := by simpa using σ.commutes x
    have hτ : τ x = x := by simpa using τ.commutes x
    rw [hσ, hτ]⟩

/-- Every subgroup of `K ≃ₐ[K] K` is the trivial subgroup. -/
theorem eq_bot_of_subgroup_algEquiv_self (K : Type) [Field K] [NumberField K]
    (H : Subgroup (K ≃ₐ[K] K)) : H = ⊥ := by
  have hsingle := subsingleton_algEquiv_self K
  ext x
  simp only [Subgroup.mem_bot]
  exact ⟨fun _ => Subsingleton.elim x 1, fun hx => hx ▸ H.one_mem⟩

/-- **The cohomological field axiom holds for the trivial extension `K / K`.**

Since `Gal(K/K) = K ≃ₐ[K] K` is trivial, its only subgroup is `⊥`; the axioms at `⊥` are
`NK.GlobalCFTdeep.subsingleton_groupCohomology_bot` and
`NK.GlobalCFTdeep.natCard_groupCohomology_bot`, while `H²` itself vanishes, so that `0` is a
fundamental class of order `1 = [K : K]`. -/
theorem cohomologicalFieldAxiom_self (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFT.CohomologicalFieldAxiom K K := by
  have hsingle := subsingleton_algEquiv_self K
  refine ⟨?_, ?_, ?_⟩
  · intro H
    rw [eq_bot_of_subgroup_algEquiv_self K H]
    exact NK.GlobalCFTdeep.subsingleton_groupCohomology_bot
      (NK.GlobalCFT.IdeleClassGroup.rep K K) 0
  · intro H
    rw [eq_bot_of_subgroup_algEquiv_self K H]
    rw [NK.GlobalCFTdeep.natCard_groupCohomology_bot
      (NK.GlobalCFT.IdeleClassGroup.rep K K) 1, Subgroup.card_bot]
  · refine ⟨0, ?_⟩
    rw [addOrderOf_zero]
    exact (Nat.card_eq_one_iff_unique.mpr ⟨hsingle, ⟨1⟩⟩).symm

end NK.GlobalCFTdeep.Audit
