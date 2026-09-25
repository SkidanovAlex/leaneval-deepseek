import Mathlib
import Submission.Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient

/-!
# Invariant characters of a `ℤ`-representation

Vocabulary for the class-group term of the Shafarevich relation-rank bound: for a finite group `G`
acting `ℤ`-linearly on an abelian group `V`, the space of `G`-invariant additive characters
`V → 𝔽_p`.  For `V = Cl(𝓞 K)` with the canonical `Gal(K/F)`-action this is
`Work.CFTLib.clInvariantChar F K p`.
-/

namespace Work.CFTLib

open CategoryTheory

/-- **The `G`-invariant additive characters of a `ℤ`-representation.**  For a representation
`A : Rep ℤ G` and a natural number `p`, this is the `𝔽_p`-subspace of `Hom(A, 𝔽_p)` consisting of
the characters fixed by the action of `G`.  Equivalently, it is the space of characters killed by
the augmentation subgroup `I_G A`. -/
noncomputable def invariantHoms {G : Type} [Group G] (A : Rep ℤ G) (p : ℕ) :
    Submodule (ZMod p) (A.V →+ ZMod p) where
  carrier := {χ | ∀ (g : G) (x : A.V), χ ((A.ρ g) x) = χ x}
  zero_mem' := by intro g x; simp
  add_mem' := by
    intro χ ψ hχ hψ g x
    simp only [Set.mem_ofPred_eq] at hχ hψ ⊢
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hχ g x, hψ g x]
  smul_mem' := by
    intro a χ hχ g x
    simp only [Set.mem_ofPred_eq] at hχ ⊢
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, hχ g x]

@[simp] lemma mem_invariantHoms {G : Type} [Group G] (A : Rep ℤ G) (p : ℕ)
    (χ : A.V →+ ZMod p) :
    χ ∈ invariantHoms A p ↔ ∀ (g : G) (x : A.V), χ ((A.ρ g) x) = χ x := Iff.rfl

end Work.CFTLib
