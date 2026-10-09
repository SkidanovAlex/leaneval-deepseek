import Mathlib
import Submission.Work.SSGRoute.E7Fin.RedLattice.InvDimFunctional
import Submission.Work.SSGRoute.E7Fin.RedLattice.exists_equivariant_section
import Submission.Work.SSGRoute.E7Fin.RedLattice.exists_equivariant_prod_iso
import Submission.Work.SSGRoute.E7Fin.diagTensorInvariantsEngine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin.RedLattice

open Work.ArtinInduction.LatticeModp

/-- **Additivity of `X ↦ dim (X ⊗ N)^G` for `p ∤ |G|`.**

A `G`-equivariant short exact sequence of finite `𝔽_p[G]`-modules splits (Maschke: the
`G`-equivariant surjection carries a `G`-equivariant section, `exists_equivariant_section`),
so `N₂ ≅ N₁ × N₃` `G`-equivariantly (`exists_equivariant_prod_iso`).  The invariant
`X ↦ dim (X ⊗ N)^G` is transported along that isomorphism and is additive over the product
(`diagTensorInvariants_eq_of_equiv`, `diagTensorInvariants_prod`), giving the claim. -/
theorem invDimFunctional_isAddInv (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (hcop : Nat.Coprime (Fintype.card G) p)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Work.ArtinInduction.LatticeModp.IsAddInv
      (Work.SSGRoute.E7Fin.RedLattice.invDimFunctional p G N) := by
  intro N₁ N₂ N₃ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i j hi hj hker hieq hjeq
  -- Maschke: the equivariant surjection `j` admits an equivariant section `s`
  obtain ⟨s, hsj, hseq⟩ := exists_equivariant_section p hcop j hjeq hj
  -- hence `N₂ ≅ N₁ × N₃` as `𝔽_p[G]`-modules
  obtain ⟨e, he⟩ := exists_equivariant_prod_iso p i j hi hker hieq hjeq s hsj hseq
  -- unfold the invariant `X ↦ dim (X ⊗ N)^G`
  have h₂ : (Work.SSGRoute.E7Fin.RedLattice.invDimFunctional p G N) N₂ =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) N₂ N)) := rfl
  have h₁ : (Work.SSGRoute.E7Fin.RedLattice.invDimFunctional p G N) N₁ =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) N₁ N)) := rfl
  have h₃ : (Work.SSGRoute.E7Fin.RedLattice.invDimFunctional p G N) N₃ =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) N₃ N)) := rfl
  -- transport along `e : N₁ × N₃ ≅ N₂` and split the product
  rw [h₂, h₁, h₃, ← Work.SSGRoute.E7Fin.diagTensorInvariants_eq_of_equiv (N := N) e he,
    Work.SSGRoute.E7Fin.diagTensorInvariants_prod N₁ N₃ N]
  push_cast
  ring

end Work.SSGRoute.E7Fin.RedLattice
