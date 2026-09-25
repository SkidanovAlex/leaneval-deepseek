import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.fiveTerm_setup
import Submission.Work.CFTLib.fiveTerm_count
import Submission.Work.CFTLib.fiveTerm_transgression
import Submission.Work.CFTLib.fiveTerm_finiteDim_H2

/-!
# The five-term inflation–restriction sequence: the dimension identity

This file assembles the dimension identity of the five-term inflation–restriction sequence
for a surjective homomorphism `π : G' →* G` of finite groups with trivial `𝔽_p`-coefficients,

`dim im(H²(G) → H²(G')) + dim H¹(N)^{G'} + dim H¹(G) = dim H²(G) + dim H¹(G')`,

and specializes it to the Galois groups of a tower `F ⊆ K ⊆ K'` of finite Galois number
fields, `N = Gal(K'/K)`:

`Work.CFTLib.fiveTerm_finrank`.
-/

namespace Work.CFTLib

open NumberField CategoryTheory
open scoped Classical

noncomputable section

open Representation groupCohomology

/-- Rank–nullity for the inflation `H²(G,𝔽_p) → H²(G',𝔽_p)`. -/
lemma finrank_H2_eq_ker_add_range_inflMap {G G' : Type} [Group G] [Group G'] [Fintype G]
    [Fintype G'] (π : G' →* G) (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (H2 p G)
      = Module.finrank (ZMod p) (LinearMap.ker (inflMap p π))
        + Module.finrank (ZMod p) (LinearMap.range (inflMap p π)) := by
  haveI : Module.Finite (ZMod p) (H2 p G) := by
    have := fiveTerm_finiteDim_H2 (p := p) (G := G); infer_instance
  have hiso : Module.finrank (ZMod p) ((H2 p G) ⧸ LinearMap.ker (inflMap p π))
      = Module.finrank (ZMod p) (LinearMap.range (inflMap p π)) :=
    LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (inflMap p π))
  have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker (inflMap p π))
  omega

/-- **The dimension identity of the five-term inflation–restriction sequence** for a surjective
homomorphism `π : G' →* G` of finite groups. -/
theorem fiveTerm_finrank_abstract (p : ℕ) [Fact p.Prime] {G G' : Type} [Group G] [Group G']
    [Fintype G] [Fintype G'] (π : G' →* G) (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (LinearMap.range (groupCohomology.map π
        (𝟙 _ : Rep.res π (Rep.trivial (ZMod p) G (ZMod p)) ⟶
          Rep.trivial (ZMod p) G' (ZMod p)) 2).hom)
      + Module.finrank (ZMod p) (invCharSubmodule p π.ker)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1)
    = Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G' (ZMod p)) 1) :=
  fiveTerm_finrank_abstract_of_nullity p π hπ
    (finrank_eq_ker_add_range_beta (p := p) π)
    (finrank_eq_ker_add_range_transgression (p := p) π hπ)
    (finrank_H2_eq_ker_add_range_inflMap π p)

end

open NumberField CategoryTheory

theorem fiveTerm_finrank {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (LinearMap.range (groupCohomology.map
        (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K))
        (𝟙 _ : Rep.res (AlgEquiv.restrictNormalHom K) (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) ⟶
          Rep.trivial (ZMod p) (K' ≃ₐ[F] K') (ZMod p)) 2).hom)
      + Module.finrank (ZMod p) (Work.CFTLib.invCharSubmodule p
          (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) 1)
    = Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) 2)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) (K' ≃ₐ[F] K') (ZMod p)) 1) :=
  Work.CFTLib.fiveTerm_finrank_abstract p (AlgEquiv.restrictNormalHom K)
    (AlgEquiv.restrictNormalHom_surjective K')

end Work.CFTLib
