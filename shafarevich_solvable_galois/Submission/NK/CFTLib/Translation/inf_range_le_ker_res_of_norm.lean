import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.Translation.translation_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Translation

set_option linter.unusedVariables false

/-- **The translation between the `H⁰`- and the `H²`-forms of the reciprocity input.**

Let `G` be a finite group, `M, N ◁ G` complementary normal subgroups (`M ⊔ N = ⊤`, `M ⊓ N = ⊥`)
with `N` cyclic, and `A` a `ℤ`-linear representation of `G` with `H¹(M, A) = H¹(N, A) = 0`.

If every `G`-invariant element of `A` is a norm for `N` (i.e. lies in the image of the norm
endomorphism `Σ_{n ∈ N} ρ(n)`), then the range of the inflation along `M` is contained in the
kernel of the restriction along `N`.

This bridges the two forms of the reciprocity input used in Route B of the global fundamental
class (`Submission/Work/CFTLib/RouteB/plan.lean`, `Submission/Work/CFTLib/GFC/`):

* (**) `range(inf_M) ≤ ker(res_N)`, the form consumed by
  `Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res`;
* (**') `A^G ⊆ N_N A`, the arithmetic statement `C_K ⊆ N_{Ω/L}C_Ω` for idèle class groups.

Proof sketch: since `M ⊔ N = ⊤` and `M ⊓ N = ⊥`, the projection `G → G ⧸ M` restricts to an
isomorphism `N ≅ G ⧸ M`; at the level of cochains `res_N ∘ inf_M` is therefore the map induced by
`π|_N` together with the coefficient inclusion `A^M ↪ A`, so `range(inf_M) ≤ ker(res_N)` is
equivalent to the vanishing of `coeff : H²(N, A^M) → H²(N, A)`. Because `N` is cyclic, the
periodicity isomorphism `H²(N, X) ≅ Ĥ⁰(N, X) = X^N/N_N X` (Mathlib's
`Rep.FiniteCyclicGroup.groupCohomologyπEven`) is natural in the coefficients, so `coeff = 0` is
equivalent to the vanishing of `A^G/N_N(A^M) → A^N/N_N A`, i.e. to `A^G ⊆ N_N A`. -/
theorem inf_range_le_ker_res_of_norm {G : Type} [Group G] [Fintype G]
    (M N : Subgroup G) [M.Normal] [N.Normal] [IsCyclic N] [Fintype N]
    (hMN : M ⊔ N = ⊤) (hdisj : M ⊓ N = ⊥) (A : Rep ℤ G)
    (h1M : Subsingleton (groupCohomology (Rep.res M.subtype A) 1))
    (h1N : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (hnorm : ∀ a : A.V, (∀ g : G, A.ρ g a = a) →
      ∃ b : A.V, (∑ n : N, A.ρ (n : G) b) = a) :
    LinearMap.range ((groupCohomology.infNatTrans ℤ M 2).app A).hom ≤
      LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype 2).app A).hom := by
  rw [LinearMap.range_le_ker_iff]
  exact H2_comp_eq_zero M N hMN A hnorm

end NK.CFTLib.Translation
