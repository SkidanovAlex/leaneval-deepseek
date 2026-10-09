import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The connecting homomorphism is an isomorphism when the middle group is acyclic

Let `G` be a finite group and `0 → X₁ → X₂ → X₃ → 0` a short exact sequence of `ℤ[G]`-modules.
If the Tate cohomology of the middle term vanishes in all degrees, then the connecting
homomorphism of the long exact sequence

`δ : Ĥⁿ(G, X₃) ⟶ Ĥⁿ⁺¹(G, X₁)`

is an isomorphism for every `n`: injectivity comes from exactness at `Ĥⁿ(G, X₃)` (the image of
`Ĥⁿ(G, X₂) = 0`), and surjectivity from exactness at `Ĥⁿ⁺¹(G, X₁)` (which identifies the image of
`δ` with the kernel of the map to the trivial group `Ĥⁿ⁺¹(G, X₂) = 0`).

Mathlib already packages both halves of this argument as `ShortComplex.ShortExact.mono_δ` /
`ShortComplex.ShortExact.epi_δ` (and its conjunction `isIso_δ`) in
`Mathlib.Algebra.Homology.HomologySequence`, applied to the short exact sequence of Tate complexes
supplied by `TateCohomology.map_tateComplexFunctor_shortExact`.  The only translation needed here is
from the hypothesis `Subsingleton` to the `IsZero` form expected by those lemmas, which is
`ModuleCat.isZero_of_subsingleton`.
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Commons.RepresentationTheory.TateCohomology

theorem tateCohomology_iso_of_acyclic_middle {G : Type} [Group G] [Fintype G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : CategoryTheory.ShortComplex.ShortExact S)
    (h : ∀ r : ℤ, Subsingleton (tateCohomology S.X₂ r)) (r : ℤ) :
    Nonempty (tateCohomology S.X₃ r ≃ₗ[ℤ] tateCohomology S.X₁ (r + 1)) := by
  -- The triviality of the middle term in degrees `r` and `r + 1`, in the `IsZero` form expected
  -- by the homology-sequence machinery.
  haveI hr : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology r) := h r
  haveI hr1 : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology (r + 1)) := h (r + 1)
  -- Hence the connecting homomorphism `δ : Ĥʳ(G, X₃) ⟶ Ĥʳ⁺¹(G, X₁)` is a bijection.
  haveI : IsIso (TateCohomology.δ hS r) :=
    CategoryTheory.ShortComplex.ShortExact.isIso_δ
      (TateCohomology.map_tateComplexFunctor_shortExact hS) r (r + 1) rfl
      (ModuleCat.isZero_of_subsingleton _) (ModuleCat.isZero_of_subsingleton _)
  exact ⟨(asIso (TateCohomology.δ hS r)).toLinearEquiv⟩

end Commons.RepresentationTheory.TateCohomology
