import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of `H²(G, B) ⟶ H²(G, k)` for a surjective "order" map

Let `G` be a group and let `ord : B ⟶ trivial k G k` be a morphism of `k`-linear
`G`-representations onto the trivial representation `k` which is surjective on underlying sets.
Let `K = ker ord`.  If the cohomology `Hⁿ⁺¹(G, K)` vanishes, then the induced map
`Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k)` is injective.

This is the relevant part of the long exact cohomology sequence of the short exact sequence
`0 ⟶ K ⟶ B ⟶ k ⟶ 0`: exactness at `Hⁿ⁺¹(G, B)` reads
`im(Hⁿ⁺¹(G, K) ⟶ Hⁿ⁺¹(G, B)) = ker(Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k))`, and the first map has zero source
when `Hⁿ⁺¹(G, K) = 0`, so the second map has zero kernel.  The case `n = 1`, `k = ℤ` is the one
needed for the "order/valuation" maps appearing in the proof of the Neukirch–Uchida theorem.

Mathlib's `Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence` provides
exactly the required exactness statement: a short exact sequence of representations `X` gives a
short exact sequence `X.map (cochainsFunctor k G)` of complexes of inhomogeneous cochains, whose
homology is group cohomology, and `groupCohomology.mapShortComplex₂_exact` is the exactness of
`Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`.  The short exact sequence of representations is here the
kernel sequence `ShortComplex.kernelSequence ord` of the surjective map `ord`.
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory CategoryTheory.Limits

/-- **Injectivity of `Hⁿ⁺¹(ord)`, general form.**  For a surjective morphism
`ord : B ⟶ trivial k G k` of `k`-linear representations with vanishing
`Hⁿ⁺¹(G, ker ord)`, the induced map `Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k)` is injective.

Indeed `0 ⟶ ker ord ⟶ B ⟶ k ⟶ 0` is a short exact sequence of representations, so its long
exact cohomology sequence is exact at `Hⁿ⁺¹(G, B)`:
`Hⁿ⁺¹(G, ker ord) ⟶ Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k)` is exact.  As `Hⁿ⁺¹(G, ker ord) = 0` the first
map is zero, so the kernel of `Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k)` is trivial. -/
theorem mono_map_of_isZero_kernel_succ {k : Type} [CommRing k] {G : Type} [Group G]
    {B : Rep k G} (ord : B ⟶ Rep.trivial k G k) (hsurj : Function.Surjective ord.hom) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero
      (groupCohomology (CategoryTheory.Limits.kernel ord) (n + 1))) :
    CategoryTheory.Mono (groupCohomology.map (MonoidHom.id G) ord (n + 1)) := by
  -- `0 ⟶ ker ord ⟶ B ⟶ k ⟶ 0` is a short exact sequence of `k`-linear `G`-representations.
  have hX : (ShortComplex.kernelSequence ord).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact ord) inferInstance
      ((Rep.epi_iff_surjective ord).2 hsurj)
  -- Exactness of `Hⁿ⁺¹(G, ker ord) ⟶ Hⁿ⁺¹(G, B) ⟶ Hⁿ⁺¹(G, k)`.
  have hex : ((ShortComplex.kernelSequence ord).map
      (groupCohomology.functor k G (n + 1))).Exact :=
    groupCohomology.mapShortComplex₂_exact hX (n + 1)
  -- `Hⁿ⁺¹(G, ker ord)` is zero, so the first map is zero, and an exact short complex whose first
  -- map is zero has monic second map.
  exact hex.mono_g (h.eq_zero_of_src _)

/-- **Injectivity of `H²(ord)`.**  For a surjective morphism `ord : B ⟶ trivial ℤ G ℤ` of
`ℤ`-linear representations with vanishing `H²(G, ker ord)`, the induced map
`H²(G, B) ⟶ H²(G, ℤ)` is injective. -/
theorem mono_map_of_isZero_kernel
    {G : Type} [Group G] [Fintype G]
    {B : Rep ℤ G} (ord : B ⟶ Rep.trivial ℤ G ℤ) (hsurj : Function.Surjective ord.hom)
    (h : CategoryTheory.Limits.IsZero (groupCohomology (CategoryTheory.Limits.kernel ord) 2)) :
    CategoryTheory.Mono (groupCohomology.map (MonoidHom.id G) ord 2) :=
  mono_map_of_isZero_kernel_succ (k := ℤ) ord hsurj 1 h

end Commons.RepresentationTheory.GroupCohomology