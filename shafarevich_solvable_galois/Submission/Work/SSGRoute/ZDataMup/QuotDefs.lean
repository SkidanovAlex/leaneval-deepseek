import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.Defs
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Definitions shared by the finiteness of `localDataSpace ⧸ localVanish`

The target `Work.SSGRoute.ZDataMup.finite_localDataSpace_quotient` proves that the quotient of the
level-`K` local-data space `localDataSpace K T` by the submodule `localVanish K T` of tuples
vanishing on the local groups `decomp k A ⊓ G_K` is a finite-dimensional `𝔽_p`-vector space.

The quotient is the product over `A ∈ T` of the space of *locally constant* `1`-cocycles on the
level-`K` local group `H_A = decomp k A ⊓ K.fixingSubgroup`, regarded as functions on `H_A`:

* `restrictToSub H` is the linear map restricting a function on `G_k = Ω ≃ₐ[k] Ω` to `H ≤ G_k`;
* `lcCocycleImage K H` is the image of the locally constant `1`-cocycles `localCocycle K H` under
  this restriction.

Finiteness of `↥(lcCocycleImage K H)` for `H = H_A` a level-`K` local group (the file
`ZDataMup/finite_lcCocycleImage.lean`) is the arithmetic input: the locally constant cocycles on
`H_A` are the homomorphisms `H_A →* Multiplicative (ZMod p)` with open kernel, which are finite by
`Work.SSGRoute.finite_openKernel_homs_decomp_kernel`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

/-- Restriction of functions `G_k → ZMod p` to a subgroup `H ≤ G_k`, as a `ZMod p`-linear map. -/
def restrictToSub {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    ((Ω ≃ₐ[k] Ω) → ZMod p) →ₗ[ZMod p] (↥H → ZMod p) where
  toFun f := f ∘ Subtype.val
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

@[simp] theorem restrictToSub_apply {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : (Ω ≃ₐ[k] Ω) → ZMod p) (x : ↥H) :
    restrictToSub (p := p) H f x = f x.1 := rfl

/-- The image of the locally constant `1`-cocycles on `H ≤ G_k` under restriction to `H`:
the locally constant cocycles on `H` regarded as functions on `H` itself. -/
noncomputable def lcCocycleImage {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) (↥H → ZMod p) :=
  (localCocycle (p := p) K H).map (restrictToSub (p := p) H)

end Work.SSGRoute.ZDataMup
