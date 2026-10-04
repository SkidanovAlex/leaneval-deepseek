import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inverse function theorem on manifolds, `C^∞` version with an open domain

`Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible`
proves the inverse function theorem for `C^∞` maps between `C^∞` manifolds, stated with the
smoothness hypothesis `ContMDiffOn I I' ∞ f U` for an arbitrary set `U ∈ 𝓝 x`.

In applications one usually has an *open* set `U ∋ x` on which `f` is smooth (for instance a chart
source, a neighbourhood on which a chart representation is smooth, ...).  The present file records
that form of the statement: an open set is a neighbourhood of each of its points, so the lemma is
an immediate corollary.  It is the form actually consumed downstream when constructing local
diffeomorphisms from data given on an explicit open set.
-/

namespace Commons.Geometry.Manifold.LocalDiffeomorph

open scoped _root_.Manifold _root_.ContDiff
open Filter
open scoped Topology

/-- **Inverse function theorem, manifold case, `C^∞` version on an open set.**

Let `f : M → N` be a `C^∞` map between `C^∞` manifolds (modelled on `I`, `I'` over `𝕜`), let
`U` be an open set containing `x`, and suppose that `x` is an interior point of the model of
`M` and that the manifold derivative `mfderiv I I' f x` is invertible.  Then `f` is a `C^∞` local
diffeomorphism at `x`.

This is
`isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible`
applied to `U`, using that an open set is a neighbourhood of each of its points. -/
theorem isLocalDiffeomorphAt_of_contMDiffOn_of_mfderiv_isInvertible
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I' ((⊤ : ENat) : WithTop ENat) N]
    {f : M → N} {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContMDiffOn I I' ((⊤ : ENat) : WithTop ENat) f U)
    (hx : I.IsInteriorPoint x)
    (h : (mfderiv I I' f x).IsInvertible) :
    IsLocalDiffeomorphAt I I' ((⊤ : ENat) : WithTop ENat) f x :=
  isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible (hU.mem_nhds hxU) hf hx h

end Commons.Geometry.Manifold.LocalDiffeomorph
