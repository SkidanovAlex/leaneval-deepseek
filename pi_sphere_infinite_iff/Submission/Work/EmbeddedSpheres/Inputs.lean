import Submission.Work.EmbeddedSpheres.Basic

/-!
# The three classical ingredients of the embedded-representative theorem

The corrected hypothesis of the chapter is `Work.EmbeddedSpheres.EmbeddedRepresentativesSmooth n k`
(`Basic.lean`): for a closed oriented smooth `n`-manifold `M` in the range `2k < n`, every class of
`H_k(M;ℤ)` is the class of an embedded framed `k`-sphere.  Classical differential topology proves it
in three steps, and this module names each step as a `Prop` — never as an axiom.  All three are
statements about genuine smooth manifolds; the assembly *proving* the theorem from them is
`Submission/Work/EmbeddedSpheres/Assembly.lean`.

1. **Hurewicz representation** (`HurewiczRepresentation n k`).  For `M` a `(k-1)`-connected closed
   oriented smooth `n`-manifold, every class of `H_k(M;ℤ)` is the image of the chosen generator of
   `H_k(S^k;ℤ)` under a continuous map `S^k → M`.  For `k ≥ 2` this is the Hurewicz theorem applied
   to the `(k-1)`-connected `M` (`π_k(M) ≅ H_k(M)`); for `k = 1` it is `H_1 = π_1^{ab}`, i.e. the
   abelianisation of the fundamental group, together with the surjectivity of `π_1 → H_1` for a
   path-connected space.  In this workspace there are no homotopy groups at all
   (`Work.Bordism`'s model has none), so this step is *stated*, not proved; it is not a statement
   about smoothness — it needs no Sard/transversality — so it is the most tractable of the three.

2. **Approximation by an embedding** (`EmbeddingApproximation n k`).  In the metastable range
   `2k < n`, every continuous map `S^k → M` is homotopic to an embedding.  This is the step that
   needs the missing machinery: smooth approximation of continuous maps, Sard's theorem and
   transversality (a generic perturbation of an immersion is an embedding when `2k < n`).  Mathlib
   has fragments of smooth approximation and no transversality at all; see the README.

3. **The tube exists** (`TubularEmbedding n k`).  Given an *embedded* `S^k ⊂ M` (`M` a smooth closed
   `n`-manifold, `2k < n`), there is a framed sphere whose core is homotopic to the given embedding:
   i.e. the normal bundle of the embedded sphere is trivialisable and the trivialisation can be
   promoted to a tubular neighbourhood.  The triviality of the normal bundle is the content:
   `ν ⊕ TS^k ≅ TM|_S` makes `ν` stably trivial, and the stabilisation
   `π_{k-1}(SO(n-k)) → π_{k-1}(SO)` is injective in the metastable range; for `n = 8` the relevant
   groups are `π_0(SO(7)) = 0` (`k = 1`), `π_1(SO(6)) ≅ π_1(SO) = ℤ/2` (`k = 2`; the stabilisation
   is an isomorphism, and `π_1(SO(6)) → π_1(SO)` injective makes `ν` trivial), and
   `π_2(SO(5)) = 0` (`k = 3`).  The *framing* (the trivialisation of the trivial bundle) is a
   `π_{k-1}(SO(n-k))`-torsor: trivial for `k = 2` (`π_2(SO(6)) = 0`), two choices for `k = 1`
   (`π_1(SO(7)) = ℤ/2`), a `ℤ` of choices for `k = 3` (`π_3(SO(5)) = ℤ`).  The *class* of the framed
   sphere does not depend on the framing (`FramedSphere.cls` is the class of the core), so the
   choice is irrelevant for Step 1.

The `n = 8`, `k ≤ 3` case of the theorem is what Step 1 of the dimension-`8` signature theorem needs:
`2k < n` holds for `k ≤ 3`, and the three ingredients above are the ones with `(n,k) = (8,1),(8,2),
(8,3)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.EmbeddedSpheres

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology Work.ThreeConnected

noncomputable section

/-- **Ingredient 1 (Hurewicz).**  Every homology class of a `(k-1)`-connected closed oriented smooth
`n`-manifold is the image of the generator of `H_k(S^k;ℤ)` under the map induced by a continuous map
`S^k → M`.

For `k ≥ 2` this is the Hurewicz isomorphism `π_k(M) ≅ H_k(M)` for a `(k-1)`-connected `M`; for
`k = 1` it is the surjectivity of `π_1(M) → H_1(M)` for a connected `M` (Hurewicz, `H_1 ≅ π_1^{ab}`). -/
def HurewiczRepresentation (n k : ℕ) : Prop :=
  ∀ M : SmoothShadow n, IsConnectedUpTo (k - 1) M.toClosedOriented → ∀ x : M.hom k,
    ∃ (hk : 1 ≤ k) (f : C(Work.Surgery.Sph k, M.pt)), classOfMap k hk f = x

/-- **Ingredient 2 (Whitney approximation in the metastable range).**  For a closed oriented smooth
`n`-manifold with `2k < n`, every continuous map `S^k → M` is homotopic to an *embedding*.

This is the step that needs Sard/transversality and smooth approximation; it is the hardest of the
three formalisation targets and nothing like it exists in Mathlib (see the README). -/
def EmbeddingApproximation (n k : ℕ) : Prop :=
  ∀ M : SmoothShadow n, 2 * k < n → ∀ f : C(Work.Surgery.Sph k, M.pt),
    ∃ g : C(Work.Surgery.Sph k, M.pt), f.Homotopic g ∧ Topology.IsEmbedding ⇑g

/-- **Ingredient 3 (the tube exists).**  For an *embedded* `k`-sphere in a closed oriented smooth
`n`-manifold with `2k < n`, there is a framed sphere — an embedding of the whole tube
`S^k × D^{n-k}` — whose core is homotopic to the given embedding.

The content is the triviality of the normal bundle of the embedded sphere together with the
existence of a tubular neighbourhood (the framing itself is a choice, and does not affect the class
of the core). -/
def TubularEmbedding (n k : ℕ) : Prop :=
  ∀ M : SmoothShadow n, 2 * k < n → ∀ (hk : 1 ≤ k) (g : C(Work.Surgery.Sph k, M.pt)),
    Topology.IsEmbedding ⇑g →
    ∃ F : FramedSphere n k (TopCat.of M.pt), (framedCore F).Homotopic g

/-- **Ingredient 2+3 combined: every map is homotopic to the core of a framed sphere.**  This is the
precise statement of "approximation by an embedded sphere with trivialised normal bundle", and it is
*proved* from ingredients 2 and 3 in `Assembly.lean`. -/
def MetastableApproximation (n k : ℕ) : Prop :=
  ∀ M : SmoothShadow n, 2 * k < n → ∀ (hk : 1 ≤ k) (f : C(Work.Surgery.Sph k, M.pt)),
    ∃ F : FramedSphere n k (TopCat.of M.pt), (framedCore F).Homotopic f

/-- **The smooth surgery step.**  For a closed oriented smooth `n`-manifold and an embedded framed
`k`-sphere in it, there is a closed oriented **smooth** `n`-manifold `N` together with the
`LowRangeSurgery` data of the surgery on that sphere (killing exactly the class of the sphere).

This is the *point-set* half of the geometric input of Step 1: it is the statement that the surgered
manifold of a smooth manifold is again smooth, i.e. that the trace of a smooth surgery is smooth
(the workspace's `Work.Surgery` chapter, through its named inputs `HasCollar`/`SmoothGlue`/
`SmoothAttach`), together with the homological effect of the surgery
(`Work.ThreeConnected.Excision.traceEffect` computes that effect for the surgered end of the
concrete trace; the missing bookkeeping is that this surgered end is the smooth surgered manifold).
Nothing about `EmbeddedRepresentatives` is used: the framed sphere is given. -/
def SmoothSurgeryExists (n k : ℕ) : Prop :=
  ∀ (M : ClosedOriented n), IsSmoothShadow n M → IsConnectedUpTo (k - 1) M → FiniteHomology M →
    ∀ (hk : 1 ≤ k) (F : FramedSphere n k M.X),
      ∃ (N : ClosedOriented n) (_ : IsSmoothShadow n N) (h : LowRangeSurgery n k M N),
        h.cls = FramedSphere.cls hk F

end

end Work.EmbeddedSpheres
