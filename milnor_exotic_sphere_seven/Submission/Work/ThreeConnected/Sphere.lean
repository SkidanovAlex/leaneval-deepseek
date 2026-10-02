import Submission.Work.ThreeConnected.SurgeryStep
import Submission.Work.Surgery.Handle
import Submission.Work.Cohomology.Degree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Embedded spheres with trivialised normal bundle

This module makes precise the **geometric input of item 2** of the brief: the existence, in the range
`2k < n`, of embedded representatives of a class of `H_k` with trivialised normal bundle.

## The convention: the embedding of the tube *is* the trivialisation

An embedding `S^k × D^{n-k} ↪ M` whose image is a closed tubular neighbourhood of the sphere
`S^k ↪ M` encodes at once

* the embedded sphere (its core `S^k × {0}`), and
* a trivialisation of its normal bundle (the identification of the tube with the product
  `S^k × D^{n-k}`).

This is the same convention as in `Submission/Work/Surgery/Handle.lean`, where an attaching map *is*
the framing data.  `Work.ThreeConnected.FramedSphere` is that data.

## The class of a framed sphere

`Work.ThreeConnected.FramedSphere.cls` is the class in `H_k(M;ℤ)` of the core sphere: the image of
the chosen generator `Work.Cohomology.sphereHomologyGen k` of `H_k(S^k;ℤ)` under the map induced by
the core `S^k → M`.

## The two geometric inputs of Step 1, separated

* `Work.ThreeConnected.EmbeddedRepresentatives n k` — **item 2**: every class of `H_k(M;ℤ)` for a
  `(k-1)`-connected closed oriented `n`-manifold `M` is the class of an embedded framed `k`-sphere
  (in the range `2k < n`, where `k ≤ 3` for `n = 8`);
* `Work.ThreeConnected.TraceEffect n k` — **item 1**: for every embedded framed `k`-sphere in a
  closed oriented `n`-manifold there is a `LowRangeSurgery` killing exactly its class (so that the
  trace exists, is a bordism, and has the stated effect on homology).

Their conjunction is the input `Work.ThreeConnected.CanKill n k` used by the killing iteration:

* `Work.ThreeConnected.canKill_of_embeddedRepresentatives_and_trace`.

## Note on the model

The model `Work.Bordism.ClosedOriented n` is a space with a fundamental class, without a smooth
structure.  The two predicates below are therefore stated for the *homotopy-theoretic shadow* of the
geometric statements: they quantify over `M : ClosedOriented n` and its integral homology.  For a
genuine closed oriented smooth manifold one takes `X` the underlying space, `c = [M]`, and reads the
predicates as statements about it.

## A warning about a reduction in the literature

Both predicates are *theorems* for genuine smooth manifolds in the range `2k < n`, but neither is
proved in this workspace; see `README.md` for the precise list of what is missing.  In particular the
result that a homology class is represented by an *embedded* sphere (rather than by a continuous map)
is Whitney's approximation theorem in the range `2k < n`, and the triviality of the normal bundle is
the stable triviality of `ν ⊕ TM|_S ≅ εⁿ` together with the injectivity of
`π_{k-1}(SO(n-k)) → π_{k-1}(SO)` (for `n = 8`: `k = 1` rank `7`, `k = 2` rank `6`,
`k = 3` rank `5`, all in the stable range).
-/

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {n k : ℕ} {X : TopCat.{0}}

/-- The radius of the `D^{n-k}`-coordinate (the *belt* direction) of a point of the disc
`Disk (n-k-1) = D^{n-k}`. -/
def beltRad (l : ℕ) (y : Work.Surgery.Disk l) : ℝ :=
  ‖(y : EuclideanSpace ℝ (Fin (l + 1)))‖

/-- **An embedded framed `k`-sphere in a space `X`**: an embedding of the closed tube
`S^k × D^{n-k}`, i.e. of the disc bundle of the (trivialised) normal bundle of a `k`-sphere in an
`n`-manifold.

The embedding *is* the trivialisation of the normal bundle: the core `S^k × {0}` is the sphere and
the product structure of the tube trivialises the normal bundle along it. -/
structure FramedSphere (n k : ℕ) (X : TopCat.{0}) where
  /-- the embedding of the tube -/
  φ : Work.Surgery.Sph k × Work.Surgery.Disk (n - k - 1) → X
  /-- it is an embedding -/
  isEmbedding : Topology.IsEmbedding φ
  /-- the ambient space is Hausdorff (true for a manifold); used to know that the image of a
  compact piece of the tube is closed -/
  [t2 : T2Space X]
  /-- **the tube is a genuine tubular neighbourhood**: the image of the *open* tube
  `{‖y‖ < 1} = S^k × D̊^{n-k}` is open in `X`.  Equivalently, the interior of the closed tube is the
  open disc bundle — which is what makes the embedding a trivialisation of the *normal bundle*
  rather than merely an embedding of an `n`-disc.  For a genuine smooth manifold this is invariance
  of domain; here it is recorded, since the belt-side cover of the trace meets the gluing locus along
  this open set. -/
  isOpen_tube : IsOpen (φ '' {u : Work.Surgery.Sph k × Work.Surgery.Disk (n - k - 1) |
    beltRad (n - k - 1) u.2 < 1})

/-- The **core sphere** of a framed sphere: `p ↦ (p, 0)`. -/
noncomputable def FramedSphere.core (F : FramedSphere n k X) : Work.Surgery.Sph k → X :=
  fun p => F.φ (p, 0)

theorem FramedSphere.continuous_core (F : FramedSphere n k X) : Continuous F.core :=
  F.isEmbedding.continuous.comp (by continuity)

/-- The core sphere as a map of topological spaces. -/
noncomputable def FramedSphere.coreHom (F : FramedSphere n k X) :
    TopCat.of (Work.Surgery.Sph k) ⟶ X :=
  TopCat.ofHom ⟨F.core, F.continuous_core⟩

/-- **The class of a framed sphere** in `H_k(X;ℤ)`: the image of the chosen generator of
`H_k(S^k;ℤ)` under the map induced by the core. -/
noncomputable def FramedSphere.cls (hk : 1 ≤ k) (F : FramedSphere n k X) :
    (chainC ℤ (TopCat.toSSet.obj X)).homology k :=
  HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Work.Surgery.Sph k)) X F.coreHom) k
    (sphereHomologyGen k hk)

variable (n k : ℕ)

/-- **Item 2 of the brief, as a proposition**: every homology class of a `(k-1)`-connected closed
oriented `n`-manifold is the class of an embedded framed `k`-sphere.

Classically this is Whitney's embedding/approximation theorem in the range `2k < n`: a class of
`H_k(M;ℤ)` is realised by a continuous map `S^k → M` (Hurewicz, using `(k-1)`-connectedness), which
can be approximated by an embedding when `2k < n`; the normal bundle of the embedded sphere is then
trivial in the relevant range (`n = 8`: `π_0(SO(7)) = 0`, `π_1(SO(6)) ≅ π_1(SO)`, `π_2(SO(5)) = 0`),
and a *choice* of trivialisation (a framing: `π_1(SO(7)) = ℤ/2` for `k = 1`, `π_2(SO(6)) = 0` for
`k = 2`, `π_3(SO(5)) = ℤ` for `k = 3`) gives the tube embedding of `FramedSphere`.  The extra fields
`T2Space X` and `isOpen_tube` of `FramedSphere` are part of that geometric input: they record that
the tube is a genuine closed tubular neighbourhood of the sphere (invariance of domain for a smooth
manifold), which is what the belt-side cover of `Excision/BeltCover.lean` uses. -/
def EmbeddedRepresentatives : Prop :=
  ∀ (M : ClosedOriented n), IsConnectedUpTo (k - 1) M → ∀ x : M.hom k,
    ∃ (hk : 1 ≤ k) (F : FramedSphere n k M.X), FramedSphere.cls hk F = x

/-- **Item 1 of the brief, as a proposition**: the surgery along an embedded framed `k`-sphere has a
trace which is a bordism to the surgered manifold, kills exactly the class of the sphere, and has the
effect on homology below the middle dimension described by `LowRangeSurgery`.

This is the *homological* content of the surgery construction (the existence of the surgered manifold
`M' = (M ∖ S^k × D̊^{n-k}) ∪ (D^{k+1} × S^{n-k-1})`, of its trace, and the long exact sequence of the
pair `(W, M)`); the point-set construction of `M'` is in
`Submission/Work/ThreeConnected/SurgerySpace.lean`.

**`TraceEffect n k` is now a theorem** for `1 ≤ k` and `k + 1 < n - k`: see
`Work.ThreeConnected.Excision.traceEffect` in
`Submission/Work/ThreeConnected/Excision/TraceEffectAssembly.lean`, whose proof computes the whole
homology of the concrete trace (attaching side, belt side, the class identification and the
finite-generation bookkeeping; see `Submission/Work/ThreeConnected/README.md` §1.9 and §3.2).  So the
*only* input of Step 1 of the surgical route is `EmbeddedRepresentatives` below. -/
def TraceEffect : Prop :=
  ∀ (M : ClosedOriented n) (hk : 1 ≤ k) (F : FramedSphere n k M.X),
    ∃ (N : ClosedOriented n) (h : LowRangeSurgery n k M N),
      h.cls = FramedSphere.cls hk F

/-- **The two geometric inputs together are `CanKill`.**  This is the precise sense in which Step 1
is reduced to items 1 and 2 of the brief: `EmbeddedRepresentatives` gives a framed sphere
representing the prescribed class, and `TraceEffect` performs the surgery on it. -/
theorem canKill_of_embeddedRepresentatives_and_trace
    (hrep : EmbeddedRepresentatives n k) (htr : TraceEffect n k) : CanKill n k := by
  intro M hconn hfin x
  obtain ⟨hk, F, hF⟩ := hrep M hconn x
  obtain ⟨N, h, hcls⟩ := htr M hk F
  exact ⟨N, h, by rw [hcls, hF]⟩

end

end Work.ThreeConnected
