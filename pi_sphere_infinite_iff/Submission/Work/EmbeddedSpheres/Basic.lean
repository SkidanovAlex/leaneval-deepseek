import Submission.Work.ThreeConnected.Sphere
import Submission.Work.ThreeConnected.SurgeryStep
import Submission.Work.Cohomology.Degree

set_option synthInstance.maxHeartbeats 400000

/-!
# Embedded representatives of homology classes: the model

This is the first module of the chapter `Submission/Work/EmbeddedSpheres/`, the chapter responsible
for the **embedded-representative theorem**, the geometric input of Step 1 of the dimension-`8`
signature theorem (see `Submission/Work/ThreeConnected/README.md` §3.1 and `Submission/NOTES.md`
§15.8, §15.12, §15.13).

## What is being formalised, and why a new predicate is needed

The input consumed by `Submission/Work/ThreeConnected/` is
`Work.ThreeConnected.EmbeddedRepresentatives n k`:

```
∀ (M : ClosedOriented n), IsConnectedUpTo (k-1) M → ∀ x : M.hom k,
  ∃ (hk : 1 ≤ k) (F : FramedSphere n k M.X), FramedSphere.cls hk F = x
```

where `Work.Bordism.ClosedOriented n` is the *homotopy-theoretic shadow* of a closed oriented
`n`-manifold: a space together with a fundamental class, with **no** smooth (or even manifold)
structure whatsoever.  In that generality the statement is **false**, and refutably so: the
one-point space `PUnit` (and the empty space) is a legitimate element of `ClosedOriented n` with
`H_k = 0` and is vacuously `(k-1)`-connected, but it admits no embedding of the tube
`S^k × D^{n-k}` at all, hence no `FramedSphere` — while the statement demands one also for the class
`x = 0`.  See `Submission/Work/EmbeddedSpheres/Refute.lean`
(`Work.EmbeddedSpheres.not_embeddedRepresentatives`), which proves
`¬ Work.ThreeConnected.EmbeddedRepresentatives n k` for every `1 ≤ k`.

The mathematics behind `EmbeddedRepresentatives` is true, but only for *genuine* manifolds: it is
Whitney's approximation theorem in the metastable range `2k < n`.  This module therefore fixes the
model: `SmoothShadow n` below is a **closed oriented smooth `n`-manifold** (a compact connected
smooth manifold, without boundary, together with a fundamental class), and
`EmbeddedRepresentativesSmooth n k` is the *corrected* hypothesis, quantifying over `SmoothShadow`
instead of over all shadows.

## The conventions

* A `SmoothShadow n` is a type `pt` with a topological space structure, a charted space structure
  modelled on `EuclideanSpace ℝ (Fin n)`, an `IsManifold (𝓡 n) ∞` structure, `CompactSpace`,
  `T2Space`, `ConnectedSpace`, and a fundamental class `c ∈ Hₙ(pt;ℤ)` generating `Hₙ(pt;ℤ)`.
  Its *shadow* is `SmoothShadow.toClosedOriented : Work.Bordism.ClosedOriented n`, so that
  everything proved in `Work.ThreeConnected` (which only ever uses the shadow) applies verbatim.
* `IsSmoothShadow n M` says that a shadow `M : ClosedOriented n` *is* the shadow of a
  `SmoothShadow n` (same space, same fundamental class).
* A `FramedSphere n k X` is `Work.ThreeConnected.FramedSphere`: an embedding of the tube
  `S^k × D^{n-k} ↪ X`.  The embedding *is* the trivialisation of the normal bundle (the core
  `S^k × {0}` is the sphere and the product structure trivialises the normal bundle along it), and
  its class `FramedSphere.cls hk F ∈ H_k(X;ℤ)` is the image of the chosen generator
  `Work.Cohomology.sphereHomologyGen k hk` under the core.
* `classOfMap hk f` below is the class of a *continuous map* `f : S^k → X`; it is the input of the
  Hurewicz half of the representative theorem, and it agrees with `FramedSphere.cls` on the core
  (`Work.EmbeddedSpheres.classOfMap_core`).

## Main definitions of this module

* `Work.EmbeddedSpheres.SmoothShadow` — a closed oriented smooth `n`-manifold, with its shadow;
* `Work.EmbeddedSpheres.IsSmoothShadow` — a shadow that admits a smooth structure;
* `Work.EmbeddedSpheres.classOfMap` — the class of a continuous map `S^k → X`;
* `Work.EmbeddedSpheres.RepresentativeAt` — "every class of `H_k` is the class of an embedded framed
  `k`-sphere";
* `Work.EmbeddedSpheres.EmbeddedRepresentativesSmooth` — **the corrected hypothesis** (quantified
  over `SmoothShadow`);
* `Work.EmbeddedSpheres.EmbeddedRepresentativesShadow` — the same, but quantified over shadows
  carrying a smooth structure;
* `Work.EmbeddedSpheres.SmoothCanKill` — the form of the input in which the *surgery output* is
  again smooth, which is what the killing iteration of `Work.ThreeConnected` consumes without
  losing the smooth structure.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.EmbeddedSpheres

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology Work.ThreeConnected

noncomputable section

/-! ## The smooth model -/

/-- **A closed oriented smooth `n`-manifold**, in this workspace's model: a type with a smooth
structure (charted on `EuclideanSpace ℝ (Fin n)`, `C^∞`), compact, Hausdorff and connected, together
with a fundamental class `c ∈ Hₙ(pt;ℤ)` *generating* `Hₙ(pt;ℤ)` (the workspace's encoding of
"closed oriented", as in `Work.TangentClasses.ClosedOriented8Manifold` and
`Work.Thom.ClosedOrientedSmooth8`).

Everything that `Work.ThreeConnected` does with a closed oriented manifold only uses the *shadow*
`SmoothShadow.toClosedOriented`, so this structure is a refinement, never a replacement. -/
structure SmoothShadow (n : ℕ) where
  /-- the underlying type of the manifold -/
  pt : Type
  [topologicalSpace : TopologicalSpace pt]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) pt]
  [isManifold : IsManifold (𝓡 n) ∞ pt]
  [compactSpace : CompactSpace pt]
  [t2Space : T2Space pt]
  [connectedSpace : ConnectedSpace pt]
  /-- the fundamental class -/
  c : (chainC ℤ (TopCat.toSSet.obj (TopCat.of pt))).homology n
  /-- the fundamental class generates `Hₙ` -/
  c_generates : Submodule.span ℤ {c} = ⊤
  /-- **the fundamental class is non-zero**, i.e. `Hₙ` is non-trivial.  This is the *orientability*
  condition: for a closed connected `n`-manifold, `Hₙ(M;ℤ) ≅ ℤ` exactly when `M` is orientable and
  `Hₙ(M;ℤ) = 0` otherwise, so `c ≠ 0` forces `M` to be orientable (without it, a non-orientable `M`
  would be a `SmoothShadow` with `c = 0`, `span{0} = ⊤`).  It is what makes the `k = 1` framing
  statement true. -/
  c_ne_zero : c ≠ 0

attribute [instance] SmoothShadow.topologicalSpace SmoothShadow.chartedSpace
  SmoothShadow.isManifold SmoothShadow.compactSpace SmoothShadow.t2Space SmoothShadow.connectedSpace

namespace SmoothShadow

variable {n : ℕ} (M : SmoothShadow n)

/-- The singular simplicial set of the manifold. -/
abbrev sset : SSet := TopCat.toSSet.obj (TopCat.of M.pt)

/-- The integral homology `H_k(M;ℤ)` of the manifold. -/
abbrev hom (k : ℕ) : ModuleCat ℤ := (chainC ℤ M.sset).homology k

/-- **The shadow** of a closed oriented smooth `n`-manifold: the pair (space, fundamental class)
which is all that the chapters `Work.Bordism` and `Work.ThreeConnected` record. -/
def toClosedOriented : ClosedOriented n := ⟨TopCat.of M.pt, M.c⟩

@[simp] theorem toClosedOriented_X : M.toClosedOriented.X = TopCat.of M.pt := rfl

@[simp] theorem toClosedOriented_c : M.toClosedOriented.c = M.c := rfl

/-- The homology of the shadow is the homology of the manifold (definitionally). -/
theorem toClosedOriented_hom (k : ℕ) : M.toClosedOriented.hom k = M.hom k := rfl

end SmoothShadow

/-- **A shadow that is the shadow of a closed oriented smooth `n`-manifold.** -/
def IsSmoothShadow (n : ℕ) (M : ClosedOriented n) : Prop :=
  ∃ M' : SmoothShadow n, M'.toClosedOriented = M

/-- The defining property of `IsSmoothShadow`, transported to the manifold. -/
theorem IsSmoothShadow.toSmooth {n : ℕ} {M : ClosedOriented n} (h : IsSmoothShadow n M) :
    ∃ M' : SmoothShadow n, M'.toClosedOriented = M := h

/-! ## The class of a continuous map `S^k → X` -/

/-- The `TopCat` morphism underlying a continuous map. -/
def topMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom f

/-- **The class of a continuous map `f : S^k → X`**: the image of the chosen generator of
`H_k(S^k;ℤ)` under `f_*`.  For the core of a framed sphere this is `FramedSphere.cls`
(`Work.EmbeddedSpheres.classOfMap_core`). -/
def classOfMap (k : ℕ) (hk : 1 ≤ k) {X : TopCat.{0}} (f : C(Work.Surgery.Sph k, X)) :
    (chainC ℤ (TopCat.toSSet.obj X)).homology k :=
  HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Work.Surgery.Sph k)) X
    (topMap f)) k (sphereHomologyGen k hk)

/-- The core of a framed sphere, as a continuous map. -/
def framedCore {n k : ℕ} {X : TopCat.{0}} (F : FramedSphere n k X) :
    C(Work.Surgery.Sph k, X) := ⟨F.core, F.continuous_core⟩

/-- **`FramedSphere.cls` is the class of the core map** (definitionally). -/
theorem classOfMap_core {n k : ℕ} {X : TopCat.{0}} (hk : 1 ≤ k) (F : FramedSphere n k X) :
    classOfMap k hk (framedCore F) = FramedSphere.cls hk F := rfl

/-! ## The representative statements -/

/-- **Every class of `H_k(M;ℤ)` is the class of an embedded framed `k`-sphere in `M`.**  This is the
*conclusion* of the embedded-representative theorem for a single manifold `M` (in the range
`2k < n`), isolated from its hypotheses so that it can be used as a predicate. -/
def RepresentativeAt (n k : ℕ) (M : ClosedOriented n) : Prop :=
  ∀ x : M.hom k, ∃ (hk : 1 ≤ k) (F : FramedSphere n k M.X), FramedSphere.cls hk F = x

/-- **The embedded-representative theorem, corrected: for closed oriented _smooth_ `n`-manifolds.**

This is the statement that `Work.ThreeConnected.EmbeddedRepresentatives n k` was meant to be.  It is
the classical input of Step 1 of the dimension-`8` signature theorem: for `2k < n` (for `n = 8`,
`k ≤ 3`), every class of `H_k(M;ℤ)` is the class of an embedded `k`-sphere with trivialised normal
bundle.  It is *not* proved in this workspace; `NamedInputs.lean` decomposes it into its three
classical ingredients (Hurewicz representation, approximation by an embedding, and the existence of a
tube embedding), and `Assembly.lean` *proves* the decomposition. -/
def EmbeddedRepresentativesSmooth (n k : ℕ) : Prop :=
  ∀ M : SmoothShadow n, IsConnectedUpTo (k - 1) M.toClosedOriented →
    RepresentativeAt n k M.toClosedOriented

/-- **The embedded-representative theorem over shadows carrying a smooth structure**: the same
statement as `EmbeddedRepresentativesSmooth`, but phrased for a `ClosedOriented n` together with the
proof that it is a smooth shadow.  This is the form that composes with the statements of
`Work.ThreeConnected`, whose vocabulary is `ClosedOriented n`. -/
def EmbeddedRepresentativesShadow (n k : ℕ) : Prop :=
  ∀ M : ClosedOriented n, IsSmoothShadow n M → IsConnectedUpTo (k - 1) M → RepresentativeAt n k M

/-- The corrected hypothesis for smooth manifolds implies its shadow form. -/
theorem embeddedRepresentativesShadow_of_smooth {n k : ℕ}
    (h : EmbeddedRepresentativesSmooth n k) : EmbeddedRepresentativesShadow n k := by
  rintro M ⟨M', rfl⟩ hconn
  exact h M' hconn

/-- The shadow form of the hypothesis restricted to one smooth manifold. -/
theorem embeddedRepresentativesSmooth_of_shadow {n k : ℕ}
    (h : EmbeddedRepresentativesShadow n k) : EmbeddedRepresentativesSmooth n k :=
  fun M hconn => h M.toClosedOriented ⟨M, rfl⟩ hconn

/-! ## The input the killing iteration of `Work.ThreeConnected` consumes -/

/-- **The surgery output of a smooth manifold is again a smooth manifold, with the full low-range
surgery data.**  `SmoothCanKill n k` is the form of the geometric input of Step 1 in which the
*smooth structure of the surgered manifold* is carried along: for every class of `H_k` of a closed
oriented smooth `n`-manifold there is a *smooth* closed oriented `n`-manifold `N` together with a
`LowRangeSurgery n k M N` killing exactly that class.  This is what an induction over the degrees
`k = 1, 2, 3` consumes without losing the smooth structure (the field `IsSmoothShadow n N` makes the
hypothesis reusable at `N`).

Mathematically this is the conjunction of two classical theorems: the embedded-representative theorem
(`EmbeddedRepresentativesSmooth`) and the *point-set* theorem that the trace of a surgery on a smooth
manifold is smooth, whose surgered end is smooth (the workspace's `Work.Surgery` chapter, through the
named inputs `HasCollar`/`SmoothGlue`/`SmoothAttach`).  The second half is why this predicate, rather
than `EmbeddedRepresentativesSmooth` itself, is the input that the killing iteration wants: the
abstract `Work.ThreeConnected.LowRangeSurgery` records only the homology of the surgered end. -/
def SmoothCanKill (n k : ℕ) : Prop :=
  ∀ (M : ClosedOriented n), IsSmoothShadow n M → IsConnectedUpTo (k - 1) M → FiniteHomology M →
    ∀ x : M.hom k, ∃ (N : ClosedOriented n) (_ : IsSmoothShadow n N)
      (h : LowRangeSurgery n k M N), h.cls = x

end

end Work.EmbeddedSpheres
