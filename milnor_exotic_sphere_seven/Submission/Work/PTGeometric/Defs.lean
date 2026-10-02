import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.Tubular.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC, the geometric half of Pontryagin–Thom: the vocabulary

This is the opening file of the subproject **PTGEOMETRIC**
(`Submission/Work/PTGeometric/`, namespace `Work.PTGeometric`): the part of the Pontryagin–Thom
chapter that turns a **null-homotopy of the genuine collapse map** `S^{8+k} → T = Th(γ_k)` into a
null-bordism of the pieces.

## Why a new notion of target is needed

The Transversality chapter (`Work.ThomBordism.Transversality`) models the manifold part of the Thom
space by a `CoreTarget n k`: a smooth `n`-manifold `E` with **one global** smooth map
`Φ : E → ℝ^k` which is a submersion along its zero set (`CoreTarget.core`).  The transverse preimage
of such a target has a *trivial* normal bundle: if `W = (Φ ∘ F) ⁻¹' {0} ⊆ M` then `d(Φ ∘ F)`
identifies the normal bundle of `W` in `M` with the trivial bundle `ℝ^k` (kernel = `TW`).

For the zero section of the **universal bundle** `γ_k` this global `Φ` does not exist: `dΦ` along
the core would trivialise the normal bundle of the core, which *is* `γ_k`, and `γ_k` is non-trivial
as soon as its first Pontryagin class does not vanish.  So the genuine Grassmannian geometry cannot
be expressed with a `CoreTarget`, exactly as the project lead's note
(`Submission/Work/ThomBordism/familyAssembly.lean`) says.

## What replaces it

`Work.PTGeometric.LocalCoreTarget n k`: a smooth `n`-manifold `E` with a subset `core` which is
covered by open sets `locU i`, each carrying a *local* defining function `Phi i : E → ℝ^k` which
vanishes exactly on `core ∩ locU i` and is a submersion along it.  Nothing is required outside
`locU i`.  Transversality of `F : M → E` to the core at `x` is then
`∃ i, F x ∈ locU i ∧ IsSubmersionAt (Phi i ∘ F) x` — the honest chart-by-chart condition, which is
satisfiable for the non-trivial bundle (each chart of the Grassmannian trivialises `γ_k` and
provides its `Phi i`).

Every `CoreTarget` is a `LocalCoreTarget` with a single index (`LocalCoreTarget.ofCoreTarget`), so
the chapter's theorems apply here as well; the converse is false (the universal bundle).

## Main definitions

* `Work.PTGeometric.LocalCoreTarget`, `.core`, `.Phi`, `.locU`
* `Work.PTGeometric.IsCoreTransverseAt`, `.IsCoreTransverse`, `.IsCoreTransverseOnBoundary`
* `Work.PTGeometric.CorePreimage`, `.EndPreimage`
* `Work.PTGeometric.LocalPreimageTheorem` (the geometric theorem, as a named `Prop`)
* `Work.PTGeometric.GenuinePullbackOrientationData` (the orientation datum of the situation)
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

/-- **The manifold part of a Thom-like target with a codimension-`k` core, described locally.**

`E` is a smooth `n`-manifold; in the application it is the total space of the universal oriented
`k`-plane bundle `γ_k` (so `n = k·m + k` for the Grassmannian `G̃r_k(ℝ^{k+m})`; for the
Pontryagin–Thom construction of an `8`-manifold `m = 8`, i.e. `n = 9k`).  `core` is the zero section,
a closed submanifold of codimension `k`, and the local defining functions `Phi i` — defined on the
open sets `locU i`, which cover the core — are the local trivialisations of the normal bundle of the
core (equivalently: the charts of the Grassmannian in which `γ_k` is trivialised).

Unlike `Work.ThomBordism.Transversality.CoreTarget` there is **no** global `Φ : E → ℝ^k` that
vanishes exactly on the core and is a submersion along it: such a `Φ` would trivialise the normal
bundle of the core, which is `γ_k` itself (`LocalPreimageTheorem` below is the theorem that needs
the local version). -/
structure LocalCoreTarget (n k : ℕ) where
  /-- the manifold part of the target -/
  E : Type
  [topologicalSpace : TopologicalSpace E]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) E]
  [isManifold : IsManifold (𝓡 n) ∞ E]
  /-- the core (the zero section) -/
  core : Set E
  /-- the core is closed (the zero section of a vector bundle over a compact base is closed) -/
  isClosed_core : IsClosed core
  /-- the index set of the local trivialisations -/
  locIx : Type
  /-- the open sets on which the local defining functions are defined -/
  locU : locIx → Set E
  /-- they are open -/
  isOpen_locU : ∀ i, IsOpen (locU i)
  /-- they cover the core -/
  core_subset : core ⊆ ⋃ i, locU i
  /-- the local defining function (the trivialisation of the normal bundle of the core over `locU i`) -/
  Phi : locIx → E → EuclideanSpace ℝ (Fin k)
  /-- smoothness of the local defining functions -/
  contMDiff_Phi : ∀ i, ContMDiff (𝓡 n) (𝓡 k) ∞ (Phi i)
  /-- over `locU i`, the zero set of `Phi i` is exactly the core -/
  mem_core_iff : ∀ i, ∀ x ∈ locU i, (Phi i x = 0 ↔ x ∈ core)
  /-- `Phi i` is a submersion along the core -/
  isSubmersion_Phi : ∀ i, ∀ x ∈ locU i, Phi i x = 0 →
    IsSubmersionAt (𝓡 n) (𝓡 k) ∞ (Phi i) x

attribute [instance] LocalCoreTarget.topologicalSpace LocalCoreTarget.chartedSpace
  LocalCoreTarget.isManifold

namespace LocalCoreTarget

variable {n k : ℕ}

/-- The local defining function at an index, read on the core. -/
theorem Phi_eq_zero_of_mem_core (X : LocalCoreTarget n k) {i : X.locIx} {x : X.E}
    (hx : x ∈ X.core) (h : x ∈ X.locU i) : X.Phi i x = 0 :=
  (X.mem_core_iff i x h).mpr hx

/-- The local defining functions are submersions at the points of the core. -/
theorem isSubmersionAt_Phi_of_mem_core (X : LocalCoreTarget n k) {i : X.locIx} {x : X.E}
    (hx : x ∈ X.core) (h : x ∈ X.locU i) :
    IsSubmersionAt (𝓡 n) (𝓡 k) ∞ (X.Phi i) x :=
  X.isSubmersion_Phi i x h (X.Phi_eq_zero_of_mem_core hx h)

/-- **Every `CoreTarget` is a `LocalCoreTarget`** (one index, the global `Φ` defined on all of `E`).
So the local notion specialises to the chapter's, and the theorems below apply to the chapter's
targets as well. -/
def ofCoreTarget (X : Work.ThomBordism.Transversality.CoreTarget n k) : LocalCoreTarget n k where
  E := X.E
  topologicalSpace := X.topologicalSpace
  chartedSpace := X.chartedSpace
  isManifold := X.isManifold
  core := X.core
  isClosed_core := by
    have h : X.core = X.Φ ⁻¹' {0} := Work.ThomBordism.Transversality.CoreTarget.core_eq_preimage X
    rw [h]
    exact isClosed_singleton.preimage X.contMDiff_Φ.continuous
  locIx := PUnit
  locU := fun _ => univ
  isOpen_locU := fun _ => isOpen_univ
  core_subset := fun x _ => Set.mem_iUnion.mpr ⟨PUnit.unit, mem_univ x⟩
  Phi := fun _ => X.Φ
  contMDiff_Phi := fun _ => X.contMDiff_Φ
  mem_core_iff := by
    intro _ x _
    exact Work.ThomBordism.Transversality.CoreTarget.mem_core
  isSubmersion_Phi := by
    intro _ x _ hx
    exact X.isSubmersionAt_Φ x (Work.ThomBordism.Transversality.CoreTarget.mem_core.mp hx)

@[simp] theorem ofCoreTarget_E (X : Work.ThomBordism.Transversality.CoreTarget n k) :
    (ofCoreTarget X).E = X.E := rfl

@[simp] theorem ofCoreTarget_core (X : Work.ThomBordism.Transversality.CoreTarget n k) :
    (ofCoreTarget X).core = X.core := rfl

@[simp] theorem ofCoreTarget_Phi (X : Work.ThomBordism.Transversality.CoreTarget n k)
    (i : (ofCoreTarget X).locIx) : (ofCoreTarget X).Phi i = X.Φ := rfl

end LocalCoreTarget

variable {n k : ℕ}

/-- **`F` is transverse to the core of `X` at `x`.**

Either `F x` is off the core, or *some* local trivialisation `locU i` contains `F x` and the
composite `Phi i ∘ F` is a submersion at `x`.  With `Phi i` a submersion along the core, this is the
classical condition `im (dF x) + T_{F x} core = T_{F x} E`, i.e. transversality to the zero section
of the (possibly non-trivial) bundle.

This is the chart-by-chart form of `Work.ThomBordism.Transversality.IsTransverseAt`, and for
`LocalCoreTarget.ofCoreTarget X` of a chapter `CoreTarget` the two agree (`ofCoreTarget_...`). -/
def IsCoreTransverseAt (X : LocalCoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (F : M → X.E) (x : M) : Prop :=
  F x ∈ X.core → ∃ i, F x ∈ X.locU i ∧ IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Phi i (F y)) x

/-- `F` is transverse to the core everywhere. -/
def IsCoreTransverse (X : LocalCoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (F : M → X.E) : Prop :=
  ∀ x, IsCoreTransverseAt X I F x

/-- `F` is transverse to the core on the set `A ⊆ M` (pointwise). -/
def IsCoreTransverseOn (X : LocalCoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (F : M → X.E) (A : Set M) : Prop :=
  ∀ x ∈ A, IsCoreTransverseAt X I F x

/-- **Transversality to the core on a neighbourhood of the boundary** (the hypothesis from which the
local transversality/perturbation theorem `LocalTransversalApproximation` starts, the analogue of
`Work.ThomBordism.Transversality.IsTransverseNearBoundary`). -/
def IsCoreTransverseNearBoundary (X : LocalCoreTarget n k) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M] (F : M → X.E) : Prop :=
  ∃ U : Set M, (𝓡∂ ((8 + k) + 1)).boundary M ⊆ U ∧ IsOpen U ∧
    IsCoreTransverseOn X (𝓡∂ ((8 + k) + 1)) F U

/-- `F` is transverse to the core at every boundary point of the source, through **one** local
trivialisation.

This is the hypothesis the preimage theorem needs beyond transversality of `F` (the analogue of
`Work.ThomBordism.Transversality.BoundaryTransverse`, and for the same reason: it is *not* implied by
transversality of `F` near the boundary, see the Transversality chapter's `README.md` §0.1).

The two conjuncts are asked for the *same* index `i`, which is what the geometric situation supplies:
a trivialisation of `γ_k` at the point, in which both the map and its boundary restriction read as
the same submersion.  (The second conjunct in fact *implies* the first at a boundary point of a
manifold with boundary: `T_x M = T_x ∂M + ℝ≥0·ν`, so a surjective derivative on `T_x ∂M` is
surjective.) -/
def IsCoreTransverseOnBoundary (X : LocalCoreTarget n k) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E) : Prop :=
  ∀ (x : M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), F x ∈ X.core →
    ∃ i, F x ∈ X.locU i ∧
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => X.Phi i (F y)) x ∧
      IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => X.Phi i (F (y : M))) ⟨x, hx⟩

def CorePreimage (X : LocalCoreTarget n k) {M : Type*} (F : M → X.E) : Set M := F ⁻¹' X.core

/-- **The end preimage of the core**: the boundary points of `M` whose image lies on the core (the
boundary of the transverse preimage, in the Pontryagin–Thom construction the disjoint union of the
pieces of the family). -/
def EndPreimage (X : LocalCoreTarget n k) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E) : Set M :=
  (𝓡∂ ((8 + k) + 1)).boundary M ∩ CorePreimage X F

theorem mem_CorePreimage {X : LocalCoreTarget n k} {M : Type*} {F : M → X.E} {x : M} :
    x ∈ CorePreimage X F ↔ F x ∈ X.core := Iff.rfl

theorem mem_EndPreimage {X : LocalCoreTarget n k} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] {F : M → X.E} {x : M} :
    x ∈ EndPreimage X F ↔ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M ∧ F x ∈ X.core := Iff.rfl

/-- **The local preimage theorem** (the geometric theorem of the subproject, as a named `Prop`).

For a compact `T2` smooth `(9+k)`-manifold `M` with boundary (modelled on the half-space), a
`LocalCoreTarget X` and a smooth `F : M → X.E` which is transverse to the core (chart by chart,
`IsCoreTransverse`) and whose restriction to `∂M` is transverse to the core as well
(`IsCoreTransverseOnBoundary`), the transverse preimage `F ⁻¹' X.core` is a compact `T2` smooth
`9`-manifold with boundary, and its boundary is the end preimage of the core.

This is `Work.ThomBordism.Transversality.Preimage.exists_preimage_structure` (which is *proved*, but
for a `CoreTarget`, i.e. for a target with a **global** defining function) generalised to the local
form: the tangent space of the preimage is `ker d(Phi i ∘ F)` on `locU i`, and the charts built from
the submersion normal forms at the points of the preimage glue because locally the preimage is the
zero set of a submersion in either trivialisation. -/
def LocalPreimageTheorem : Prop :=
  ∀ (n k : ℕ) (X : LocalCoreTarget n k) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M] [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
    [CompactSpace M] [T2Space M] (F : M → X.E),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ F →
    IsCoreTransverse X (𝓡∂ ((8 + k) + 1)) F →
    IsCoreTransverseOnBoundary X F →
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (EuclideanHalfSpace 9) W)
      (_ : IsManifold (𝓡∂ 9) ∞ W) (_ : CompactSpace W) (_ : T2Space W)
      (e : W ≃ₜ ↥(CorePreimage X F)),
      (∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (e w : M) ∈ EndPreimage X F)

/-- **The orientation datum of the situation** (the analogue of
`Work.ThomBordism.Transversality.PullbackOrientationData` for a `LocalCoreTarget`).

The transverse preimage `W = F ⁻¹' X.core` carries a relative fundamental class
`[W, ∂W] ∈ H₉(W, ∂W; ℤ)` (oriented by the orientation of the ambient `M` together with the
orientation of the normal bundle of the core — i.e. the **Thom class of `γ_k`**, pulled back along
the trivialisations `Phi i`), which is a local generator at every interior point of `W`, and the
identification of `∂W` with the pieces of the family is orientation-compatible, i.e. carries the
boundary class to the sum of the pieces' fundamental classes — the exact shape of the consumer's
field `Work.ThomBordism.NullBordismFamily.hw`.

As in the Transversality chapter (§0.7 of its `README.md`) this is a datum of the *situation* and not
a universal hypothesis: the existence of `w` with the local-generator property is ORIENT's
`Work.Orient.RelativeFundamentalClassExists 8` (proved from the collar theorem), while the *signed*
boundary identity is the orientation compatibility of the geometric identification of `∂W` with the
pieces, which is not provable from ORIENT alone.  The datum is quantified over *all* manifold models
`W` of the preimage (`hW`), exactly as in the chapter. -/
def GenuinePullbackOrientationData (X : LocalCoreTarget n k) (ι : Type) [Fintype ι]
    (Fam : ι → Work.ThomBordism.Man8) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M] [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E)
    (e : ↥(EndPreimage X F) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W]
    (hW : W ≃ₜ ↥(CorePreimage X F))
    (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (hW w : M) ∈ EndPreimage X F),
    ∃ (bdryPreimage : ((𝓡∂ 9).boundary W) ≃ₜ ↥(EndPreimage X F))
      (w : (Work.Cohomology.relChains (TopCat.of W) ((𝓡∂ 9).boundary W)).homology 9),
      (∀ (x : W) (hx : x ∉ (𝓡∂ 9).boundary W),
        Submodule.span ℤ {(HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W) ((𝓡∂ 9).boundary W) x hx) 9 w)} = ⊤) ∧
      (Work.Cohomology.hPairδ (TopCat.of W) ((𝓡∂ 9).boundary W) 8 w
        = ∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary W))
              (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c)

end

end Work.PTGeometric
