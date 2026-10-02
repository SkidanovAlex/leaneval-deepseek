import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.Transversality.Homotopy
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transverse preimage of the core is a null-bordism

This file contains item 2 (second half) of the **Transversality** chapter: the *preimage theorem*
plus *orientation theory* for a map transverse to the zero section, in the form in which the rest of
area THOM consumes it.

## The two missing theorems, isolated

* **The preimage theorem** (geometric).  If `F : M → E` is smooth and transverse to the core
  `X.core ⊆ E` (a submanifold of codimension `k`), then `F ⁻¹' X.core` is a smooth submanifold of
  `M` of dimension `dim M - k`, with boundary `∂M ∩ F ⁻¹' X.core`.  In the model actually used by the
  chapter (`M` a compact smooth `(9+k)`-manifold with boundary, modelled on the half-space) this is
  **proved** in `Submission/Work/ThomBordism/Transversality/Preimage/exists_preimage_structure.lean`
  (`Preimage.exists_preimage_structure`), *provided* the boundary restriction of `F` is transverse to
  the core as well (`BoundaryTransverse` below; the naive statement without that hypothesis is
  **false**, see §0.1 of the `README.md`).
* **Orientation theory.**  The orientation of the ambient manifold `M` together with the orientation
  of the normal bundle of the core (the **Thom class** of `γ_k`) orients `W = F ⁻¹' X.core`, and
  gives a relative fundamental class `[W, ∂W] ∈ H₉ (W, ∂W; ℤ)` which is a local generator at every
  interior point and whose boundary is the sum of the fundamental classes of the pieces of `∂W`.
  Mathlib has no fundamental-class theory; the ORIENT area
  (`Submission/Work/Orient/`) supplies the existence theorem
  `Work.Orient.RelativeFundamentalClassExists 8`, and the compatibility of the boundary
  identification with the *signed* sum of the pieces is isolated here as `PullbackOrientationData`
  (see below): a datum of the *situation*, **not** a universal hypothesis — universally quantified
  over all geometric data the statement is false (see `README.md` §0.7).

`TransversalPullback` records the *output* of those two theorems for a map which is transverse to the
core: a compact oriented `9`-manifold `W` with `∂W ≃ₜ ∂M ∩ F ⁻¹' X.core` (the *end preimage* of the
core), and its relative fundamental class, with the boundary identified with the pieces of the family
through the given homeomorphism `e` of the end preimage with `Σ i, (Fam i).pt`.

`TransversalPreimageTheorem` is the theorem that this data exists as soon as the situation carries
its orientation datum (`PullbackOrientationData`); it is *proved* in `Preimage/orientation.lean`
(`transversalPreimageTheorem`).

## Main definitions

* `Work.ThomBordism.Transversality.endPreimage`
* `Work.ThomBordism.Transversality.BoundaryTransverse`
* `Work.ThomBordism.Transversality.TransversalPullback`
* `Work.ThomBordism.Transversality.PullbackOrientationData` (the per-situation orientation datum)
* `Work.ThomBordism.Transversality.TransversalPreimageTheorem`

## Main results

* `TransversalPullback.toNullBordismFamily` — the assembly into `NullBordismFamily`;
* `exists_nullBordismFamily_of_inputs` — the two inputs of the chapter (the homotopy theorem and the
  preimage theorem) applied to a transverse-near-the-boundary map with the ends identified with the
  pieces produce a null-bordism of the family;
* `boundaryTransverse_iff` — `BoundaryTransverse` is the pointwise boundary-submersivity condition
  used by the geometric input `Preimage.exists_preimage_structure`.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.Transversality

noncomputable section

variable {n k : ℕ}

/-- The **end preimage of the core**: the boundary points of `M` whose image under `F` lies on the
core.  In the application `M` is the disk with `N` holes, `∂M = ⊔_{N} S^{8+k}`, and this is the
disjoint union of `N` copies of the manifold `V` itself (the collapse map is transverse to the zero
section near the boundary, with preimage `V`). -/
def endPreimage {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {X : CoreTarget n k} (F : M → X.E) : Set M :=
  I.boundary M ∩ {x | X.Φ (F x) = 0}

theorem mem_endPreimage {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] {X : CoreTarget n k} {F : M → X.E} {x : M} :
    x ∈ endPreimage I F ↔ x ∈ I.boundary M ∧ X.Φ (F x) = 0 := Iff.rfl

/-- The end preimage depends only on the values of `F` on the boundary. -/
theorem endPreimage_congr {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] {X : CoreTarget n k} {F F' : M → X.E}
    (h : ∀ x ∈ I.boundary M, F x = F' x) : endPreimage I F = endPreimage I F' := by
  ext x
  rw [mem_endPreimage, mem_endPreimage]
  exact and_congr_right fun hx => by rw [h x hx]

/-! ## Boundary transversality

The preimage theorem needs `F` to be transverse to the core, **and** its restriction to `∂M` to be
transverse to the core as well (as a map of the boundaryless manifold `∂M`).  The latter is *not* a
consequence of the former: `M = {x₁ ≥ 0} ⊆ ℝ^{9+k}`, `X.Φ = pr₁`, `F = id` is transverse to the core
near the boundary (`∂M = {x₁ = 0}` meets the core only where the other `k-1` coordinates vanish,
where `pr₁` is a submersion), yet `(Φ ∘ F)|∂M = 0` is not a submersion anywhere on the end preimage,
and `F ⁻¹' core = ∂M` is a boundaryless `9`-manifold inside `∂M`, not a manifold whose boundary is
the end preimage.  See §0.1 of the `README.md` for this and for a second counterexample showing that
the weaker hypothesis "the level set meets the interior near the boundary" does not suffice either.

The correct hypothesis is therefore: **the restriction of `F` to `∂M` is transverse to the core**
(the boundary `∂M` carries the boundaryless manifold structure of `M`, supplied by the Surgery area
`Submission/Work/Surgery/BoundaryInstances.lean`). -/
def BoundaryTransverse (k : ℕ) (X : CoreTarget ((8 + k) + 1) k) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E) : Prop :=
  IsTransverse X (𝓡 (8 + k)) (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => F (y : M))

/-- **`BoundaryTransverse` is the pointwise boundary-submersivity condition** used by the geometric
input `Preimage.exists_preimage_structure`: for every boundary point `x` of the end preimage,
`(Φ ∘ F)|∂M` is a submersion at `x`. -/
theorem boundaryTransverse_iff {k : ℕ} {X : CoreTarget ((8 + k) + 1) k} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] {F : M → X.E} :
    BoundaryTransverse k X F ↔ ∀ (x : M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M),
      X.Φ (F x) = 0 → IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => X.Φ (F (y : M))) ⟨x, hx⟩ := by
  simp only [BoundaryTransverse, IsTransverse, IsTransverseOn, IsTransverseAt, mem_univ,
    true_implies]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h y
    exact h y.1 y.2

/-- **`BoundaryTransverse` only depends on the restriction of `F` to `∂M`.** -/
theorem boundaryTransverse_congr {k : ℕ} {X : CoreTarget ((8 + k) + 1) k} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] {F F' : M → X.E}
    (h : ∀ y : ↥((𝓡∂ ((8 + k) + 1)).boundary M), F (y : M) = F' (y : M)) :
    BoundaryTransverse k X F ↔ BoundaryTransverse k X F' := by
  unfold BoundaryTransverse
  rw [show (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => F (y : M))
      = (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => F' (y : M)) from funext h]

/-- A map whose boundary restriction avoids the core is boundary-transverse (the case in which the
end preimage is empty). -/
theorem boundaryTransverse_of_avoid {k : ℕ} {X : CoreTarget ((8 + k) + 1) k} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] {F : M → X.E}
    (h : ∀ y : ↥((𝓡∂ ((8 + k) + 1)).boundary M), X.Φ (F (y : M)) ≠ 0) :
    BoundaryTransverse k X F :=
  isTransverseOn_of_avoid (𝓡 (8 + k)) fun y _ => h y

/-! ## The transverse preimage of the core, as an oriented bordism -/

/-- **The transverse preimage of the core, as an oriented bordism.**

This is the *output* of the preimage theorem and of orientation theory, for a smooth map
`F : M → E` which is transverse to the core, with the end preimage of the core identified with the
pieces `Fam i` through a homeomorphism `e`:

* `W` — the transverse preimage `F ⁻¹' X.core`, a compact `T2` smooth `9`-manifold with boundary;
* `bdryPreimage` — the preimage theorem: `∂W` is the end preimage of the core;
* `w` — the relative fundamental class `[W, ∂W]`, obtained from the orientation of `M` and the Thom
  class of the universal bundle;
* `hw` — the boundary of the fundamental class is the sum of the pieces' fundamental classes;
* `w_fund` — the relative fundamental class is a local generator at every interior point of `W`

  (so that `W` is a bordism in the sense of `Work.ThomBordism.NullBordismFamily`). -/
structure TransversalPullback (k : ℕ) (X : CoreTarget ((8 + k) + 1) k) (ι : Type) [Fintype ι]
    (Fam : ι → Man8) {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (F : M → X.E) (e : ↥(endPreimage I F) ≃ₜ (Σ i : ι, (Fam i).pt)) where
  /-- the transverse preimage -/
  W : Type
  [topologicalSpace : TopologicalSpace W]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace 9) W]
  [isManifold : IsManifold (𝓡∂ 9) 1 W]
  [compactSpace : CompactSpace W]
  [t2Space : T2Space W]
  /-- **The `C^∞` structure of the transverse preimage.**  The preimage theorem
  (`Work.ThomBordism.Transversality.Preimage.exists_preimage_structure`, and its local form
  `Work.PTGeometric.LocalPreimageTheorem`) produces the transverse preimage as a `C^∞` manifold with
  boundary; the `C¹` field `isManifold` is its restriction.  The `C^∞` structure is what the
  good-cover proof of the finiteness of `H_*(W;ℤ)` (hence `Work.ThomBordism.Detection`) uses. -/
  [isManifold_smooth : IsManifold (𝓡∂ 9) ∞ W]
  /-- **A collar of the boundary of the transverse preimage** (`Work.Surgery.HasCollar 8 W`):
  data of the situation, like the relative fundamental class `w` and its local-generator
  property.  In the Pontryagin–Thom construction it is what makes the pair `(W, ∂W)` amenable to
  Lefschetz duality (`Work.ThomBordism.LefschetzDualityBdry` and the crux
  `Work.ThomBordism.BoundaryMaximalIsotropic`), and it is what the double `W ∪_{∂W} W̄` is built
  from; the general collar neighbourhood theorem is *not* proved in this workspace, which is why the
  collar is data here. -/
  collar : HasBdryCollar W
  /-- the **preimage theorem**: the boundary of the transverse preimage is the end preimage -/
  bdryPreimage : ((𝓡∂ 9).boundary W) ≃ₜ ↥(endPreimage I F)
  /-- the **relative fundamental class** of `(W, ∂W)`, from the orientation of `M` and the Thom
  class of the universal bundle -/
  w : (Work.Cohomology.relChains (TopCat.of W) ((𝓡∂ 9).boundary W)).homology 9
  /-- its boundary is the sum of the fundamental classes of the pieces -/
  hw : Work.Cohomology.hPairδ (TopCat.of W) ((𝓡∂ 9).boundary W) 8 w
      = ∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X
            (TopCat.of ((𝓡∂ 9).boundary W))
            (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
              (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c
  /-- `w` is a local generator at every interior point -/
  w_fund : ∀ (x : W), (hx : x ∉ (𝓡∂ 9).boundary W) →
    Submodule.span ℤ
      {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W) ((𝓡∂ 9).boundary W) x hx) 9 w)} = ⊤

attribute [instance] TransversalPullback.topologicalSpace TransversalPullback.chartedSpace
  TransversalPullback.isManifold TransversalPullback.compactSpace TransversalPullback.t2Space
  TransversalPullback.isManifold_smooth

variable {X : CoreTarget ((8 + k) + 1) k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
  {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E' H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : M → X.E} {e : ↥(endPreimage I F) ≃ₜ (Σ i : ι, (Fam i).pt)}

/-- **The transverse preimage of the core is a null-bordism of the family.**

This is the assembly of item 2 of the chapter: the preimage theorem (encoded in
`TransversalPullback.bdryPreimage`) and orientation theory (the fundamental class `w` and its
properties) produce exactly the `NullBordismFamily` of the interface, whose boundary
homeomorphism is the composite of the preimage identification `bdryPreimage` with the given
identification `e` of the end preimage with the pieces. -/
def TransversalPullback.toNullBordismFamily (P : TransversalPullback k X ι Fam I F e) :
    NullBordismFamily ι Fam where
  W := P.W
  bdry := P.bdryPreimage.trans e
  w := P.w
  hw := P.hw
  w_fund := P.w_fund

theorem nonempty_nullBordismFamily_of_pullback (P : TransversalPullback k X ι Fam I F e)
    (hc : HasBdryCollar P.W) :
    Nonempty (NullBordismFamily ι Fam) :=
  -- `hc` is unused: `NullBordismFamily` carries no collar (see the note in `Interface.lean`).
  -- It is kept so that the callers of this theorem (the dead Transversality chapter, whose
  -- `TransversalPullback` still records the collar of the preimage as data) do not change.
  ⟨P.toNullBordismFamily⟩

/-! ## The two named inputs: orientation and the preimage theorem -/

/-- **The orientation theory of the transverse preimage** — the remaining geometric input of item
`2b`, in the form in which the chapter consumes it.

The data are those of the geometric preimage theorem: a compact smooth `(9+k)`-manifold `M` with
boundary (modelled on the half-space), a `CoreTarget` `X : CoreTarget (9+k) k`, a `C^∞` map
`F : M → X.E` transverse to the core, and a realization `W ≃ₜ F ⁻¹' X.core` of the transverse
preimage by a compact smooth `9`-manifold with boundary whose boundary is the end preimage.  The
statement is that `W` then carries the relative fundamental class `[W, ∂W] ∈ H₉(W, ∂W; ℤ)` of the
orientation induced by the orientation of `M` and by the orientation of the normal bundle of the core
(the **Thom class** of `γ_k`), and that *some* identification of `∂W` with the pieces of the family
(the end preimage being identified with them through `e`) is compatible with it, i.e. carries the
boundary class to the sum of the pieces' fundamental classes.

Why this is the honest residual, and why it cannot be reduced inside this chapter:

* the *existence* of `w` with the local-generator property is the output of the ORIENT area
  (`Work.Orient.RelativeFundamentalClassExists 8`, via
  `Work.Orient.exists_relFundClass_of_halfOrientation`), which is itself proved from two inputs
  (`Work.Orient.CoreIsoProp 8`, i.e. the collar theorem of the Surgery area, and the
  boundary-orientation convention);
* the *signed* boundary identity — the shape of the consumer's field
  `Work.ThomBordism.NullBordismFamily.hw` — is not part of the (deliberately sign-blind) ORIENT
  interface: it is the statement that the *geometric* identification of `∂W` with the pieces (the one
  produced by the collapse map of the Pontryagin–Thom construction) is orientation-compatible.  This
  is not provable from ORIENT alone;
* the identification is where the bundle-theoretic data of the GRASSMANN/PONTRYAGINTHOM areas
  (`T = Th(γ_k)`, its Thom class) enter: the orientation of `W = F ⁻¹'core` is the product of the
  orientation pulled back from `M` and the normal orientation pulled back along `Φ`.

The empty case `W = ∅` (which can occur when `F ⁻¹' X.core = ∅`) is trivially satisfiable — both
sides of the boundary identity live in `H₈(∅) = 0` — which is why the statement carries no
`Nonempty W` hypothesis (ORIENT's existence theorem does need it, so a prover of this statement has to
treat the empty case separately; the geometric realization provided by
`Preimage.exists_preimage_structure` may well be empty).

`W` and the homeomorphism `hW` are *data* of this statement rather than choices made in the proof so
that the statement can be applied to the realization produced by
`Preimage.exists_preimage_structure`.  Note that the family of admissible identifications
`bdryPreimage.trans e` (as `bdryPreimage` ranges over the homeomorphisms `∂W ≃ₜ endPreimage`, which
is nonempty by `hW` and `hbdry` and is a torsor over the self-homeomorphisms of `∂W`) does not depend
on the choice of `hW`, so the statement is a property of the geometric situation and not of the
particular realization. -/
def PullbackOrientationData (k : ℕ) (X : CoreTarget ((8 + k) + 1) k) (ι : Type) [Fintype ι]
    (Fam : ι → Man8) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E)
    (e : ↥(endPreimage (𝓡∂ ((8 + k) + 1)) F) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W]
    (hW : W ≃ₜ ↥(F ⁻¹' X.core))
    (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔
      (hW w : M) ∈ endPreimage (𝓡∂ ((8 + k) + 1)) F),
    ∃ (bdryPreimage : ((𝓡∂ 9).boundary W) ≃ₜ ↥(endPreimage (𝓡∂ ((8 + k) + 1)) F))
      (w : (Work.Cohomology.relChains (TopCat.of W) ((𝓡∂ 9).boundary W)).homology 9),
      (∀ (x : W) (hx : x ∉ (𝓡∂ 9).boundary W),
        Submodule.span ℤ {(HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W) ((𝓡∂ 9).boundary W) x hx) 9 w)} = ⊤) ∧
      (Work.Cohomology.hPairδ (TopCat.of W) ((𝓡∂ 9).boundary W) 8 w
        = ∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary W))
              (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c)

/-- **Item 2 of the chapter, second half: the transverse preimage theorem.**

A smooth map `F : M → E` from a compact smooth `(9+k)`-manifold with boundary, modelled on the
half-space, into the `(9+k)`-dimensional `CoreTarget` `X` (the manifold part of `Th(γ_k)`, with the
zero section as core), which is **transverse to the core everywhere**, whose restriction to `∂M` is
transverse to the core as well (`BoundaryTransverse`, a hypothesis that is *not* implied by
transversality of `F` near the boundary — see the `README.md` §0.1), whose end preimage of the core is
identified with the pieces of a finite family of closed oriented `8`-manifolds (the homeomorphism
`e`), **and which carries the orientation datum of the situation** (`PullbackOrientationData`: the
transverse preimage is oriented by the ambient orientation and the Thom class of `γ_k`, with the
boundary identified with the pieces as an oriented bordism), has a *transverse preimage*
`TransversalPullback`: a compact oriented `9`-manifold `W` with a relative fundamental class, whose
boundary is the end preimage.

The content is exactly the two theorems absent from Mathlib (the preimage theorem and orientation
theory); `TransversalPullback` records their output and
`TransversalPullback.toNullBordismFamily` extracts the `NullBordismFamily`.  It is *proved* from the
geometric input `Preimage.exists_preimage_structure` plus the datum, in
`Submission/Work/ThomBordism/Transversality/Preimage/orientation.lean`
(`transversalPreimageTheorem_of_data`), and `transversalPreimageTheorem` is the same statement proved
unconditionally-modulo-the-datum as a single `Prop`.

**The datum must be a datum of the situation and not a universal hypothesis.**  The *universal*
statement "for all data, the conclusion holds" is **false**: for `W = ℂP⁴ × [0,1]` (a bordism of two
copies of `ℂP⁴`) the boundary class of every relative fundamental class is `±([E₁] - [E₀])`, with
*opposite* coefficients on the two boundary components, while the pieces' classes transported to the
boundary have coefficients of the *same* sign (an orientation-reversing homeomorphism
`ℂP⁴ → ℂP⁴` does not exist), and no re-identification of `∂W` with the pieces can change the relative
signs.  See `README.md` §0.7.  This is why the chapter carries the datum as a field of the geometric
realisation (`NullHomotopyData.pullbackOrientation`, `Assembly.lean`) rather than as a hypothesis. -/
def TransversalPreimageTheorem : Prop :=
  ∀ (k : ℕ) (X : CoreTarget ((8 + k) + 1) k) (ι : Type) [Fintype ι] (Fam : ι → Man8)
    (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] (F : M → X.E),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 ((8 + k) + 1)) ∞ F →
      IsTransverse X (𝓡∂ ((8 + k) + 1)) F → BoundaryTransverse k X F →
      (e : ↥(endPreimage (𝓡∂ ((8 + k) + 1)) F) ≃ₜ (Σ i : ι, (Fam i).pt)) →
      PullbackOrientationData k X ι Fam F e →
      (∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
        [IsManifold (𝓡∂ 9) 1 W] [CompactSpace W] [T2Space W], HasBdryCollar W) →
      ∃ P : TransversalPullback k X ι Fam (𝓡∂ ((8 + k) + 1)) F e, HasBdryCollar P.W

/-! ## The assembly of item 2 -/

/-- **Item 2 of the chapter, assembled.**

Combining the two halves: a smooth map `F` from a compact smooth `(9+k)`-manifold with boundary
(modelled on the half-space) into a `CoreTarget`, transverse to the core *near the boundary* and with
its boundary restriction transverse to the core (`hbnd`), with the end preimage of the core identified
with the pieces of the family through `e`, and with the orientation datum of the situation supplied
**for every smoothing of `F` that agrees with `F` on the boundary** (this is the shape of the field
`NullHomotopyData.pullbackOrientation` of `Assembly.lean`), has a null-bordism: `F` is homotoped
relative to the boundary (`TransversalApproximation`) to a map `F'` transverse to the core
*everywhere*, and `TransversalPreimageTheorem` applied to `F'` and its datum gives the transverse
preimage, i.e. a null-bordism of the family.

The hypothesis on the datum is *not* a universal statement about all geometric data (that universal
statement is false, see the docstring of `TransversalPreimageTheorem`); it is the statement that *this*
geometric situation — the ends of `F` bounding the pieces — is oriented consistently, which is what
the Pontryagin–Thom construction supplies. -/
theorem exists_nullBordismFamily_of_inputs (happrox : TransversalApproximation)
    (hpull : TransversalPreimageTheorem) (k : ℕ) (X : CoreTarget ((8 + k) + 1) k) (ι : Type)
    [Fintype ι] (Fam : ι → Man8) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] (F : M → X.E)
    (hF : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 ((8 + k) + 1)) ∞ F)
    (htr : IsTransverseNearBoundary (𝓡∂ ((8 + k) + 1)) X F) (hbnd : BoundaryTransverse k X F)
    (e : ↥(endPreimage (𝓡∂ ((8 + k) + 1)) F) ≃ₜ (Σ i : ι, (Fam i).pt))
    (hdat : ∀ (F' : M → X.E)
      (hF' : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, F' x = F x),
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 ((8 + k) + 1)) ∞ F' →
      IsTransverse X (𝓡∂ ((8 + k) + 1)) F' → BoundaryTransverse k X F' →
      PullbackOrientationData k X ι Fam F' ((Homeomorph.setCongr (endPreimage_congr hF')).trans e))
    (hcollar : ∀ (F' : M → X.E)
      (hF' : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, F' x = F x),
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 ((8 + k) + 1)) ∞ F' →
      IsTransverse X (𝓡∂ ((8 + k) + 1)) F' → BoundaryTransverse k X F' →
      ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
        [IsManifold (𝓡∂ 9) 1 W] [CompactSpace W] [T2Space W], HasBdryCollar W) :
    Nonempty (NullBordismFamily ι Fam) := by
  obtain ⟨F', hF'sm, hF'tr, _Hh, _hHsm, _hH0, hH1, hHbd⟩ :=
    happrox ((8 + k) + 1) k (EuclideanSpace ℝ (Fin ((8 + k) + 1)))
      (EuclideanHalfSpace ((8 + k) + 1)) (𝓡∂ ((8 + k) + 1)) X M F hF htr
  have heq : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, F' x = F x := by
    intro x hx
    rw [← hH1 x, hHbd x hx 1]
  have hbnd' : BoundaryTransverse k X F' := by
    have hfun : (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => F' (y : M))
        = (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => F (y : M)) := by
      funext y
      rw [← hH1 (y : M), hHbd (y : M) y.2 1]
    rw [BoundaryTransverse] at hbnd ⊢
    rw [hfun]
    exact hbnd
  have hdata' : PullbackOrientationData k X ι Fam F'
      ((Homeomorph.setCongr (endPreimage_congr heq)).trans e) :=
    hdat F' heq hF'sm hF'tr hbnd'
  obtain ⟨P, hP⟩ := hpull k X ι Fam M F' hF'sm hF'tr hbnd'
      ((Homeomorph.setCongr (endPreimage_congr heq)).trans e) hdata'
      (hcollar F' heq hF'sm hF'tr hbnd')
  exact nonempty_nullBordismFamily_of_pullback P hP

/-- **The end preimage of the cylinder is the union of the two end preimages.**  For the cylinder
`M × [0,1]` of `boundary_cylinder` the boundary is `M × {⊥, ⊤}`, so the end preimage of the core
splits into the two ends' preimages — the two boundary components of the transverse preimage `W`. -/
theorem endPreimage_cylinder {n k : ℕ} (X : CoreTarget (n + 1) k) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (F : M × Icc (0 : ℝ) 1 → X.E) :
    endPreimage ((𝓡 n).prod (𝓡∂ 1)) F
      = ({x : M × Icc (0 : ℝ) 1 | x.2 = ⊥} ∩ {x | X.Φ (F x) = 0}) ∪
        ({x : M × Icc (0 : ℝ) 1 | x.2 = ⊤} ∩ {x | X.Φ (F x) = 0}) := by
  rw [endPreimage, boundary_cylinder]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union, Set.prod, Set.mem_univ,
    true_and, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hΦ⟩
    · exact Or.inl ⟨hx, hΦ⟩
    · exact Or.inr ⟨hx, hΦ⟩
  · rintro (⟨hx, hΦ⟩ | ⟨hx, hΦ⟩)
    · exact ⟨Or.inl hx, hΦ⟩
    · exact ⟨Or.inr hx, hΦ⟩

/-- **The end preimage of the core is compact** (when the source is compact): the boundary of the
transverse preimage is a compact space, as required for the bordism model. -/
theorem isCompact_endPreimage {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] {X : CoreTarget n k} {F : M → X.E}
    (hF : Continuous fun y => X.Φ (F y)) [CompactSpace M] :
    IsCompact (endPreimage I F) := by
  rw [endPreimage, Set.inter_comm]
  exact ((isClosed_eq hF continuous_const).inter
    (ModelWithCorners.isClosed_boundary (n := 1) (by norm_num))).isCompact

end

end Work.ThomBordism.Transversality
