import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.SignatureBordism.Bordism
import Submission.Work.Bordism.Basic
import Submission.Work.Cohomology.localHomology
import Submission.Work.Surgery.Collar

set_option synthInstance.maxHeartbeats 400000

/-!
# The chapter interface for Thom's theorem (`Work.Drive.ThomRational`)

This file fixes the **model** and the **object-level definitions** that the components of Thom's
argument are stated against, so that the components compose, and it records the **assembly** of the
target from four named inputs.  Definitions and reductions only (no `sorry`, no axioms).

## The model

* A **closed oriented `8`-manifold with its tangent Pontryagin classes** is `Man8`: a compact `T2`
  smooth (`C¹`) `8`-manifold modelled on `EuclideanSpace ℝ (Fin 8)` (corners `𝓡 8`), **possibly
  disconnected**, together with a class `c ∈ H₈` that is a **fundamental class**: its image in the
  local homology `H₈(pt, pt ∖ {x})` generates at every point (`Man8.c_fund`).  The Pontryagin
  classes are the *defined* `Work.Thom.p1Tangent'`/`p2Tangent'` — no free data.  (Disconnectedness is
  needed because the disjoint union of a family lives here; `Man8.c_fund` is what makes the number
  statements non-refutable — with an arbitrary class, three copies of `ℂP⁴` with
  `c = 2[V₁] - [V₂] - [V₃]` have vanishing numbers but `σ = -1`.)

* A **bordism with a finite family of closed oriented `8`-manifolds as boundary** is
  `NullBordismFamily ι F`: a compact `T2` smooth `9`-manifold `W` with boundary (model
  `modelWithCornersEuclideanHalfSpace 9`), a homeomorphism `∂W ≃ₜ Σ i, (F i).pt`, and the relative
  fundamental class `[W, ∂W] ∈ H₉(W, ∂W;ℤ)` (`w_fund`: a local generator at every interior point)
  whose boundary is the sum of the pieces' fundamental classes.  **Neither** `Work.Bordism.Bordism`
  **nor** `Work.Bordism.GeometricBordism` is usable: both are *degenerate* (they impose no condition
  on the ambient space or the parametrisation, so `W = pt` makes the point bordant to everything).

## The four inputs, and where `Work.Drive.StableStemsTorsion` enters

`Work.Drive.ThomRational` is assembled at the end of this file
(`thomRational_of_geometric_input`) from

1. `Smooth8Fundamental` — the *global* generation `Smooth8.c_generates` of `H₈` implies the local
   one (`Man8.c_fund`): the map `H₈(M;ℤ) → H₈(M, M∖{x};ℤ)` is an isomorphism for connected closed
   `M`;
2. two generators `X`, `Y` with the classical numbers `(p₁², p₂, σ) = (25, 10, 1)` and `(18, 9, 1)`
   (area GEN);
3. **`Generation X Y`** — the crux: for every `V` a positive multiple of `V` is bordant to a signed
   combination of `X` and `Y`.  This is Pontryagin–Thom + transversality, and the **only** place
   `Work.Drive.StableStemsTorsion` is used (`GenerationOfStems`), through rational Hurewicz in the
   stable range for the Thom space of the oriented Grassmannian;
4. `BoundarySigma`, `BoundaryP1Sq`, `BoundaryP2Num` — the sum of each of the three numbers over the
   pieces of a boundary vanishes (bordism invariance of the numbers; for `σ` this is Lefschetz
   duality for the pair `(W, ∂W)` plus additivity over the disjoint union).

## Why the family form, and what is *not* needed

An earlier version of this interface built a single `Man8` out of a weighted family (a disjoint
union).  That required (i) a `ChartedSpace`/`IsManifold` structure on a coproduct together with a
local-generator proof for the summed fundamental class, and (ii) the additivity
`Work.Bordism.sigma_disj`, whose hypothesis `FiniteDimensional ℚ (H⁴(·;ℚ))` is **not available** for a
general compact manifold (finite-CW structure is not in Mathlib).  That obstruction is not an
artifact: for an infinite-dimensional middle cohomology Mathlib's `signature` is `0` by convention
(`sigPos_le_finrank` and `finrank = 0`), so the additivity identity genuinely *fails* when one
summand is infinite-dimensional and the other is not.

With the family form, the only sums in the assembly are finite sums of **integers** over an
explicitly given family (`genFamily_sum`), which are pure arithmetic: `hirzebruch_of_generation_boundarySums`
uses no additivity of `σ` at all, and the target is reached without *any* finite-dimensionality
hypothesis on a cohomology.  The additivity of `σ` over a coproduct is still needed *inside* the
proof of `BoundarySigma` (and `Work.Bordism.sigma_disj` supplies it whenever the pieces are
finite-dimensional); only in the (mathematically unrealizable) case of an infinite-dimensional piece
does that convention become visible.

## What is missing

* `Generation` — the whole Pontryagin–Thom chapter: tubular neighbourhoods and the collapsed Gauss
  map to the Thom space `T` of the oriented Grassmannian, the rational cohomology `H^*(T;ℚ)` via the
  Thom isomorphism and the Gysin sequences of `G̃r_k(ℝ^{k+m})`, rational Hurewicz in the stable range
  (where `Work.Drive.StableStemsTorsion` enters), and transversality (`Sard`), which Mathlib does not
  have.
* `BoundarySigma`, `BoundaryP1Sq`, `BoundaryP2Num` — middle-degree Lefschetz duality for `(W, ∂W)`
  (Poincaré duality *in the middle degree* for closed manifolds **is** available in the workspace,
  `Work.Cohomology.pd_middle_even`, but it lives in an import island incompatible with
  `Work.Drive.Interfaces` — `Submission.Work.Cohomology.Crux.ovlRestrictionSurjective` and
  `Submission.Work.Cohomology.Crux.vkCruxRestr` both declare `Work.Cohomology.ovlTopX`), the
  naturality of `Work.Thom.p1Tangent'` under the boundary inclusion and under the inclusions of the
  components of a disjoint union, and the additivity of the numbers over a coproduct.
* `Smooth8Fundamental`, and the two generator manifolds with their numbers (area GEN).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-! ## The model -/

/-- The inclusion of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` for `A ⊆ B`. -/
def relChainsIncl (X : TopCat) {A B : Set X} (h : A ⊆ B) : Work.Cohomology.relChains X A ⟶
    Work.Cohomology.relChains X B :=
  Work.Cohomology.relChainsMapOf X X A B (𝟙 X)
    (TopCat.ofHom ⟨fun a => ⟨a.1, h a.2⟩,
      Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)⟩)
    (by ext a; rfl)

/-- The inclusion of relative chain complexes `C_*(X, A) ⟶ C_*(X, X ∖ {x})` for `x ∉ A`. -/
def relChainsInclPunct (X : TopCat) (A : Set X) (x : X) (hx : x ∉ A) :
    Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains X {y | y ≠ x} :=
  relChainsIncl X (fun y hy hyx => hx (hyx ▸ hy))

/-- A **closed oriented `8`-manifold with its tangent Pontryagin classes**: a compact `T2` smooth
(`C^∞`) manifold modelled on `EuclideanSpace ℝ (Fin 8)` (with corners `𝓡 8`), possibly disconnected,
together with a fundamental class `c ∈ H₈`.  The Pontryagin classes are the *defined*
`Work.Thom.p1Tangent'`, `p2Tangent'`. -/
structure Man8 where
  /-- the underlying type -/
  pt : Type
  [topologicalSpace : TopologicalSpace pt]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 8)) pt]
  [isManifold : IsManifold (𝓡 8) ∞ pt]
  [compactSpace : CompactSpace pt]
  [t2Space : T2Space pt]
  /-- the fundamental class -/
  c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of pt))).homology 8
  /-- `c` is a **fundamental class**: its image in the local homology `H₈(pt, pt ∖ {x})` generates
  that group at every point `x`. -/
  c_fund : ∀ x : pt, Submodule.span ℤ
    {HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsProj (TopCat.of pt) {y : pt | y ≠ x}) 8 c} = ⊤

attribute [instance] Man8.topologicalSpace Man8.chartedSpace Man8.isManifold Man8.compactSpace
  Man8.t2Space

/-- The `C¹` structure underlying the `C^∞` one. (Project lead, 2026-09-24: `Man8` is `C^∞` because
Pontryagin–Thom and transversality need smoothness, and every consumer is `C^∞`.) -/
instance Man8.isManifold_one (V : Man8) : IsManifold (𝓡 8) 1 V.pt :=
  IsManifold.of_le (n := ∞) (by simp)

namespace Man8

/-- The underlying space. -/
abbrev X (V : Man8) : TopCat.{0} := TopCat.of V.pt

/-- The underlying `Work.Bordism.ClosedOriented 8`. -/
def toClosedOriented (V : Man8) : Work.Bordism.ClosedOriented 8 := ⟨V.X, V.c⟩

/-- **The first Pontryagin class of the tangent bundle** (defined, not data). -/
def p1 (V : Man8) : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj V.X)).homology 4 :=
  Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) V.pt

/-- **The second Pontryagin class of the tangent bundle** (defined, not data). -/
def p2 (V : Man8) : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj V.X)).homology 8 :=
  Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) V.pt

/-- The signature `σ(V)`. -/
def sigma (V : Man8) : ℤ := Work.SignatureBordism.sigma 4 (TopCat.toSSet.obj V.X) V.c

/-- The `p₁²`-number `⟨p₁(TV) ⌣ p₁(TV), c⟩`. -/
def p1Sq (V : Man8) : ℤ := Work.SignatureBordism.p₁SqNumber (TopCat.toSSet.obj V.X) V.c V.p1

/-- The `p₂`-number `⟨p₂(TV), c⟩`. -/
def p2Num (V : Man8) : ℤ := Work.SignatureBordism.p₂Number (TopCat.toSSet.obj V.X) V.c V.p2

/-- **Orientation reversal**: the same manifold with the opposite fundamental class `-c`. -/
def neg (V : Man8) : Man8 where
  pt := V.pt
  c := -V.c
  c_fund := by
    intro x
    have h : HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsProj (TopCat.of V.pt) {y : V.pt | y ≠ x}) 8 (-V.c)
        = -(HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsProj (TopCat.of V.pt) {y : V.pt | y ≠ x}) 8 V.c) :=
      map_neg _ _
    have hset : ({-(HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsProj (TopCat.of V.pt) {y : V.pt | y ≠ x}) 8 V.c)} : Set _)
        = -({(HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsProj (TopCat.of V.pt) {y : V.pt | y ≠ x}) 8 V.c)} : Set _) := by
      ext y
      simp
    rw [h, hset, Submodule.span_neg]
    exact V.c_fund x

@[simp] theorem neg_pt (V : Man8) : V.neg.pt = V.pt := rfl
@[simp] theorem neg_c (V : Man8) : V.neg.c = -V.c := rfl

/-- **The signature changes sign under orientation reversal.** -/
@[simp] theorem neg_sigma (V : Man8) : V.neg.sigma = -V.sigma := by
  have h : Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj (TopCat.of V.pt)) (-V.c))
      = -Work.SignatureBordism.quadOfBilin
        (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj (TopCat.of V.pt)) V.c) := by
    rw [Work.SignatureBordism.ratInterForm_neg_fundamental]
    ext x
    simp only [Work.SignatureBordism.quadOfBilin_apply, LinearMap.neg_apply, neg_apply]
  show Work.SignatureBordism.signature
      (Work.SignatureBordism.quadOfBilin
        (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj (TopCat.of V.pt)) (-V.c))) = _
  rw [h, Work.SignatureBordism.signature_neg]
  rfl

/-- **The `p₁²`-number changes sign under orientation reversal.** -/
@[simp] theorem neg_p1Sq (V : Man8) : V.neg.p1Sq = -V.p1Sq :=
  Work.SignatureBordism.p₁SqNumber_neg_fundamental
    (X := TopCat.toSSet.obj (TopCat.of V.pt)) V.c
    (Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) V.pt)

/-- **The `p₂`-number changes sign under orientation reversal.** -/
@[simp] theorem neg_p2Num (V : Man8) : V.neg.p2Num = -V.p2Num :=
  Work.SignatureBordism.p₂Number_neg_fundamental
    (X := TopCat.toSSet.obj (TopCat.of V.pt)) V.c
    (Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) V.pt)

end Man8

/-- The **`Man8` data of a `Work.Drive.Smooth8`** (forget connectedness; the `C^∞` structure
restricts to the `C¹` one the model asks for).  The fundamental-class condition is taken as an
explicit hypothesis: `Smooth8Fundamental` below is the (genuine, delegated) statement that it holds
for every closed oriented smooth `8`-manifold. -/
def Man8.ofSmooth8 (M : Work.Drive.Smooth8)
    (hfund : ∀ x : M.pt, Submodule.span ℤ
      {HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsProj (TopCat.of M.pt) {y : M.pt | y ≠ x}) 8 M.c} = ⊤) : Man8 where
  pt := M.pt
  isManifold := M.isManifold
  c := M.c
  c_fund := hfund

/-- The numbers of `Man8.ofSmooth8 M` are the `Work.Drive.Smooth8` numbers of `M`. -/
theorem Man8.sigma_ofSmooth8 (M : Work.Drive.Smooth8) (h) :
    (Man8.ofSmooth8 M h).sigma = M.sigma := rfl
theorem Man8.p1Sq_ofSmooth8 (M : Work.Drive.Smooth8) (h) :
    (Man8.ofSmooth8 M h).p1Sq = M.p1Sq := rfl
theorem Man8.p2Num_ofSmooth8 (M : Work.Drive.Smooth8) (h) :
    (Man8.ofSmooth8 M h).p2Num = M.p2Num := rfl

/-! ## The numbers of the zero fundamental class

These are used to dispose of the degenerate `Smooth8`s whose class is `0` (a closed *non-orientable*
`8`-manifold has `H₈ = 0`, so `c = 0` satisfies `Work.Drive.Smooth8.c_generates`): all three numbers
vanish, so the pointwise Hirzebruch identity holds trivially there. -/

/-- The signature of the zero quadratic form vanishes. -/
theorem signature_zero {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] :
    Work.SignatureBordism.signature (0 : QuadraticForm 𝕜 V) = 0 := by
  have h := Work.SignatureBordism.signature_neg (0 : QuadraticForm 𝕜 V)
  rw [neg_zero] at h
  omega

/-- The intersection form against the zero homology class vanishes. -/
theorem interForm_zero_fundamental (R : Type) [CommRing R] (X : SSet) (m n : ℕ) :
    Work.SignatureBordism.interForm R X m n (0 : (Work.Cohomology.chainC R X).homology (m + n))
      = 0 := by
  apply LinearMap.ext; intro y
  apply LinearMap.ext; intro z
  rw [show (0 : (Work.Cohomology.chainC R X).homology (m + n))
      = (0 : R) • (0 : (Work.Cohomology.chainC R X).homology (m + n)) by simp]
  rw [Work.SignatureBordism.interForm_smul_fundamental]
  simp

/-- The `p₁²`-number of the zero fundamental class vanishes. -/
@[simp] theorem p₁SqNumber_zero_fundamental (X : SSet)
    (p₁ : (Work.Cohomology.cochainC ℤ X).homology 4) :
    Work.SignatureBordism.p₁SqNumber X 0 p₁ = 0 := by
  rw [Work.SignatureBordism.p₁SqNumber_apply, interForm_zero_fundamental]
  simp only [LinearMap.zero_apply]

/-- The `p₂`-number of the zero fundamental class vanishes. -/
@[simp] theorem p₂Number_zero_fundamental (X : SSet)
    (p₂ : (Work.Cohomology.cochainC ℤ X).homology 8) :
    Work.SignatureBordism.p₂Number X 0 p₂ = 0 := by
  rw [Work.SignatureBordism.p₂Number_apply]
  simp

/-- The signature of the zero fundamental class vanishes. -/
@[simp] theorem sigma_zero_fundamental (X : SSet) :
    Work.SignatureBordism.sigma 4 X 0 = 0 := by
  show Work.SignatureBordism.signature
    (Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.ratInterForm 4 X 0)) = 0
  have h : Work.SignatureBordism.ratInterForm 4 X (0 : (Work.Cohomology.chainC ℤ X).homology 8)
      = 0 := by
    unfold Work.SignatureBordism.ratInterForm
    rw [interForm_zero_fundamental]
    apply Work.SignatureBordism.tensor_bilin_ext
    intro a b m n
    simp [Work.SignatureBordism.baseChangeBilin_tmul]
  rw [h]
  have hq : Work.SignatureBordism.quadOfBilin
      (0 : (Work.SignatureBordism.ratCohomology 4 X) →ₗ[ℚ]
        (Work.SignatureBordism.ratCohomology 4 X) →ₗ[ℚ] ℚ) = 0 := by
    apply QuadraticMap.ext
    intro x
    simp [Work.SignatureBordism.quadOfBilin_apply]
  rw [hq]
  exact signature_zero

/-- A `Work.Drive.Smooth8` whose class vanishes has vanishing signature. -/
theorem Smooth8_sigma_eq_zero_of_c_eq_zero (M : Work.Drive.Smooth8) (h : M.c = 0) :
    M.sigma = 0 := by
  show Work.SignatureBordism.sigma 4 M.toCOS8.sset M.toCOS8.c = 0
  rw [show M.toCOS8.c = M.c from rfl, h]
  exact sigma_zero_fundamental _

/-- A `Work.Drive.Smooth8` whose class vanishes has vanishing `p₁²`-number. -/
theorem Smooth8_p1Sq_eq_zero_of_c_eq_zero (M : Work.Drive.Smooth8) (h : M.c = 0) :
    M.p1Sq = 0 := by
  show Work.SignatureBordism.p₁SqNumber M.toCOS8.sset M.toCOS8.c M.toCOS8.p1 = 0
  rw [show M.toCOS8.c = M.c from rfl, h]
  exact p₁SqNumber_zero_fundamental _ _

/-- A `Work.Drive.Smooth8` whose class vanishes has vanishing `p₂`-number. -/
theorem Smooth8_p2Num_eq_zero_of_c_eq_zero (M : Work.Drive.Smooth8) (h : M.c = 0) :
    M.p2Num = 0 := by
  show Work.SignatureBordism.p₂Number M.toCOS8.sset M.toCOS8.c M.toCOS8.p2 = 0
  rw [show M.toCOS8.c = M.c from rfl, h]
  exact p₂Number_zero_fundamental _ _

/-! ## The boundary model, for a finite family -/

/-- **A collar of the boundary**, as data of the interface: the same proposition as
`Work.Surgery.HasCollar 8 W`, re-stated with the `9`-shaped instance arguments (the ones carried by
`ChartedSpace (EuclideanHalfSpace 9)`) so that it can be used in the interface without
instance-argument plumbing.  `Work.Surgery.HasCollar 8 W` needs `ChartedSpace (EuclideanHalfSpace
(8 + 1)) W`, which does not unify with the registered instance in every context; all consumers
convert with `HasBdryCollar.hasCollar`. -/
def HasBdryCollar (W : Type*) [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W] : Prop :=
  Work.Surgery.HasCollar 8 W

/-- The interface's collar is the Surgery area's `HasCollar`. -/
theorem HasBdryCollar.hasCollar {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W] (h : HasBdryCollar W) :
    Work.Surgery.HasCollar 8 W := h

/-- **An honest oriented bordism with a finite family of closed oriented `8`-manifolds as its
boundary.**  `W` is a compact `2`nd-countable `T2` smooth (`C¹`) `9`-manifold with boundary
(modelled on the half-space), whose boundary is identified with the disjoint union
`Σ i, (F i).pt` of the pieces, together with the relative fundamental class
`[W, ∂W] ∈ H₉(W, ∂W;ℤ)`, whose boundary is the sum of the pieces' fundamental classes.

The orientation of a boundary component is encoded in the piece itself (`Man8.neg` reverses the
orientation), exactly as in the geometry.  "`N` copies of `V`" is the family `Fin N → Man8`,
`i ↦ V`, so no manifold structure on a disjoint union is ever needed. -/
structure NullBordismFamily (ι : Type) [Fintype ι] (F : ι → Man8) where
  /-- the bounding manifold -/
  W : Type
  [topologicalSpace : TopologicalSpace W]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace 9) W]
  [isManifold : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
  [compactSpace : CompactSpace W]
  [t2Space : T2Space W]
  /-- **The `C^∞` structure of the bounding manifold.**  The producers of a `NullBordismFamily`
  (the transverse preimage theorem, `Work.ThomBordism.Transversality.Preimage` /
  `Work.PTGeometric.LocalPreimageTheorem`) give the preimage as a `C^∞` manifold with boundary, and
  the finiteness of `H_*(W;ℤ)` — hence `Work.ThomBordism.Detection` — is proved for `C^∞` (`C²`
  would do, for the good-cover argument) manifolds with boundary.  The `C¹` field `isManifold` above
  is the restriction; consumers that only need `C¹` keep using it. -/
  [isManifold_smooth : IsManifold (modelWithCornersEuclideanHalfSpace 9) ∞ W]
  /- **There is deliberately no collar field here.**  An earlier revision of this interface carried
  `collar : HasBdryCollar W` as data of the null-bordism (the project lead's directive of
  2026-09-25), as the hypothesis of the layer collapse `Work.ThomBordism.RelDuality.relClass_lift`
  and hence of `Work.ThomBordism.LefschetzDualityBdry`.  That hypothesis turned out to be
  *unnecessary*: `relClass_lift` is now proved from `Work.ThomBordism.RelDuality.exists_boundaryCollapse`,
  which produces the boundary collapse datum from finitely many chart-wise collapse pieces and
  **without a collar**, and `Work.ThomBordism.Detection` is proved from the chart-based finite
  generation of `H₄(W;ℤ)` (`Work.ThomBordism.homologyFiniteOfNullBordism`, via the ENR route), also
  without a collar.  So *no* consumer of `NullBordismFamily` needs a collar, and carrying it as a
  field would force every producer (in particular the live Pontryagin–Thom construction,
  `Work.PTGeometric`) to supply a hypothesis that no proof uses.  Producers that *do* have a collar
  by construction (the Pontryagin–Thom transverse preimage: the null-homotopy is stationary near the
  collapse end, `Work.PTGeometric.GenuineNullBordismData.collar`) can still record it in their own
  data; `HasBdryCollar` and the bridge `HasBdryCollar.hasCollar` remain available above. -/
  /-- the boundary of `W` is the disjoint union of the pieces -/
  bdry : ((modelWithCornersEuclideanHalfSpace 9).boundary W) ≃ₜ (Σ i : ι, (F i).pt)
  /-- the relative fundamental class of `(W, ∂W)` -/
  w : (Work.Cohomology.relChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9
  /-- its boundary is the sum of the pieces' fundamental classes -/
  hw : Work.Cohomology.hPairδ (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 w
      = ∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (F i).X
            (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W))
            (TopCat.ofHom ⟨fun y => bdry.symm ⟨i, y⟩,
              bdry.continuous_invFun.comp continuous_sigmaMk⟩)) 8 (F i).c
  /-- `w` is a **relative fundamental class**: at every interior point `x ∈ W` its image in the local
  homology `H₉(W, W ∖ {x})` generates that group. -/
  w_fund : ∀ (x : W), (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W) →
    Submodule.span ℤ
      {HomologicalComplex.homologyMap
        (relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w} = ⊤

/-- **A single closed oriented `8`-manifold which is a boundary**, as the length-one instance of
`Work.ThomBordism.NullBordismFamily` (`Fin 1 → Man8`, constant). -/
abbrev NullBordism (V : Man8) := NullBordismFamily (Fin 1) (fun _ => V)

-- The instance fields of `NullBordismFamily` are registered so that the manifold structure of a
-- bounding manifold `W` is found by type class search (as for `Man8`).
attribute [instance] NullBordismFamily.topologicalSpace NullBordismFamily.chartedSpace
  NullBordismFamily.isManifold NullBordismFamily.compactSpace NullBordismFamily.t2Space
  NullBordismFamily.isManifold_smooth

/-- The `C¹` structure is the restriction of the `C^∞` one.  (With both instances registered, a
consumer asking for `IsManifold (𝓡∂ 9) 1 W.W` finds the field `isManifold`; one asking for
`IsManifold (𝓡∂ 9) ∞ W.W` finds `isManifold_smooth`.) -/
theorem NullBordismFamily.isManifold_of_le {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W.W := W.isManifold

/-! ## The components of Thom's argument -/

/-- The explicit family "`N` copies of `V`, then `|b₁|` signed copies of `X`, then `|b₂|` signed
copies of `Y`", used in `Work.ThomBordism.Generation`. -/
def genFamily (V X Y : Man8) (N : ℕ) (b₁ b₂ : ℤ) :
    (Fin N ⊕ (Fin b₁.natAbs ⊕ Fin b₂.natAbs)) → Man8 :=
  fun i => match i with
    | Sum.inl _ => V
    | Sum.inr (Sum.inl _) => if 0 < b₁ then X else X.neg
    | Sum.inr (Sum.inr _) => if 0 < b₂ then Y else Y.neg

/-- **The generation input of Thom's theorem** (the crux of the whole reduction): for every closed
oriented `8`-manifold `V` there are `N > 0` and integers `b₁`, `b₂` such that the disjoint union of
`N` copies of `V` and `|b₁|` signed copies of `X` and `|b₂|` signed copies of `Y` bounds — i.e.
`N [V] = b₁ [X] + b₂ [Y]` in the oriented bordism group `Ω^SO_8`.

Classically this is Pontryagin–Thom: embed `V ⊂ ℝ^{8+k}`, let `ν` be the normal bundle, collapse
`S^{8+k} → Th(γ_k) =: T` along a tubular neighbourhood and take the resulting class
`α_V ∈ π_{8+k}(T)`; rational Hurewicz in the stable range (whose homotopy-theoretic core is
`Work.Drive.StableStemsTorsion`) identifies `π_{8+k}(T) ⊗ ℚ` with `H_{8+k}(T;ℚ) ≅ H⁸(G;ℚ)`, where
`G` is the oriented Grassmannian and `H⁸(G;ℚ) = ℚ{p₁², p₂}`; the Hurewicz pairings of `α_V` with
`p₁²U`, `p₂U` are the *normal* Pontryagin numbers, which are polynomials in the tangent ones, and
transversality exhibits a positive multiple of `V` as the boundary of the combination. -/
def Generation (X Y : Man8) : Prop :=
  ∀ V : Man8, ∃ (N : ℕ) (_ : 0 < N) (b₁ b₂ : ℤ),
    Nonempty (NullBordismFamily (Fin N ⊕ (Fin b₁.natAbs ⊕ Fin b₂.natAbs))
      (genFamily V X Y N b₁ b₂))

/-- **`Generation`, with the stable stems as hypothesis**: this is the *only* place in the whole
argument where `Work.Drive.StableStemsTorsion` is used (through the rational Hurewicz theorem in the
stable range for the Thom space of the oriented Grassmannian). -/
def GenerationOfStems (X Y : Man8) : Prop :=
  Work.Drive.StableStemsTorsion → Generation X Y

/-- **(5) Bordism invariance of `σ`, in the family form.**  The signatures of the pieces of a
boundary sum add up to `0`.

Mathematically this is two ingredients: (a) *Lefschetz duality* for the pair `(W, ∂W)`, which makes
the middle form of `∂W` hyperbolic, hence of signature `0`; (b) the *additivity* of the signature
over the disjoint union of the pieces (`Work.Bordism.sigma_disj`, whose hypothesis
`FiniteDimensional ℚ (H⁴(·;ℚ))` is available for every piece except in the (formally possible but
mathematically unrealizable) case of an infinite-dimensional middle cohomology, where Mathlib's
`signature` is `0` by convention). -/
def BoundarySigma : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), NullBordismFamily ι F → ∑ i, (F i).sigma = 0

/-- The **constant-family instance** of `BoundarySigma`: if `N` copies of `V` are a boundary then
`N · σ(V) = 0`. -/
def BoundarySigmaConst : Prop :=
  ∀ (V : Man8) (N : ℕ), 0 < N → NullBordismFamily (Fin N) (fun _ => V) →
    (N : ℤ) * V.sigma = 0

/-- **Bordism invariance of the `p₁²`-number**, in the family form: the `p₁²`-numbers of the pieces
of a boundary sum add up to `0`.  (Ingredients: the naturality of `p₁Tangent'` under the boundary
inclusion and under the inclusions of the components into a disjoint union, and the fact that the
class of a disjoint union is the sum of the constituents' classes, the pairing being linear in the
homology class.) -/
def BoundaryP1Sq : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), NullBordismFamily ι F → ∑ i, (F i).p1Sq = 0

/-- **Bordism invariance of the `p₂`-number**, in the family form. -/
def BoundaryP2Num : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), NullBordismFamily ι F → ∑ i, (F i).p2Num = 0

/-- **(2)+(4) Transversality core, in the family form** — the input the assembly actually uses.  A
finite family of closed oriented `8`-manifolds whose *total* `p₁²`- and `p₂`-numbers vanish has a
positive multiple that bounds (as a family).

This is the injectivity half of Thom's theorem: "the Pontryagin numbers detect rational bordism".
Its proof is the Pontryagin–Thom chapter: embed each piece, form the Thom space `T` of the oriented
Grassmannian, get the class `α`, use rational Hurewicz in the stable range (**the only place
`Work.Drive.StableStemsTorsion` enters**) to see that a multiple of `α` is in the span of the
generators of `H_{8+k}(T;ℚ) ≅ ℚ{p₁², p₂}`, and make the null-homotopy transverse — the Pontryagin
numbers enter *on the manifold itself* (the Hurewicz pairings of `α` with `p₁²U`, `p₂U` are the
*normal* numbers, hence the tangent ones via `TV ⊕ ν ≅ ε` and the Whitney formula), so no
topological invariance of Pontryagin classes is ever needed. -/
def TransversalityCoreFamily : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∑ i, (F i).p1Sq = 0) →
    (∑ i, (F i).p2Num = 0) →
      ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N × ι) (fun k => F k.2))

/-- **(2)+(4) Transversality core, restricted to families with nonempty members.**

`Man8` carries **no** nonemptiness hypothesis (`c_fund` is a `∀ x : pt, …`, and the manifold
structure is constructible on an empty type — `Work.ThomBordism.Man8.empty`), so
`TransversalityCoreFamily` also quantifies over families with empty members; and the assembly
`Work.ThomBordism.assembly` *does* produce them (a degenerate `Work.Drive.Smooth8`, i.e. one whose
fundamental class vanishes, is replaced by `Man8.empty`).  But the producers of the geometric data
(tubular neighbourhoods, tube charts, smooth transverse null-homotopies) can only work with
**nonempty** manifolds — `Work.Tubular.hasTubularNeighbourhood`, `Work.Tubular.exists_collapse_genLoop`
and every `TubeChart` (`TubeChart.inv : Euc N → NormalTotal E` is a total function) need
`Nonempty V.pt`, and PTGEOMETRIC's `GenuineTubeGeometry` is *uninhabited* for an empty piece.
This is therefore the honest form of the input: the same statement for families all of whose members
are nonempty.

It is *equivalent* to `TransversalityCoreFamily` in the presence of the nonempty-family case:
`TransversalityCoreFamily → TransversalityCoreFamilyNE` is immediate
(`Work.ThomBordism.transversalityCoreFamilyNE_of_transversalityCore`), and the converse is
`Work.ThomBordism.transversalityCoreFamily_of_nonempty` (`nonemptyFamily.lean`), which drops the
empty members of a family — their numbers vanish
(`Work.ThomBordism.Man8.p1Sq_eq_zero_of_isEmpty` and friends, `degenerateFamily.lean`) — and
transports the resulting null-bordism across the homeomorphism of the two `Σ`-types
(`Work.ThomBordism.nullBordismFamily_subtype`). -/
def TransversalityCoreFamilyNE : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, Nonempty (F i).pt) →
    (∑ i, (F i).p1Sq = 0) → (∑ i, (F i).p2Num = 0) →
      ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N × ι) (fun k => F k.2))

/-- **The unrestricted family form implies the nonempty one** (the hypothesis is weaker). -/
theorem transversalityCoreFamilyNE_of_transversalityCore
    (h : TransversalityCoreFamily) : TransversalityCoreFamilyNE :=
  fun ι _ F _ h1 h2 => h ι F h1 h2

/-- **(2)+(4) Transversality core, restricted to families whose members are *connected*.**

This is the form the geometric producers can actually reach (project lead's decision on the
connectivity gap, probe round 14): TUBULAR's local degree
(`Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected`) and PTGEOMETRIC's last mile only
apply to a *connected* closed oriented manifold, and the producers of the tubular data
(`Work.ThomBordism.FamilyTubeData`) therefore carry `(∀ i, ConnectedSpace (F i).pt)`.

It is enough for the target: every family that the chapter's consumer
(`Work.ThomBordism.thomRational_of_transversalityCoreConn`, `connAssembly.lean`) feeds to this
statement consists of the manifolds `V i = smooth8ToMan8 (M i)` of a
`Work.Drive.Smooth8`-family, which are connected (they *are* `M i`, case `c ≠ 0`, and `Smooth8` carries
`ConnectedSpace`; `smooth8ToMan8.connectedSpace`) — the degenerate indices (`c = 0`) are **dropped**
from the family rather than replaced by `Man8.empty`, which is what makes the connectivity hypothesis
dischargeable.

`TransversalityCoreFamily` (and `TransversalityCoreFamilyNE`) imply this form, because
`ConnectedSpace` gives `Nonempty` and the hypothesis is stronger; the converse is *not* available
(dropping a non-connected *nonempty* member is not harmless, since such a manifold need not have
vanishing numbers) — which is why the consumer side is restated here as well rather than reusing
`TransversalityCoreFamily`. -/
def TransversalityCoreFamilyConn : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8), (∀ i, ConnectedSpace (F i).pt) →
    (∑ i, (F i).p1Sq = 0) → (∑ i, (F i).p2Num = 0) →
      ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N × ι) (fun k => F k.2))

/-- **The unrestricted family form implies the connected one** (the hypothesis is stronger). -/
theorem transversalityCoreFamilyConn_of_transversalityCore (h : TransversalityCoreFamily) :
    TransversalityCoreFamilyConn :=
  fun ι _ F _ h1 h2 => h ι F h1 h2

/-- **The nonempty-family form implies the connected one** (`ConnectedSpace` gives `Nonempty`). -/
theorem transversalityCoreFamilyConn_of_NE (h : TransversalityCoreFamilyNE) :
    TransversalityCoreFamilyConn :=
  fun ι _ F _ h1 h2 => h ι F (fun _ => inferInstance) h1 h2

/-- **(2)+(4) Transversality core.**  A closed oriented `8`-manifold whose `p₁²`- and `p₂`-numbers
vanish has a positive multiple that bounds: the geometric half of the crux (Pontryagin–Thom plus the
transversality argument turning the vanishing of the Hurewicz pairings into a null-bordism).  No
generator is mentioned. -/
def TransversalityCore : Prop :=
  ∀ V : Man8, V.p1Sq = 0 → V.p2Num = 0 →
    ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N) (fun _ => V))

/-- **The geometric core**: a closed oriented `8`-manifold with vanishing `p₁²`- and `p₂`-numbers has
vanishing signature. -/
def GeometricCore : Prop :=
  ∀ V : Man8, V.p1Sq = 0 → V.p2Num = 0 → V.sigma = 0

/-- **The signature vanishes whenever the middle cohomology is infinite-dimensional.**  This is a
fact about Mathlib's `signature` (hence about `Man8.sigma`): `sigPos Q ≤ finrank`, and Mathlib's
`finrank` is `0` on an infinite-dimensional space, so `sigPos = sigNeg = 0`.  It is the reason the
additivity of `σ` over a disjoint union genuinely fails when one summand is infinite-dimensional and
the other is not, and it is the case in which `BoundarySigma` carries no information. -/
theorem Man8.sigma_eq_zero_of_not_finiteDimensional (V : Man8)
    (h : ¬ FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj V.X))) :
    V.sigma = 0 := by
  haveI : Module.Free ℚ (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj V.X)) :=
    Module.Free.of_divisionRing ℚ _
  have h0 : Module.finrank ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj V.X)) = 0 := by
    refine finrank_eq_zero_of_not_exists_basis_finset (fun hs => h ?_)
    obtain ⟨s, ⟨b⟩⟩ := hs
    exact Module.Finite.of_basis b
  have hle : sigPos (Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj V.X) V.c)) ≤ 0 := by
    rw [← h0]; exact sigPos_le_finrank _
  have hle' : sigPos (-(Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj V.X) V.c))) ≤ 0 := by
    rw [← h0]; exact sigPos_le_finrank _
  show Work.SignatureBordism.signature (Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj V.X) V.c)) = 0
  simp only [Work.SignatureBordism.signature, sigNeg, Nat.eq_zero_of_le_zero hle,
    Nat.eq_zero_of_le_zero hle']
  norm_num

/-- **Bordism invariance of `σ`**, in the length-one form: a closed oriented `8`-manifold that
bounds has signature `0`. -/
def BordismInvariance : Prop :=
  ∀ V : Man8, NullBordism V → V.sigma = 0

/-- The signature of the pieces of a boundary sum vanishes. -/
theorem boundarySigmaConst_of_boundarySigma (h : BoundarySigma) : BoundarySigmaConst := by
  intro V N hN W
  have h0 := h (Fin N) (fun _ => V) W
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h0

/-- **Components (2)+(4) and (5) give the geometric core.** -/
theorem geometricCore_of_transversalityCore_boundarySigma
    (ht : TransversalityCore) (hb : BoundarySigma) : GeometricCore := by
  intro V h1 h2
  obtain ⟨N, hN, ⟨W⟩⟩ := ht V h1 h2
  have h0 : (N : ℤ) * V.sigma = 0 := boundarySigmaConst_of_boundarySigma hb V N hN W
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hN.ne')

/-- **Components (2)+(4) (family form) and (5) give the geometric core.** -/
theorem geometricCore_of_transversalityCoreFamily_boundarySigma
    (ht : TransversalityCoreFamily) (hb : BoundarySigma) : GeometricCore := by
  intro V h1 h2
  obtain ⟨N, hN, ⟨W⟩⟩ := ht (Fin 1) (fun _ => V) (by simpa using h1) (by simpa using h2)
  have h0 := hb (Fin N × Fin 1) (fun _ => V) W
  have hsum : (∑ k : Fin N × Fin 1, (V.sigma : ℤ)) = N * V.sigma := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one,
      one_mul]
  rw [hsum] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hN.ne')

/-! ## The assembly: `ThomRational` from the four inputs -/

/-- The sum of a `neg`-antisymmetric integer function over the generation family
(`Work.ThomBordism.genFamily`): `N` copies of `V` plus `|b₁|` signed copies of `X` plus `|b₂|`
signed copies of `Y` contribute `N f V + b₁ f X + b₂ f Y`.  This is pure arithmetic on the index
set — no manifold theory is involved. -/
theorem genFamily_sum (f : Man8 → ℤ) (hneg : ∀ W : Man8, f W.neg = -f W)
    (V X Y : Man8) (N : ℕ) (b₁ b₂ : ℤ) :
    ∑ i, f (genFamily V X Y N b₁ b₂ i) = N * f V + b₁ * f X + b₂ * f Y := by
  have h1 : ∀ (Z : Man8) (b : ℤ),
      (∑ _ : Fin b.natAbs, f (if 0 < b then Z else Z.neg)) = b * f Z := by
    intro Z b
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hb : 0 < b
    · rw [if_pos hb, Int.natAbs_of_nonneg hb.le]
    · rw [if_neg hb, hneg Z, ← Int.natAbs_neg,
        Int.natAbs_of_nonneg (neg_nonneg_of_nonpos (not_lt.mp hb))]
      ring
  have hN : (∑ _ : Fin N, f V) = N * f V := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [genFamily, hN, h1 X b₁, h1 Y b₂]
  ring

/-- **`Hirz8` from the generation input and the three boundary statements**, for manifolds in the
`Man8` model.

Fix `V` and let `N`, `b₁`, `b₂` and the boundary `W` of the generation family be given by
`Generation`.  Applying the three `Boundary*` statements to `W` and evaluating the sums over the
explicit family (`genFamily_sum`) gives

`N σ(V) + b₁ σ(X) + b₂ σ(Y) = 0`,  `N p₁²(V) + b₁ p₁²(X) + b₂ p₁²(Y) = 0`,
`N p₂(V) + b₁ p₂(X) + b₂ p₂(Y) = 0`.

Together with the two generators' identities `45 σ(X) = 7 p₂(X) - p₁²(X)`,
`45 σ(Y) = 7 p₂(Y) - p₁²(Y)`, this gives `N (45 σ(V) - (7 p₂(V) - p₁²(V))) = 0`, and `N > 0`. -/
theorem hirzebruch_of_generation_boundarySums
    (X Y : Man8) (hgen : Generation X Y) (hσ : BoundarySigma) (hA : BoundaryP1Sq)
    (hB : BoundaryP2Num)
    (hX : X.p1Sq = 25 ∧ X.p2Num = 10 ∧ X.sigma = 1)
    (hY : Y.p1Sq = 18 ∧ Y.p2Num = 9 ∧ Y.sigma = 1) :
    ∀ V : Man8, 45 * V.sigma = 7 * V.p2Num - V.p1Sq := by
  intro V
  obtain ⟨N, hN, b₁, b₂, ⟨W⟩⟩ := hgen V
  have hs := hσ _ (genFamily V X Y N b₁ b₂) W
  have ha := hA _ (genFamily V X Y N b₁ b₂) W
  have hb := hB _ (genFamily V X Y N b₁ b₂) W
  rw [genFamily_sum (fun W => W.sigma) (fun W => W.neg_sigma) V X Y N b₁ b₂] at hs
  rw [genFamily_sum (fun W => W.p1Sq) (fun W => W.neg_p1Sq) V X Y N b₁ b₂] at ha
  rw [genFamily_sum (fun W => W.p2Num) (fun W => W.neg_p2Num) V X Y N b₁ b₂] at hb
  obtain ⟨hXs, hXb, hXp⟩ := hX
  obtain ⟨hYs, hYb, hYp⟩ := hY
  have h2 : (N : ℤ) * (45 * V.sigma - (7 * V.p2Num - V.p1Sq)) = 0 := by
    have h1 : 45 * (b₁ * X.sigma + b₂ * Y.sigma) = 7 * (b₁ * X.p2Num + b₂ * Y.p2Num)
        - (b₁ * X.p1Sq + b₂ * Y.p1Sq) := by
      rw [hXs, hXb, hXp, hYs, hYb, hYp]; ring
    have hb1 : b₁ * X.sigma + b₂ * Y.sigma = -(N : ℤ) * V.sigma := by linarith [hs]
    have ha1 : b₁ * X.p1Sq + b₂ * Y.p1Sq = -(N : ℤ) * V.p1Sq := by linarith [ha]
    have hb2 : b₁ * X.p2Num + b₂ * Y.p2Num = -(N : ℤ) * V.p2Num := by linarith [hb]
    rw [hb1, ha1, hb2] at h1
    linarith
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hN')

/-- **The local-generator condition for the `Man8` data of a `Work.Drive.Smooth8`, in the
non-degenerate case.**  `Work.Drive.Smooth8` requires only that `M.c` *generates* `H₈(M;ℤ)`; the
trivial group is generated by `0`, so for a closed **non-orientable** `8`-manifold (where
`H₈(M;ℤ) = 0`, e.g. `ℝP⁸`) `c = 0` satisfies the interface and is *not* a fundamental class.  For
`c ≠ 0` the manifold is orientable and `c = ± [M]`, and then `c` is a *local* generator at every
point: this is the statement delegated here (the map `H₈(M;ℤ) → H₈(M, M∖{x};ℤ)` is an isomorphism
for a closed connected orientable `8`-manifold, since `H₈(M ∖ {x};ℤ) = 0`).

The degenerate case `c = 0` is *not* an obstruction to the target: all three numbers vanish there
(the lemmas above), so the pointwise identity holds trivially. -/
def Smooth8Fundamental : Prop :=
  ∀ M : Work.Drive.Smooth8, M.c ≠ 0 → ∀ x : M.pt, Submodule.span ℤ
    {HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsProj (TopCat.of M.pt) {y : M.pt | y ≠ x}) 8 M.c} = ⊤

/-- **The whole reduction of `Work.Drive.ThomRational`.**  Given

* the fundamental-class lemma `Smooth8Fundamental`,
* two closed oriented `8`-manifolds `X`, `Y` with the classical numbers `(25, 10, 1)` and
  `(18, 9, 1)` (area GEN),
* the generation input `Generation X Y` (the crux; with `Work.Drive.StableStemsTorsion` as hypothesis
  see `GenerationOfStems`),
* the three boundary statements `BoundarySigma`, `BoundaryP1Sq`, `BoundaryP2Num`,

Thom's theorem in its rational form follows.  The algebra is the same as in
`Work.ThomBordism.thomRational_of_hirzebruch`: the pointwise identity for every manifold is
`hirzebruch_of_generation_boundarySums`, and a weighted family with vanishing weighted `p₁²`- and
`p₂`-numbers then has vanishing weighted signature by linearity. -/
theorem thomRational_of_geometric_input
    (hfund : Smooth8Fundamental) (X Y : Man8)
    (hX : X.p1Sq = 25 ∧ X.p2Num = 10 ∧ X.sigma = 1)
    (hY : Y.p1Sq = 18 ∧ Y.p2Num = 9 ∧ Y.sigma = 1)
    (hgen : Generation X Y) (hσ : BoundarySigma) (hA : BoundaryP1Sq) (hB : BoundaryP2Num) :
    Work.Drive.ThomRational := by
  have hpt := hirzebruch_of_generation_boundarySums X Y hgen hσ hA hB hX hY
  intro n M w h1 h2
  have key : ∀ i, 45 * (M i).sigma = 7 * (M i).p2Num - (M i).p1Sq := fun i => by
    by_cases hc : (M i).c = 0
    · rw [Smooth8_sigma_eq_zero_of_c_eq_zero (M i) hc,
        Smooth8_p1Sq_eq_zero_of_c_eq_zero (M i) hc,
        Smooth8_p2Num_eq_zero_of_c_eq_zero (M i) hc]
      ring
    · have h := hpt (Man8.ofSmooth8 (M i) (hfund (M i) hc))
      simpa only [Man8.sigma_ofSmooth8, Man8.p1Sq_ofSmooth8, Man8.p2Num_ofSmooth8] using h
  have h45 : 45 * (∑ i, w i * (M i).sigma) = 0 := by
    calc 45 * (∑ i, w i * (M i).sigma)
        = ∑ i, w i * (45 * (M i).sigma) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i, w i * (7 * (M i).p2Num - (M i).p1Sq) :=
            Finset.sum_congr rfl (fun i _ => by rw [key i])
      _ = ∑ i, (7 * (w i * (M i).p2Num) - w i * (M i).p1Sq) :=
            Finset.sum_congr rfl (fun i _ => by ring)
      _ = 7 * (∑ i, w i * (M i).p2Num) - ∑ i, w i * (M i).p1Sq := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by rw [h2, h1]; ring
  exact (mul_eq_zero.mp h45).resolve_left (by norm_num)

end

end Work.ThomBordism
