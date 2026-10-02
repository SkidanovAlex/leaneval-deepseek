import Mathlib
import Submission.Work.Surgery.Collar
import Submission.Work.Orient.Boundary
import Submission.Work.ThomBordism.orientOfCollar
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint
import Submission.Work.Orient.Boundary.ExistsInteriorHalfBall
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.CoreClass
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.ThomBordism.piecesBound_locClass_eq_of_core

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT item 2, pointwise and *local*: the relative fundamental class realises a given
half-orientation family exactly

`Work.ThomBordism.exists_relFundClass_of_collar` (`Submission/Work/ThomBordism/orientOfCollar.lean`)
produces, for a compact `(n+1)`-manifold `M` with boundary carrying a half-orientation family `γ` and
a collar `c`, a relative fundamental class `w ∈ H_{n+1}(M, ∂M)`: at every interior point the
localisation of `w` *generates* the local group `H_{n+1}(M, M∖{x}) ≅ ℤ`.

Here we prove the **signed, exact** form of that statement: the localisation of `w` at every interior
point is *equal* to the given local class `γ x`.  This is the form the boundary-orientation chapter
consumes (`Work.ThomBordism.NullBordismFamily.w_fund`).

## The proof

The class `w` is the one transported from the compact core `C₀ = (collarRegion c 1)ᶜ` by the
isomorphism `H_{n+1}(M, ∂M) ⟶ H_{n+1}(M, M∖C₀)` of `Work.ThomBordism.coreIso_of_collar`, where the
class over the core is the one produced by `Work.Orient.Boundary.exists_coreClass` — whose
localisations at the points of `C₀` are `γ` *exactly*.  This gives the exact statement on the core.

The exact statement then spreads from the core to the whole interior by the local constancy of the
*comparison* between the localisation of `w` and the family `γ`:

* over a coordinate half-ball `K` of the interior, both the localisation of `w` at `y ∈ K` and `γ y`
  are the images of single classes of `H_{n+1}(M, M∖K)` (`relChainsIncl` of `w`, and the coherence
  class of `γ` supplied by the second conjunct of `IsHalfOrientationFamily`), and the localisation
  `H_{n+1}(M, M∖K) → H_{n+1}(M, M∖{y})` is **injective** (`HalfRestrictIsoAtPoint`);
* hence "the localisation of `w` at `y` equals `γ y`" is independent of `y ∈ K`: it is a *clopen*
  condition on the interior `M°`, and `[0,1]` is preconnected, so it spreads along any path in `M°`
  from a point of `C₀`.

The general hypothesis on `γ` used by the spreading step is only that `γ` is locally realised by a
class over an open set (`Work.ThomBordism.relPunct_locClass_eq_of_core`); for a half-orientation
family this is the coherence clause (`Work.ThomBordism.localWitnesses_of_halfOrientationFamily`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Filter
open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

/-! ## The localisation of a relative class at a point of a coordinate half-ball

General-`n` form of `Work.ThomBordism.resRelH_relChainsIncl_eq_relChainsInclPunct`. -/

/-- **The local class of `z` at `y ∈ K`, computed on `H_{n+1}(M, M∖K)`.**

If `K` is disjoint from `B`, `y ∈ K` and `y ∉ B`, then restricting a class `z ∈ H_{n+1}(M, B)` first
to `H_{n+1}(M, M∖K)` and then to the local group at `y` is the local class of `z` at `y`.  The
composite is the restriction along `B ⊆ {y}ᶜ`. -/
theorem resRelH_relChainsIncl_eq_relChainsInclPunct_gen {n : ℕ}
    (X : TopCat) {B K : Set X} (hBK : B ⊆ Kᶜ) {y : X} (hyK : y ∈ K) (hy : y ∉ B)
    (z : (Work.Cohomology.relChains X B).homology (n + 1)) :
    Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK)
        ((HomologicalComplex.homologyMap (relChainsIncl X hBK) (n + 1)).hom z)
      = (HomologicalComplex.homologyMap
          (relChainsInclPunct X B y hy) (n + 1)).hom z := by
  have h2 : Kᶜ ⊆ ({y} : Set X)ᶜ := Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyK)
  rw [resRelH_eq_homologyMap_relChainsIncl' X (n + 1) (Set.singleton_subset_iff.mpr hyK)]
  rw [← ModuleCat.comp_apply]
  rw [← HomologicalComplex.homologyMap_comp]
  have hcongr : (relChainsIncl X hBK ≫ relChainsIncl X h2)
      = relChainsIncl X (A := B) (B := {a : X | a ≠ y})
          (fun a ha hax => hy (hax ▸ ha)) := by
    rw [td_relChainsIncl_trans]
  rw [hcongr]
  rfl

/-- **Agreement over a coordinate half-ball is a single linear condition** (general `n` form of
`Work.ThomBordism.agreement_iff_of_injective`).

Let `a ∈ H_{n+1}(M, M∖U)` be a class whose localisations on the open set `U` are the family `Φ`, let
`z ∈ H_{n+1}(M, B)`, and let `K ⊆ U ∩ Bᶜ` be a set over which the localisation to a point of `K` is
**injective**.  Then the comparison `Φ x = (local class of z at x)` holds at one point of `K` if and
only if it holds at another. -/
theorem agreement_iff_of_injective_gen {n : ℕ}
    (X : TopCat) {B K U : Set X} (hBK : B ⊆ Kᶜ) (hKU : K ⊆ U)
    (hinj : ∀ y (hyK : y ∈ K),
      Function.Injective (Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK)))
    (a : Work.Orient.RelH X (n + 1) U) (Φ : ∀ x : X, x ∉ B → Work.Orient.LocH X (n + 1) x)
    (ha : ∀ y (hyU : y ∈ U) (hy : y ∉ B),
      Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyU) a = Φ y hy)
    (z : (Work.Cohomology.relChains X B).homology (n + 1))
    {x y : X} (hxK : x ∈ K) (hyK : y ∈ K) (hx : x ∉ B) (hy : y ∉ B) :
    (HomologicalComplex.homologyMap (relChainsInclPunct X B x hx) (n + 1)).hom z = Φ x hx
      ↔ (HomologicalComplex.homologyMap (relChainsInclPunct X B y hy) (n + 1)).hom z = Φ y hy := by
  let u : Work.Orient.RelH X (n + 1) K :=
    (HomologicalComplex.homologyMap (relChainsIncl X hBK) (n + 1)).hom z
  let aK : Work.Orient.RelH X (n + 1) K := Work.Orient.resRelH X (n + 1) hKU a
  let w : Work.Orient.RelH X (n + 1) K := u - aK
  have hw : ∀ (y : X) (hyK : y ∈ K) (hy : y ∉ B),
      Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) w = 0
        ↔ (HomologicalComplex.homologyMap (relChainsInclPunct X B y hy) (n + 1)).hom z
            = Φ y hy := by
    intro y hyK hy
    have h1 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) w
        = Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) u
          - Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) aK := by
      simp only [w, map_sub]
    have h2 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) u
        = (HomologicalComplex.homologyMap
            (relChainsInclPunct X B y hy) (n + 1)).hom z :=
      resRelH_relChainsIncl_eq_relChainsInclPunct_gen X hBK hyK hy z
    have h3 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) aK = Φ y hy := by
      simp only [aK]
      exact (LinearMap.congr_fun (Work.Orient.Port.RelHmap_comp' X (n + 1)
        (Set.singleton_subset_iff.mpr hyK) hKU
        (Set.singleton_subset_iff.mpr (hKU hyK))) a).trans (ha y (hKU hyK) hy)
    rw [h1, h2, h3]
    exact sub_eq_zero
  constructor
  · intro h
    have h0 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hxK) w = 0 :=
      (hw x hxK hx).mpr h
    have h0' : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hxK) w
        = Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hxK) 0 := by
      rw [map_zero, h0]
    have hw0 : w = 0 := hinj x hxK h0'
    have h1 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) w = 0 := by
      rw [hw0, map_zero]
    exact (hw y hyK hy).mp h1
  · intro h
    have h0 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) w = 0 :=
      (hw y hyK hy).mpr h
    have h0' : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) w
        = Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK) 0 := by
      rw [map_zero, h0]
    have hw0 : w = 0 := hinj y hyK h0'
    have h1 : Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hxK) w = 0 := by
      rw [hw0, map_zero]
    exact (hw x hxK hx).mp h1

/-- **The localisation out of an interior coordinate half-ball is injective**, at every one of its
points (general `n` form of `Work.ThomBordism.injective_resRelH_halfBallPiece`). -/
theorem injective_resRelH_halfBallPiece_gen {n : ℕ}
    (X : TopCat) [CompactSpace X] [T2Space X] [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    (z0 : X) (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) X z0 r)
    (hint : ∀ y ∈ Work.Orient.halfBallPiece (n + 1) X z0 r,
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X)
    (y : X) (hy : y ∈ Work.Orient.halfBallPiece (n + 1) X z0 r) :
    Function.Injective (Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hy)) := by
  have h := Work.Orient.Boundary.HalfRestrictIsoAtPoint n X z0 r hr hgood hint y hy
  exact (ConcreteCategory.isIso_iff_bijective _).mp h |>.1

/-! ## Spreading the comparison from a compact core -/

/-- **The comparison of a relative class with a locally-realised family spreads from a core**
(general `n` form of `Work.ThomBordism.piecesBound_locClass_core_aux`). -/
theorem relPunct_locClass_core_aux {n : ℕ}
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ChartedSpace (EuclideanHalfSpace (n + 1)) X]
    (C₀ : Set X)
    (hC₀int : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X)
    (hC₀conn : ∀ (x : X) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X),
      ∃ (y : X) (hy : y ∈ C₀) (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X),
        Nonempty (Path (⟨x, hx⟩ : {z : X //
            z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X}) ⟨y, hy'⟩))
    (z : (Work.Cohomology.relChains X
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary X)).homology (n + 1))
    (Φ : ∀ x : X, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X →
      Work.Orient.LocH X (n + 1) x)
    (hΦ : ∀ x : X, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X →
      ∃ U : Set X, x ∈ U ∧
        U ⊆ {y : X | y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X} ∧
        IsOpen U ∧ ∃ a : Work.Orient.RelH X (n + 1) U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X),
            Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyU) a = Φ y hy)
    (hcore : ∀ (x : X) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (relChainsInclPunct X
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary X) x (hC₀int x hx)) (n + 1)).hom z
        = Φ x (hC₀int x hx)) :
    ∀ (x : X) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X),
      (HomologicalComplex.homologyMap (relChainsInclPunct X
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary X) x hx) (n + 1)).hom z
        = Φ x hx := by
  classical
  let B : Set X := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary X
  let P : {z : X // z ∉ B} → Prop := fun p =>
    (HomologicalComplex.homologyMap (relChainsInclPunct X B p.1 p.2) (n + 1)).hom z = Φ p.1 p.2
  -- `P` is locally constant on the interior
  have key : ∀ p : {z : X // z ∉ B}, ∃ V ∈ 𝓝 p, ∀ q ∈ V, (P q ↔ P p) := by
    intro p
    obtain ⟨U, hpU, hUint, hUopen, a, ha⟩ := hΦ p.1 p.2
    have hBclosed : IsClosed B := Work.Orient.Boundary.isClosed_boundary_halfSpace n X
    have hxU : p.1 ∈ U ∩ Bᶜ := ⟨hpU, p.2⟩
    obtain ⟨r, hr, hgood, hsub⟩ :=
      Work.Orient.Boundary.exists_halfBall_subset n (W := X)
        (hUopen.inter hBclosed.isOpen_compl) hxU
    refine ⟨Subtype.val ⁻¹' (Work.Orient.halfBallPiece (n + 1) X p.1 r), ?_, ?_⟩
    · exact (continuous_subtype_val.continuousAt).preimage_mem_nhds
        (Work.Orient.Boundary.halfBallPiece_mem_nhds (n := n) (W := X) hr)
    · intro q hq
      have hBK : B ⊆ (Work.Orient.halfBallPiece (n + 1) X p.1 r)ᶜ :=
        fun y hy hyK => (hsub hyK).2 hy
      have hKU : Work.Orient.halfBallPiece (n + 1) X p.1 r ⊆ U := fun y hy => (hsub hy).1
      have hinj : ∀ y (hyK : y ∈ Work.Orient.halfBallPiece (n + 1) X p.1 r),
          Function.Injective (Work.Orient.resRelH X (n + 1) (Set.singleton_subset_iff.mpr hyK)) :=
        fun y hyK => injective_resRelH_halfBallPiece_gen X p.1 r hr hgood
          (fun y hy => (hsub hy).2) y hyK
      exact agreement_iff_of_injective_gen X hBK hKU hinj a Φ ha z hq
        (Work.Orient.mem_halfBallPiece_center (n := n + 1) (W := X) (z := p.1) (r := r) hr) q.2 p.2
  have hopen : IsOpen {p : {z : X // z ∉ B} | P p} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨V, hV, hVP⟩ := key p
    exact Filter.mem_of_superset hV (fun q hq => (hVP q hq).mpr hp)
  have hclosed : IsClosed {p : {z : X // z ∉ B} | P p} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨V, hV, hVP⟩ := key p
    exact Filter.mem_of_superset hV (fun q hq hqP => hp ((hVP q hq).mp hqP))
  intro x hx
  obtain ⟨y, hyC₀, hy', ⟨γ⟩⟩ := hC₀conn x hx
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hcl : IsClopen {s : Set.Icc (0 : ℝ) 1 | P (γ s)} :=
    ⟨hclosed.preimage γ.continuous, hopen.preimage γ.continuous⟩
  have hcore' : ∀ (w : X) (hw : w ∈ C₀), P ⟨w, hC₀int w hw⟩ := fun w hw => hcore w hw
  have hne : ({s : Set.Icc (0 : ℝ) 1 | P (γ s)}).Nonempty :=
    ⟨1, by show P (γ 1); rw [Path.target γ]; exact hcore' y hyC₀⟩
  have huniv := hcl.eq_univ hne
  have hpath : ∀ s : Set.Icc (0 : ℝ) 1, P (γ s) := by
    intro s
    have hs : s ∈ {s : Set.Icc (0 : ℝ) 1 | P (γ s)} := by rw [huniv]; trivial
    exact hs
  have h0 : P (γ 0) := hpath 0
  have h0' : P (Subtype.mk x hx) := by rw [← Path.source γ]; exact h0
  exact h0'

/-- **`Work.ThomBordism.relPunct_locClass_eq_of_core`**: the local class of a relative class is
determined by its values on a core, for a family of local classes `Φ` which is locally realised by a
class over an open set of the interior.

This is `relPunct_locClass_core_aux` in the spelling of the target (`Work.Orient.relPunct`). -/
theorem relPunct_locClass_eq_of_core_local {n : ℕ} {W : Type} [TopologicalSpace W] [T2Space W]
    [CompactSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {C₀ : Set W}
    (hC₀int : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hC₀conn : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      ∃ (y : W) (hy : y ∈ C₀) (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
        Nonempty (Path (⟨x, hx⟩ : {z : W //
            z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ⟨y, hy'⟩))
    (z : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (Φ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH (TopCat.of W) (n + 1) x)
    (hΦ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      ∃ U : Set W, x ∈ U ∧
        U ⊆ {y : W | y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} ∧
        IsOpen U ∧ ∃ a : Work.Orient.RelH (TopCat.of W) (n + 1) U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
            Work.Orient.resRelH (TopCat.of W) (n + 1) (Set.singleton_subset_iff.mpr hyU) a
              = Φ y hy)
    (hcore : ∀ (x : W) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x (hC₀int x hx)) (n + 1)).hom z
        = Φ x (hC₀int x hx)) :
    ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x hx) (n + 1)).hom z
        = Φ x hx :=
  relPunct_locClass_core_aux (TopCat.of W) C₀ hC₀int hC₀conn z Φ hΦ hcore

/-- **The coherence clause of a half-orientation family, in the "local witness" form**: at every
interior point the family `γ` is, on an open neighbourhood contained in the interior, the
specialisation of a single class of the relative homology. -/
theorem localWitnesses_of_halfOrientationFamily_local {n : ℕ} {W : Type} [TopologicalSpace W]
    [T2Space W] [CompactSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH (TopCat.of W) (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n (TopCat.of W) γ) :
    ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      ∃ U : Set W, x ∈ U ∧
        U ⊆ {y : W | y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W} ∧
        IsOpen U ∧ ∃ a : Work.Orient.RelH (TopCat.of W) (n + 1) U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
            Work.Orient.resRelH (TopCat.of W) (n + 1) (Set.singleton_subset_iff.mpr hyU) a
              = γ y hy := by
  intro x hx
  have hBclosed : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Work.Orient.Boundary.isClosed_boundary_halfSpace n (TopCat.of W)
  have hUopen : IsOpen (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))ᶜ :=
    hBclosed.isOpen_compl
  obtain ⟨r, hr, hgood, hsub⟩ :=
    Work.Orient.Boundary.exists_halfBall_subset n (W := TopCat.of W) hUopen hx
  obtain ⟨U, hUK, hUopen', hxU⟩ := mem_nhds_iff.mp
    (Work.Orient.Boundary.halfBallPiece_mem_nhds (n := n) (W := TopCat.of W) (z := x) (r := r) hr)
  have hKint : ∀ y ∈ Work.Orient.halfBallPiece (n + 1) (TopCat.of W) x r,
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := fun y hy => hsub hy
  have hKcoord : Work.Orient.IsCoordHalfBall (n + 1) (TopCat.of W)
      (Work.Orient.halfBallPiece (n + 1) (TopCat.of W) x r) := ⟨x, r, hr, hgood, rfl⟩
  obtain ⟨aK, haK⟩ := hγ.2 (Work.Orient.halfBallPiece (n + 1) (TopCat.of W) x r) hKcoord hKint
  refine ⟨U, hxU, fun z hz => hsub (hUK hz), hUopen', ?_⟩
  refine ⟨Work.Orient.resRelH (TopCat.of W) (n + 1) hUK aK, ?_⟩
  intro y hyU hy
  have hyK : y ∈ Work.Orient.halfBallPiece (n + 1) (TopCat.of W) x r := hUK hyU
  have h1 := Work.Orient.Port.RelHmap_comp' (TopCat.of W) (n + 1)
    (Set.singleton_subset_iff.mpr hyU) hUK (Set.singleton_subset_iff.mpr hyK)
  change (RelHmap (TopCat.of W) (n + 1) (Set.singleton_subset_iff.mpr hyU))
    ((RelHmap (TopCat.of W) (n + 1) hUK) aK) = γ y hy
  rw [← LinearMap.comp_apply, h1]
  exact haK y hy hyK

/-! ## The relative fundamental class of a collar, with the prescribed local classes -/

/-- **ORIENT item 2, pointwise and exact**: for a compact `C^∞` `(n+1)`-manifold `M` with boundary,
a collar `c` of `M` and a half-orientation family `γ`, there is a relative fundamental class
`w ∈ H_{n+1}(M, ∂M)` whose localisation at **every** interior point is the given local class
`γ x`. -/
theorem exists_relFundClass_of_collar_loc {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (c : Work.Surgery.Collar n M)
    (γ : ∀ x : M, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M →
      Work.Orient.LocH (TopCat.of M) (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n (TopCat.of M) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1),
      Work.Orient.IsRelFundClass (TopCat.of M) (n + 1)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) w ∧
      (∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
        (HomologicalComplex.homologyMap
          (Work.Orient.relPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x hx) (n + 1)).hom w
          = γ x hx) := by
  classical
  -- the compact core of the interior produced by the collar, and the isomorphism it gives
  obtain ⟨C₀, hCp, hint, hconn, hiso⟩ := coreIso_of_collar (n := n) c
  have hbc : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M ⊆ C₀ᶜ :=
    fun z hz hzC => hint z hzC hz
  -- a class over the core whose localisations are exactly `γ`
  obtain ⟨u₀, hu₀⟩ := Work.Orient.Boundary.exists_coreClass n (TopCat.of M) hCp hint γ hγ
  let φ : (Work.Cohomology.relChains (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)).homology (n + 1) ⟶
      (Work.Cohomology.relChains (TopCat.of M) C₀ᶜ).homology (n + 1) :=
    HomologicalComplex.homologyMap (Work.Orient.relChainsIncl (TopCat.of M)
      (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) hbc) (n + 1)
  haveI : IsIso φ := hiso
  obtain ⟨w, hw⟩ := ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance).2 u₀
  -- the localisations of `w` at the points of the core
  have hcore : ∀ (x : M) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x (hint x hx)) (n + 1)).hom w
        = γ x (hint x hx) := by
    intro x hx
    have hsubx : C₀ᶜ ⊆ ({x} : Set M)ᶜ :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
    have hfac : Work.Orient.resRelH (TopCat.of M) (n + 1)
          (Set.singleton_subset_iff.mpr hx) (φ.hom w)
        = (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x (hint x hx))
            (n + 1)).hom w := by
      have hfac' : Work.Orient.relPunct (TopCat.of M)
            ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x (hint x hx)
          = Work.Orient.relChainsIncl (TopCat.of M)
              (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) hbc
            ≫ Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx := by
        rw [Work.Orient.relPunct_eq_relChainsIncl]
        rw [← Work.Orient.relChainsIncl_eq_relCokerMap (TopCat.of M) hsubx]
        rw [Work.Orient.relChainsIncl_trans (TopCat.of M) hbc hsubx]
      have hcomp := HomologicalComplex.homologyMap_comp
        (Work.Orient.relChainsIncl (TopCat.of M)
          (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := C₀ᶜ) hbc)
        (Work.Cohomology.relCokerMap (TopCat.of M) C₀ᶜ ({x} : Set M)ᶜ hsubx) (n + 1)
      rw [hfac', hcomp, ModuleCat.comp_apply]
      rfl
    rw [hw] at hfac
    exact hfac.symm.trans (hu₀ x hx)
  -- the exact statement spreads from the core to the whole interior
  have hloc : ∀ (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) x hx) (n + 1)).hom w
        = γ x hx :=
    relPunct_locClass_eq_of_core_local (C₀ := C₀) hint hconn w γ
      (localWitnesses_of_halfOrientationFamily_local γ hγ) hcore
  refine ⟨w, ?_, hloc⟩
  intro x hx
  rw [hloc x hx]
  exact hγ.1 x hx

end

end Work.ThomBordism
