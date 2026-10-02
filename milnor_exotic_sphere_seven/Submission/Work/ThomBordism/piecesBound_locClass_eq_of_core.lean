import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.IsRelFundClassOfCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local class of a relative class is determined by its values on a core

`Work.ThomBordism.piecesBound_locClass_eq_of_core`: let `W` be a compact `T2` space charted in the
half-space model `𝓡∂ 9`, `C₀ ⊆ W` a set of **interior** points meeting every path component of the
interior `W° = W ∖ ∂W` (the connectivity hypothesis `hC₀conn`), `z ∈ H₉(W, ∂W)` a relative class,
and `Φ` a family of local classes at the interior points which *locally* comes from one relative
class over an open neighbourhood (`hΦ`).  If the local class of `z` agrees with `Φ` at every point
of `C₀` (`hcore`), then it agrees with `Φ` at **every** interior point.

This is the local constancy of the comparison between the "local system" of `z` and the one given by
`Φ`, in the form needed by the boundary-orientation chapter: the hypotheses on `Φ` are purely local
consistency conditions (no generator/span condition), so this is exactly the statement that a class
of `H₉(W, ∂W)` is determined by its restriction over a compact core of the interior, applied to the
difference of `z` and of a class realising `Φ`.

## The proof

Fix a point `p` of the interior and the witness `(U, a)` of `hΦ` at `p`, and let
`K = halfBallPiece 9 X p r ⊆ U ∩ W°` be a coordinate half-ball around `p` contained in the interior
of the witness neighbourhood.  Two facts turn the comparison into a *single* linear condition on
`H₉(W, W∖K)`:

* the local class of `z` at a point `y ∈ K` is the image under the restriction
  `H₉(W, W∖K) ⟶ H₉(W, W∖{y})` of the class `u = z|_K` (`resRelH_relChainsIncl_eq_…`);
* the local class `Φ y` is, by the definition of `a` and functoriality of the restrictions, the
  image of the class `a|_K` under the same map.

Therefore `Φ y` agrees with the local class of `z` at `y` iff the class `w = u - a|_K ∈ H₉(W, W∖K)`
dies at `y`.  Since `K` consists of interior points, the localisation `H₉(W, W∖K) ⟶ H₉(W, W∖{y})` is
*injective* (`Work.Orient.Boundary.HalfRestrictIsoAtPoint`), so "dies at `y`" is independent of
`y ∈ K`: this is the local constancy.  The set where the comparison holds is thus clopen in the
interior, and the connectivity hypothesis finishes with the usual preconnectedness of `[0,1]`.
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

/-! ## Bridges between the `Work.ThomBordism` and the `Work.Orient` copies of `relChainsIncl` -/

/-- `relChainsIncl` depends on the inclusion only through its truth. -/
theorem td_relChainsIncl_congr (X : TopCat) {A B : Set X} (h h' : A ⊆ B) :
    relChainsIncl X h = relChainsIncl X h' :=
  Work.Orient.Boundary.relChainsIncl_congr_h h h'

/-- Functoriality of `relChainsIncl`. -/
theorem td_relChainsIncl_trans (X : TopCat) {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    relChainsIncl X h₁ ≫ relChainsIncl X h₂ = relChainsIncl X (h₁.trans h₂) :=
  Work.Orient.relChainsIncl_trans X h₁ h₂

/-- **`resRelH` is the homology of `relChainsIncl`** (the `Work.ThomBordism` spelling). -/
theorem resRelH_eq_homologyMap_relChainsIncl' (M : TopCat) (n : ℕ) {A B : Set M} (h : A ⊆ B) :
    Work.Orient.resRelH M n h
      = (HomologicalComplex.homologyMap (relChainsIncl M
          (Set.compl_subset_compl.mpr h)) n).hom := by
  rw [Work.Orient.resRelH_eq_homologyMap_relChainsIncl]
  rfl

/-! ## The two comparisons over a coordinate half-ball -/

/-- **The local class of `z` at `y ∈ K`, computed on `H_9(W, W∖K)`.**

If `K` is disjoint from `B`, `y ∈ K`, `y ∉ B` and `u` is the restriction of `z ∈ H_9(W, B)` to
`H_9(W, W∖K)` along an inclusion `B ⊆ Kᶜ`, then the restriction of `u` to the local group at `y` is
the local class of `z` at `y`. -/
theorem resRelH_relChainsIncl_eq_relChainsInclPunct
    (X : TopCat) {B K : Set X} (hBK : B ⊆ Kᶜ) {y : X} (hyK : y ∈ K) (hy : y ∉ B)
    (z : (Work.Cohomology.relChains X B).homology 9) :
    Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK)
        ((HomologicalComplex.homologyMap (relChainsIncl X hBK) 9).hom z)
      = (HomologicalComplex.homologyMap
          (relChainsInclPunct X B y hy) 9).hom z := by
  have h2 : Kᶜ ⊆ ({y} : Set X)ᶜ := Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyK)
  rw [resRelH_eq_homologyMap_relChainsIncl' X 9 (Set.singleton_subset_iff.mpr hyK)]
  rw [← ModuleCat.comp_apply]
  rw [← HomologicalComplex.homologyMap_comp]
  have hcongr : (relChainsIncl X hBK ≫ relChainsIncl X h2)
      = relChainsIncl X (A := B) (B := {a : X | a ≠ y})
          (fun a ha hax => hy (hax ▸ ha)) := by
    rw [td_relChainsIncl_trans]
  rw [hcongr]
  rfl

/-- **Agreement over a coordinate half-ball is a single linear condition.**

Let `a ∈ H_9(W, W∖U)` be a class whose localisations on the open set `U` are the family `Φ`, let
`z ∈ H_9(W, B)`, and let `K ⊆ U ∩ Bᶜ` be a set over which the localisation to a point of `K` is
**injective** (this holds for a coordinate half-ball of interior points, by
`Work.Orient.Boundary.HalfRestrictIsoAtPoint`).  Then `Φ x` and the local class of `z` agree at one
point `x ∈ K` if and only if they agree at another point `y ∈ K`.

The proof: let `u = z|_K`, `aK = a|_K` and `w = u - aK`.  For every `v ∈ K`, the localisation of `w`
at `v` is the difference of the local classes of `z` and `Φ` at `v`; hence the comparison at `v` is
equivalent to `w` dying at `v`, which by injectivity is the same condition for all `v ∈ K`. -/
theorem agreement_iff_of_injective
    (X : TopCat) {B K U : Set X} (hBK : B ⊆ Kᶜ) (hKU : K ⊆ U)
    (hinj : ∀ y (hyK : y ∈ K),
      Function.Injective (Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK)))
    (a : Work.Orient.RelH X 9 U) (Φ : ∀ x : X, x ∉ B → Work.Orient.LocH X 9 x)
    (ha : ∀ y (hyU : y ∈ U) (hy : y ∉ B),
      Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyU) a = Φ y hy)
    (z : (Work.Cohomology.relChains X B).homology 9)
    {x y : X} (hxK : x ∈ K) (hyK : y ∈ K) (hx : x ∉ B) (hy : y ∉ B) :
    (HomologicalComplex.homologyMap (relChainsInclPunct X B x hx) 9).hom z = Φ x hx
      ↔ (HomologicalComplex.homologyMap (relChainsInclPunct X B y hy) 9).hom z = Φ y hy := by
  let u : Work.Orient.RelH X 9 K :=
    (HomologicalComplex.homologyMap (relChainsIncl X hBK) 9).hom z
  let aK : Work.Orient.RelH X 9 K := Work.Orient.resRelH X 9 hKU a
  let w : Work.Orient.RelH X 9 K := u - aK
  have hw : ∀ (y : X) (hyK : y ∈ K) (hy : y ∉ B),
      Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) w = 0
        ↔ (HomologicalComplex.homologyMap (relChainsInclPunct X B y hy) 9).hom z = Φ y hy := by
    intro y hyK hy
    have h1 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) w
        = Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) u
          - Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) aK := by
      simp only [w, map_sub]
    have h2 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) u
        = (HomologicalComplex.homologyMap
            (relChainsInclPunct X B y hy) 9).hom z :=
      resRelH_relChainsIncl_eq_relChainsInclPunct X hBK hyK hy z
    have h3 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) aK = Φ y hy := by
      simp only [aK]
      exact (LinearMap.congr_fun (Work.Orient.Port.RelHmap_comp' X 9
        (Set.singleton_subset_iff.mpr hyK) hKU
        (Set.singleton_subset_iff.mpr (hKU hyK))) a).trans (ha y (hKU hyK) hy)
    rw [h1, h2, h3]
    exact sub_eq_zero
  constructor
  · intro h
    have h0 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hxK) w = 0 :=
      (hw x hxK hx).mpr h
    have h0' : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hxK) w
        = Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hxK) 0 := by
      rw [map_zero, h0]
    have hw0 : w = 0 := hinj x hxK h0'
    have h1 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) w = 0 := by
      rw [hw0, map_zero]
    exact (hw y hyK hy).mp h1
  · intro h
    have h0 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) w = 0 :=
      (hw y hyK hy).mpr h
    have h0' : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) w
        = Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK) 0 := by
      rw [map_zero, h0]
    have hw0 : w = 0 := hinj y hyK h0'
    have h1 : Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hxK) w = 0 := by
      rw [hw0, map_zero]
    exact (hw x hxK hx).mp h1

/-- **The localisation out of an interior coordinate half-ball is injective**, at every one of its
points.  This is `Work.Orient.Boundary.HalfRestrictIsoAtPoint` (which is stated at a point of the
piece) in the form needed below. -/
theorem injective_resRelH_halfBallPiece
    (X : TopCat) [CompactSpace X] [T2Space X] [ChartedSpace (EuclideanHalfSpace 9) X]
    (z0 : X) (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood 9 X z0 r)
    (hint : ∀ y ∈ Work.Orient.halfBallPiece 9 X z0 r,
      y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X)
    (y : X) (hy : y ∈ Work.Orient.halfBallPiece 9 X z0 r) :
    Function.Injective (Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hy)) := by
  have h := Work.Orient.Boundary.HalfRestrictIsoAtPoint 8 X z0 r hr hgood hint y hy
  exact (ConcreteCategory.isIso_iff_bijective _).mp h |>.1

/-! ## The main theorem -/

/-- **The local class agreement spreads from a core.**  The general form of
`Work.ThomBordism.piecesBound_locClass_eq_of_core` for an arbitrary bundled space `X`. -/
theorem piecesBound_locClass_core_aux
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ChartedSpace (EuclideanHalfSpace 9) X]
    (C₀ : Set X)
    (hC₀int : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X)
    (hC₀conn : ∀ (x : X) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X),
      ∃ (y : X) (hy : y ∈ C₀) (hy' : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X),
        Nonempty (Path (⟨x, hx⟩ : {z : X // z ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X})
          ⟨y, hy'⟩))
    (z : (Work.Cohomology.relChains X
      ((modelWithCornersEuclideanHalfSpace 9).boundary X)).homology 9)
    (Φ : ∀ x : X, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X →
      Work.Orient.LocH X 9 x)
    (hΦ : ∀ x : X, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X →
      ∃ U : Set X, x ∈ U ∧
        U ⊆ {y : X | y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X} ∧
        IsOpen U ∧ ∃ a : Work.Orient.RelH X 9 U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X),
            Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyU) a = Φ y hy)
    (hcore : ∀ (x : X) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (relChainsInclPunct X
        ((modelWithCornersEuclideanHalfSpace 9).boundary X) x (hC₀int x hx)) 9).hom z
        = Φ x (hC₀int x hx)) :
    ∀ (x : X) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary X),
      (HomologicalComplex.homologyMap (relChainsInclPunct X
        ((modelWithCornersEuclideanHalfSpace 9).boundary X) x hx) 9).hom z = Φ x hx := by
  classical
  let B : Set X := (modelWithCornersEuclideanHalfSpace 9).boundary X
  let P : {z : X // z ∉ B} → Prop := fun p =>
    (HomologicalComplex.homologyMap (relChainsInclPunct X B p.1 p.2) 9).hom z = Φ p.1 p.2
  -- `P` is locally constant on the interior
  have key : ∀ p : {z : X // z ∉ B}, ∃ V ∈ 𝓝 p, ∀ q ∈ V, (P q ↔ P p) := by
    intro p
    obtain ⟨U, hpU, hUint, hUopen, a, ha⟩ := hΦ p.1 p.2
    have hBclosed : IsClosed B := Work.Orient.Boundary.isClosed_boundary_halfSpace 8 X
    have hxU : p.1 ∈ U ∩ Bᶜ := ⟨hpU, p.2⟩
    obtain ⟨r, hr, hgood, hsub⟩ :=
      Work.Orient.Boundary.exists_halfBall_subset 8 (W := X)
        (hUopen.inter hBclosed.isOpen_compl) hxU
    refine ⟨Subtype.val ⁻¹' (Work.Orient.halfBallPiece 9 X p.1 r), ?_, ?_⟩
    · exact (continuous_subtype_val.continuousAt).preimage_mem_nhds
        (Work.Orient.Boundary.halfBallPiece_mem_nhds (n := 8) (W := X) hr)
    · intro q hq
      have hBK : B ⊆ (Work.Orient.halfBallPiece 9 X p.1 r)ᶜ :=
        fun y hy hyK => (hsub hyK).2 hy
      have hKU : Work.Orient.halfBallPiece 9 X p.1 r ⊆ U := fun y hy => (hsub hy).1
      have hinj : ∀ y (hyK : y ∈ Work.Orient.halfBallPiece 9 X p.1 r),
          Function.Injective (Work.Orient.resRelH X 9 (Set.singleton_subset_iff.mpr hyK)) :=
        fun y hyK => injective_resRelH_halfBallPiece X p.1 r hr hgood
          (fun y hy => (hsub hy).2) y hyK
      exact agreement_iff_of_injective X hBK hKU hinj a Φ ha z hq
        (Work.Orient.mem_halfBallPiece_center hr) q.2 p.2
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

/-- **The local class of a relative class is determined by its values on a core.**

`Work.ThomBordism.piecesBound_locClass_eq_of_core`: this is
`Work.ThomBordism.piecesBound_locClass_core_aux` for `X = TopCat.of W`. -/
theorem piecesBound_locClass_eq_of_core
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    {C₀ : Set W} (hC₀int : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W)
    (hC₀conn : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      ∃ (y : W) (hy : y ∈ C₀) (hy' : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        Nonempty (Path (⟨x, hx⟩ : {z : W // z ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W})
          ⟨y, hy'⟩))
    (z : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9)
    (Φ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      Work.Orient.LocH (TopCat.of W) 9 x)
    (hΦ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      ∃ U : Set W, x ∈ U ∧ U ⊆ {y : W | y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W} ∧
        IsOpen U ∧ ∃ a : Work.Orient.RelH (TopCat.of W) 9 U,
          ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
            Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyU) a = Φ y hy)
    (hcore : ∀ (x : W) (hx : x ∈ C₀),
      (HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) x (hC₀int x hx)) 9).hom z
        = Φ x (hC₀int x hx)) :
    ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      (HomologicalComplex.homologyMap (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom z = Φ x hx :=
  piecesBound_locClass_core_aux (TopCat.of W) C₀ hC₀int hC₀conn z Φ hΦ hcore

end

end Work.ThomBordism
