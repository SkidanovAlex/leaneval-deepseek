import Mathlib
import Submission.MobiusModel
import Submission.SecantModel
import Submission.Pi1Mobius
import Submission.OpenMobiusHomotopy

open unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Layer C: embedded circles in the open Möbius band — winding classification

**Context.**  `OpenMobius` (the interior of the Möbius band of knot secants,
`Submission/SecantSpace.lean`) is homeomorphic to the chord model
`MobiusModel` (`openMobiusModelHomeo`, `Submission/SecantModel.lean`), whose
core circle is `range mobiusCore` (the diameters); the deformation
retraction `openMobiusCoreRetract` and the homotopy equivalence
`openMobius_homotopyEquiv_core` (OpenMobiusHomotopy.lean) give
`π₁(OpenMobius) ≅ ℤ` (`pi1_openMobius_eq_int`, `Submission/Pi1OpenMobius.lean`).

**This module: the embedded-circle topology.**  In the plane of the Möbius
band, an *embedded circle* (`IsSimpleClosedCurve`) is either *separating*
(its complement is disconnected) or *non-separating* (`IsNonSeparating`).
The classification (to be completed in later passes, following Kuperberg
§1–3 and Denne):

  (1) **base case (proved here, model side)**: the *core circle* of the
      Möbius band does not separate it — its complement is path connected
      (indeed an annulus): `model_core_complement_isPathConnected` (built by
      parametrising the off-core chords by the annulus
      `Circle × (0,1)` — each chord with a chosen normal and positive
      offset — via `offCoreOfPos`, continuous and surjective);
  (2) an embedded circle whose homotopy class is trivial (in π₁(OpenMobius)
      = ℤ it is `0`) bounds a disk and in particular separates an annulus
      from the band — *to be proved*;
  (3) an embedded circle *essential* in `π₁ ≅ ℤ` winds either once around
      the band (generator, non-separating — isotopic to the core) or twice
      (orientation-preserving, separating an annulus) — *to be proved*;
  (4) these feed the obstruction lemma: a circle that meets every
      non-separating proper arc is essential; and the trisecant-locus
      components (`O`) give such circles, whose winding forces the
      Kuperberg contradiction.

Statements (2)–(4) need the surface-topology vocabulary (proper arcs,
separating vs non-separating, embedded circle isotopy) that this module
begins to lay out.
-/

/-! ## Vocabulary: simple closed curves and separation -/

/-- An *embedded circle* (simple closed curve) in a space `X`: a closed set
which is the image of an injective continuous map from the circle.  (For a
Hausdorff `X` and compact domain this is automatically a closed embedding,
e.g. by `Continuous.embedding_of_injective_on`-type results.) -/
def IsSimpleClosedCurve {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  ∃ f : Circle → X, Function.Injective f ∧ Continuous f ∧ K = Set.range f

/-- A circle does not separate `X` if its complement is connected. -/
def IsNonSeparating {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  IsConnected (Kᶜ : Set X)

/-- A circle separates `X` if its complement is not connected. -/
def IsSeparating {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  ¬ IsConnected (Kᶜ : Set X)

/-! ## The model core circle is non-separating -/

/-- Membership of a chord class in the core circle iff the (any) offset is
`0`. -/
lemma mobiusMk_mem_core_iff_offset_zero (q : ChordData) :
    (∃ n : Circle, (⟦q⟧ : MobiusModel) = mobiusCore n) ↔ q.1.2 = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    have hrel := (mobiusMk_eq_iff q (coreChord n)).mp hn
    rcases hrel with h | h
    · have hq := congrArg (fun c : ChordData => c.1.2) h
      simpa [coreChord] using hq
    · have hq := congrArg (fun c : ChordData => c.1.2) h
      simp [chordFlip, chordDataFlip] at hq
      exact hq
  · intro h0
    refine ⟨q.1.1, ?_⟩
    apply Quotient.sound
    left
    apply Subtype.ext
    ext
    · rfl
    · simpa [coreChord] using h0

/-- The model Möbius band with the core circle removed (open annulus). -/
abbrev OffCore := {c : MobiusModel // c ∉ Set.range mobiusCore}

/-- Positive-offset chord data from an annulus coordinate. -/
def chordOfPos (z : Circle × Set.Ioo (0 : ℝ) 1) : ChordData :=
  ⟨(z.1, (z.2 : ℝ)), by
    have hz1 : 0 < (z.2 : ℝ) := z.2.property.1
    have hz2 : (z.2 : ℝ) < 1 := z.2.property.2
    constructor <;> nlinarith⟩

lemma chordOfPos_offset_pos (z : Circle × Set.Ioo (0 : ℝ) 1) : 0 < (chordOfPos z).1.2 := by
  exact z.2.property.1

/-- A positive-offset chord is not on the core. -/
lemma chordOfPos_not_core (z : Circle × Set.Ioo (0 : ℝ) 1) :
    (⟦chordOfPos z⟧ : MobiusModel) ∉ Set.range mobiusCore := by
  intro h
  rcases h with ⟨n, hn⟩
  have hz := (mobiusMk_mem_core_iff_offset_zero (chordOfPos z)).mp ⟨n, hn.symm⟩
  have hpos : 0 < (chordOfPos z).1.2 := chordOfPos_offset_pos z
  linarith

/-- The annulus parametrises the off-core chords: `(n, δ) ↦` the chord with
normal `n` and positive offset `δ`. -/
noncomputable def offCoreOfPos (z : Circle × Set.Ioo (0 : ℝ) 1) : OffCore :=
  ⟨mobiusMk (chordOfPos z), chordOfPos_not_core z⟩

lemma continuous_chordOfPos : Continuous chordOfPos := by
  apply Continuous.subtype_mk
  · have hn : Continuous (fun z : Circle × Set.Ioo (0 : ℝ) 1 => (z.1 : Circle)) := continuous_fst
    have hd : Continuous (fun z : Circle × Set.Ioo (0 : ℝ) 1 => (z.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact hn.prodMk hd

lemma continuous_offCoreOfPos : Continuous offCoreOfPos := by
  apply Continuous.subtype_mk
  · exact continuous_mobiusMk.comp continuous_chordOfPos

/-- The open interval `(0,1)` is path connected (straight-line paths,
convexity of the open interval). -/
instance intervalPathConnected : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) where
  nonempty := ⟨⟨(1 / 2 : ℝ), by norm_num⟩⟩
  joined x y := by
    refine ⟨⟨⟨fun t : I => ⟨AffineMap.lineMap (x : ℝ) (y : ℝ) (t : ℝ),
        (convex_Ioo (0 : ℝ) 1).segment_subset x.2 y.2 (lineMap_mem_segment (𝕜 := ℝ) (x : ℝ) (y : ℝ) t.2)⟩, by
      refine Continuous.subtype_mk ?_ ?_
      · fun_prop⟩,
      by ext; simp [AffineMap.lineMap], by ext; simp [AffineMap.lineMap]⟩⟩

/-- Positive representative of a negative offset. -/
lemma pos_neg_d {d : ℝ} (hd : d ∈ Set.Ioo (-1) 1) (h : d < 0) : -d ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> nlinarith [hd.1, hd.2, h]

/-- The annulus surjects onto the off-core chords: every off-core chord has
a positive-offset representative (flip the normal if the offset is
negative). -/
lemma offCoreOfPos_surjective : Function.Surjective offCoreOfPos := by
  intro c
  let q : ChordData := Quotient.out c.1
  have hq : (⟦q⟧ : MobiusModel) = c.1 := Quotient.out_eq c.1
  have hoff : q.1.2 ≠ 0 := by
    intro hz
    apply c.2
    have hmem : ∃ n : Circle, (⟦q⟧ : MobiusModel) = mobiusCore n :=
      (mobiusMk_mem_core_iff_offset_zero q).mpr hz
    rcases hmem with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hq]
    exact hn.symm
  rcases lt_or_gt_of_ne hoff with hneg | hpos
  · let z : Circle × Set.Ioo (0 : ℝ) 1 := (-q.1.1, ⟨-q.1.2, pos_neg_d q.2 hneg⟩)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (⟦chordOfPos z⟧ : MobiusModel) = c.1
    have hflip : (⟦chordOfPos z⟧ : MobiusModel) = (⟦q⟧ : MobiusModel) := by
      apply Quotient.sound
      right
      apply Subtype.ext
      ext <;> simp [z, chordOfPos, chordFlip, chordDataFlip]
    rw [hflip, hq]
  · let z : Circle × Set.Ioo (0 : ℝ) 1 := (q.1.1, ⟨q.1.2, by
      have hd1 : -1 < q.1.2 := q.2.1
      have hd2 : q.1.2 < 1 := q.2.2
      constructor <;> nlinarith⟩)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (⟦chordOfPos z⟧ : MobiusModel) = c.1
    have hrfl : (⟦chordOfPos z⟧ : MobiusModel) = (⟦q⟧ : MobiusModel) := by
      rfl
    rw [hrfl, hq]

/-- The off-core chords form a path connected space (the open annulus): they
are the continuous image of the annulus `Circle × (0,1)`. -/
instance : PathConnectedSpace OffCore := by
  exact Function.Surjective.pathConnectedSpace offCoreOfPos_surjective continuous_offCoreOfPos

/-- **Base case (model side)**: the complement of the core circle in the
model Möbius band is path connected — the core does not separate the Möbius
band. -/
lemma model_core_complement_isPathConnected :
    IsPathConnected ((Set.range mobiusCore)ᶜ : Set MobiusModel) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact (inferInstance : PathConnectedSpace OffCore)

/-- The complement of the core circle is connected. -/
lemma model_core_complement_isConnected :
    IsConnected ((Set.range mobiusCore)ᶜ : Set MobiusModel) :=
  IsPathConnected.isConnected model_core_complement_isPathConnected

/-- **The core circle is non-separating in the model Möbius band.** -/
lemma model_core_circle_nonSeparating : IsNonSeparating (Set.range mobiusCore) := by
  unfold IsNonSeparating
  exact model_core_complement_isConnected

/-! ## The non-separating core in the open Möbius band

The model statement transports to `OpenMobius` through the homeomorphism
`openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel`: the homeomorphism maps
the core circle `range coreFactor` (antipodal pairs) onto the model core
`range mobiusCore` (`forwardModel_mem_mobiusCore_iff_mem_core`, built from
`forwardModel_coreFactor_mem_mobiusCore` and
`backwardModel_mobiusCore_mem_core`), so it restricts to a homeomorphism of
the complements

    openMobiusOffCoreEquiv : OpenMobiusOffCore ≃ₜ OffCore

(the requested bridge lemma).  Path-connectedness of `OffCore`
(`PathConnectedSpace OffCore` above) is therefore transported back, giving
`openMobius_core_complement_isPathConnected` and hence
**`openMobius_core_circle_nonSeparating`** — the core circle does not
separate the open Möbius band of knot secants.
-/

/-- The forward image of a core point of the open Möbius band (parameterised
by the half-period circle) is a model-core point (diameter). -/
lemma forwardModel_coreFactor_mem_mobiusCore (x : AddCircle halfPeriod) :
    forwardModel (coreFactor x) ∈ Set.range mobiusCore := by
  have hrange : coreFactor x ∈ Set.range core := by
    rw [← coreFactor_range_eq_core_range]
    exact ⟨x, rfl⟩
  rcases hrange with ⟨t, ht⟩
  rw [← ht]
  exact forwardModel_core_mem_mobiusCore t

/-- Under the homeomorphism `openMobiusModelHomeo` the core circle of
`OpenMobius` corresponds exactly to the core circle of the model: `c` is an
antipodal pair iff its chord data is a diameter. -/
lemma forwardModel_mem_mobiusCore_iff_mem_core (c : OpenMobius) :
    forwardModel c ∈ Set.range mobiusCore ↔ c ∈ Set.range coreFactor := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have hc : backwardModel (mobiusCore n) = c := by
      rw [hn]
      exact openMobiusModelEquiv.left_inv c
    rcases backwardModel_mobiusCore_mem_core n with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx]
    exact hc
  · intro h
    rcases h with ⟨x, rfl⟩
    exact forwardModel_coreFactor_mem_mobiusCore x

/-- The complement of the core circle in the open Möbius band. -/
abbrev OpenMobiusOffCore := {c : OpenMobius // c ∉ Set.range coreFactor}

/-- **Bridge lemma**: the complement of the core circle in `OpenMobius` is
homeomorphic to the complement of the model core circle (the restriction of
`openMobiusModelHomeo`). -/
noncomputable def openMobiusOffCoreEquiv : OpenMobiusOffCore ≃ₜ OffCore where
  toFun c := ⟨openMobiusModelHomeo c.1, by
    change forwardModel c.1 ∉ Set.range mobiusCore
    exact (Iff.not (forwardModel_mem_mobiusCore_iff_mem_core c.1)).mpr c.2⟩
  invFun m := ⟨openMobiusModelHomeo.symm m.1, by
    intro hm
    apply m.2
    rcases (forwardModel_mem_mobiusCore_iff_mem_core (openMobiusModelHomeo.symm m.1)).mpr hm with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc mobiusCore n = forwardModel (openMobiusModelHomeo.symm m.1) := hn
      _ = m.1 := openMobiusModelHomeo.apply_symm_apply m.1⟩
  left_inv := by
    intro c
    apply Subtype.ext
    change openMobiusModelHomeo.symm (openMobiusModelHomeo c.1) = c.1
    exact openMobiusModelHomeo.symm_apply_apply c.1
  right_inv := by
    intro m
    apply Subtype.ext
    change openMobiusModelHomeo (openMobiusModelHomeo.symm m.1) = m.1
    exact openMobiusModelHomeo.apply_symm_apply m.1
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ ?_
    · exact openMobiusModelHomeo.continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ ?_
    · exact openMobiusModelHomeo.symm.continuous.comp continuous_subtype_val

/-- The complement of the core circle in the open Möbius band is path
connected (transported from the annulus `OffCore` along the bridge
homeomorphism). -/
instance : PathConnectedSpace OpenMobiusOffCore :=
  openMobiusOffCoreEquiv.symm.surjective.pathConnectedSpace openMobiusOffCoreEquiv.symm.continuous

/-- The complement of the core circle in `OpenMobius` is path connected:
the core circle does not separate the open Möbius band. -/
lemma openMobius_core_complement_isPathConnected :
    IsPathConnected ((Set.range coreFactor)ᶜ : Set OpenMobius) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact (inferInstance : PathConnectedSpace OpenMobiusOffCore)

/-- The complement of the core circle in `OpenMobius` is connected. -/
lemma openMobius_core_complement_isConnected :
    IsConnected ((Set.range coreFactor)ᶜ : Set OpenMobius) :=
  IsPathConnected.isConnected openMobius_core_complement_isPathConnected

/-- **The core circle (antipodal pairs) does not separate the open Möbius
band of knot secants** — the `OpenMobius`-side companion of
`model_core_circle_nonSeparating`. -/
lemma openMobius_core_circle_nonSeparating : IsNonSeparating (Set.range coreFactor) := by
  unfold IsNonSeparating
  exact openMobius_core_complement_isConnected

/-! ## The essential/trivial dichotomy for embedded circles (statement)

An embedded circle in the open Möbius band `OpenMobius` is *essential* when
its parametrisation is not null-homotopic; equivalently its class in
`π₁(OpenMobius) ≅ ℤ` (`pi1_openMobius_eq_int`) is non-zero.  The dichotomy
to be established:

  (b) *trivial ⇒ bounds a disk*:  a null-homotopic embedded circle is the
      boundary of an embedded closed disk (`BoundsADisk` — an embedded copy
      of the closed unit disk in `ℝ²` with the circle as its frontier);
  (c) *essential ⇒ winds once or twice*:  an essential embedded circle is
      homotopic (as an embedded circle) either to the core circle
      (`range coreFactor`, winding number one — non-separating, proved
      above) or to a circle winding twice around the band (separating an
      annulus).

The statements are formalised below as `SimpleClosedCurve`, `image`,
`IsNullHomotopic`/`IsEssential`, and `BoundsADisk`, together with the
**target proposition** `TrivialCircleBoundsDisk_OpenMobius` (documented;
its proof requires embedded-surface / Jordan–Schoenflies-class results
which Mathlib does not currently provide, plus the degree/winding theory of
maps `Circle → OpenMobius` — this is the Layer C long pole).  The first
elementary consequences are proved: the image of an embedded circle is
compact (`image_isCompact`) and — in a Hausdorff space — closed
(`image_isClosed`).
-/

/-- The model closed 2-disk (the unit disk in `ℝ²`). -/
abbrev ModelDisk := {p : EuclideanSpace ℝ (Fin 2) // ‖p‖ ≤ 1}

/-- The boundary circle of the model closed disk. -/
def modelBoundary : Set ModelDisk := {p : ModelDisk | ‖(p : EuclideanSpace ℝ (Fin 2))‖ = 1}

/-- A set `K` *bounds a disk* if it is the image of the boundary of an
embedded closed unit disk (a closed embedding of `ModelDisk` whose boundary
maps onto `K`). -/
def BoundsADisk {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  ∃ φ : C(ModelDisk, X), Topology.IsClosedEmbedding (φ : ModelDisk → X) ∧ K = φ '' modelBoundary

/-- Null-homotopy of a map from the circle: homotopic to a constant map. -/
def NullHomotopic {X : Type*} [TopologicalSpace X] (γ : C(Circle, X)) : Prop :=
  ∃ c : X, ContinuousMap.Homotopic γ (ContinuousMap.const Circle c)

/-- An embedded circle in `X`: an injective continuous map from `Circle`
(the image is a simple closed curve). -/
structure SimpleClosedCurve (X : Type*) [TopologicalSpace X] where
  toCircleMap : C(Circle, X)
  injective' : Function.Injective toCircleMap

namespace SimpleClosedCurve

variable {X : Type*} [TopologicalSpace X]

/-- The image (the actual simple closed curve). -/
def image (c : SimpleClosedCurve X) : Set X := Set.range c.toCircleMap

/-- The embedded circle is null-homotopic if its parametrisation is. -/
def IsNullHomotopic (c : SimpleClosedCurve X) : Prop := NullHomotopic c.toCircleMap

/-- The embedded circle is *essential* if it is not null-homotopic. -/
def IsEssential (c : SimpleClosedCurve X) : Prop := ¬ IsNullHomotopic c

/-- The image of an embedded circle is compact. -/
lemma image_isCompact (c : SimpleClosedCurve X) : IsCompact (image c) := by
  unfold image
  exact isCompact_range c.toCircleMap.continuous

/-- In a Hausdorff space the image of an embedded circle is closed (it is a
compact subset; the image of the compact circle in `OpenMobius`). -/
lemma image_isClosed [T2Space X] (c : SimpleClosedCurve X) : IsClosed (image c) := by
  exact (image_isCompact c).isClosed

end SimpleClosedCurve

/-- **Target (b), documented**: a null-homotopic embedded circle in the open
Möbius band bounds an embedded disk.

(Proof pending: needs the embedded-surface dichotomy — trivial embedded
circles bound disks — i.e. a Jordan–Schoenflies-class statement for the
Möbius band, plus the reduction of null-homotopy to the core circle through
`openMobius_homotopyEquiv_core`.) -/
def TrivialCircleBoundsDisk_OpenMobius : Prop :=
  ∀ c : SimpleClosedCurve OpenMobius, c.IsNullHomotopic → BoundsADisk c.image

/-! ## The reduction: null-homotopy transfers to the core circle

If an embedded circle `γ` in `OpenMobius` is null-homotopic then, through
the homotopy-equivalence map of `openMobius_homotopyEquiv_core`, its image
in the core circle is null-homotopic as well.  (Generic form first, then
the `OpenMobius` instance.)  This is the map whose kernel/degree analysis
will eventually show the trivial side of the dichotomy bounds a disk. -/

/-- Generic: composing a null-homotopic circle map with a continuous map
gives a null-homotopic circle map. -/
lemma nullHomotopic_of_nullHomotopic_comp {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (k : C(X, Y)) {γ : C(Circle, X)}
    (h : NullHomotopic γ) : NullHomotopic (k.comp γ) := by
  rcases h with ⟨c, H⟩
  rcases H with ⟨Hγ⟩
  let Hk : ContinuousMap.Homotopy (k.comp γ)
      (k.comp (ContinuousMap.const Circle c)) :=
    (ContinuousMap.Homotopy.refl k).comp Hγ
  have hconst : k.comp (ContinuousMap.const Circle c) =
      ContinuousMap.const Circle (k c) := by
    ext x
    rfl
  refine ⟨k c, ?_⟩
  exact ⟨by simpa [hconst] using Hk⟩

/-- The transfer instance for `OpenMobius`: null-homotopy of an embedded
circle in `OpenMobius` implies null-homotopy of its image in the core
circle (through the homotopy-equivalence map of
`openMobius_homotopyEquiv_core`). -/
lemma openMobius_core_nullHomotopic_loop (γ : SimpleClosedCurve OpenMobius)
    (hγ : γ.IsNullHomotopic) :
    NullHomotopic ((Classical.choice openMobius_homotopyEquiv_core).toFun.comp γ.toCircleMap) := by
  exact nullHomotopic_of_nullHomotopic_comp
    ((Classical.choice openMobius_homotopyEquiv_core).toFun) hγ

end LeanEval.KnotTheory.Quadrisecant

