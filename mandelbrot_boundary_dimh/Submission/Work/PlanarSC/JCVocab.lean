import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Jordan.at_most_one_bounded_component
import Submission.Lib.Unif2.Commons.Topology.Jordan.at_most_two_components
import Submission.Lib.Unif2.Commons.Topology.Jordan.frontier_connectedComponentIn_subset
import Submission.Lib.Unif2.Commons.Topology.Plane.polyomino_deformationRetract_oneDim

/-!
# Vocabulary and assembly for the Jordan criterion of simple connectivity

This module holds the vocabulary of the proof of `Work.PlanarSC.jordan_criterion_simplyConnected`
(`jordanRegion`, dyadic grid edges and grid loops) and the *assembly* lemmas that combine the three
delegated pieces into the target theorem.  The target theorem itself is proved in
`Submission/Work/PlanarSC/jordan_criterion_simplyConnected.lean`, which imports this module.

Mathematically this is the "no holes" direction of the classical criterion for plane domains
(`SimplyConnectedSpace V ↔ every component of Vᶜ is unbounded`): `hJ` says that `V` contains the
closed region of every Jordan curve inside it, which is the strong form of "no holes".

The proof is assembled from the pieces listed in `NOTES_JCS.md`:
`loop_homotopic_to_gridWalk` (approximation), `gridLoop_nullhomotopic_of_cycles` (decomposition of a
closed walk into simple cycles) and `jordanRegion_nullhomotopic` (a Jordan curve is null-homotopic
in the closed region it bounds, via the dyadic-polyomino collapse of
`Commons.Topology.Plane.polyomino_deformationRetract_oneDim`).

This module defines the vocabulary (`jordanRegion`) and the elementary reductions.
-/

open Set

namespace Work.PlanarSC

/-- **The closed region bounded by a Jordan curve**: the range of `γ` together with all points whose
connected component in the complement of the range of `γ` is bounded.

For an injective `γ` this is the closed region that `γ` bounds: `range γ ∪ int γ`.  (Points of the
range are inserted directly so that the definition is meaningful for arbitrary continuous `γ`.) -/
noncomputable def jordanRegion (γ : C(Circle, ℂ)) : Set ℂ :=
  Set.range γ ∪ {z : ℂ | Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z)}

theorem range_subset_jordanRegion (γ : C(Circle, ℂ)) : Set.range γ ⊆ jordanRegion γ :=
  Set.subset_union_left

/-! ## Dyadic grid vocabulary

The approximation step of the proof replaces a loop by a loop running along the edges of the
level-`n` dyadic grid; the pieces delegated in the companion modules are stated with these notions.
Only *unit* steps of the lattice are allowed, so that the grid skeleton is a planar graph (its
segments meet only at common endpoints) — this planarity is what the decomposition step uses. -/

/-- `e` is a unit step of the dyadic lattice: one side of a level-`n` dyadic cell, in one of the
two canonical directions. -/
def IsUnitStep (e : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  (e.1.1 = e.2.1 ∧ e.1.2 + 1 = e.2.2) ∨ (e.1.2 = e.2.2 ∧ e.1.1 + 1 = e.2.1)

/-- The level-`n` dyadic grid edge with endpoints the lattice points `e.1` and `e.2`. -/
def gridEdge (n : ℕ) (e : (ℤ × ℤ) × (ℤ × ℤ)) : Set ℂ :=
  segment ℝ (Commons.Topology.Plane.gcorner n e.1.1 e.1.2)
    (Commons.Topology.Plane.gcorner n e.2.1 e.2.2)

/-- The union of a finite set of level-`n` dyadic grid edges. -/
def gridSkeleton (n : ℕ) (E : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Set ℂ := ⋃ e ∈ E, gridEdge n e

/-- A path whose range is contained in a finite union of *unit* level-`n` grid edges lying inside
`V`. -/
def IsGridLoop (n : ℕ) (V : Set ℂ) {a b : ℂ} (q : Path a b) : Prop :=
  ∃ E : Finset ((ℤ × ℤ) × (ℤ × ℤ)), (∀ e ∈ E, IsUnitStep e ∧ gridEdge n e ⊆ V) ∧
    Set.range q ⊆ gridSkeleton n E

theorem gridSkeleton_subset {n : ℕ} {V : Set ℂ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hE : ∀ e ∈ E, IsUnitStep e ∧ gridEdge n e ⊆ V) : gridSkeleton n E ⊆ V := by
  intro z hz
  obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
  exact (hE e he).2 hze

/-- **The hypothesis that the simple (embedded) level-`n` grid loops in `V` are null-homotopic in
`V`.**  This is the form in which the decomposition step of the proof consumes the Jordan
criterion. -/
def SimpleGridLoopsNullhomotopic (n : ℕ) (V : Set ℂ) : Prop :=
  ∀ (γ : C(Circle, ℂ)) (_ : Function.Injective γ) (E : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (hE : ∀ e ∈ E, IsUnitStep e ∧ gridEdge n e ⊆ V) (hrange : Set.range γ ⊆ gridSkeleton n E),
    ∃ (w : ℂ) (hw : w ∈ V), ContinuousMap.Homotopic
      (⟨fun t => (⟨γ t, gridSkeleton_subset hE (hrange ⟨t, rfl⟩)⟩ : ↥V),
        Continuous.subtype_mk γ.continuous _⟩ : C(Circle, ↥V))
      (ContinuousMap.const Circle ⟨w, hw⟩)

/-- The hypothesis `hJ` of the criterion, in the form used below. -/
def JordanCriterion (V : Set ℂ) : Prop :=
  ∀ (γ : C(Circle, ℂ)), Function.Injective γ → Set.range γ ⊆ V →
    ∀ z : ℂ, z ∉ Set.range γ → Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) →
      z ∈ V

/-- **`hJ` says exactly that `V` contains the closed region of every Jordan curve it contains.** -/
theorem jordanRegion_subset {V : Set ℂ} (hJ : JordanCriterion V)
    {γ : C(Circle, ℂ)} (hγ : Function.Injective γ) (hrange : Set.range γ ⊆ V) :
    jordanRegion γ ⊆ V := by
  intro z hz
  rcases hz with hz | hz
  · exact hrange hz
  · by_cases hzr : z ∈ Set.range γ
    · exact hrange hzr
    · exact hJ γ hγ hrange z hzr hz

/-- **Reduction to loops.**  An open connected subset of `ℂ` is simply connected as soon as every
loop in `V` admits a null-homotopy through `V` (relative endpoints). -/
theorem simplyConnectedSpace_of_loops_nullhomotopic {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsConnected V)
    (h : ∀ (x : ℂ) (p : Path x x), (∀ t, p t ∈ V) →
      ∃ F : p.Homotopy (Path.refl x), ∀ t, F t ∈ V) :
    SimplyConnectedSpace V := by
  change IsSimplyConnected V
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  exact ⟨(hVo.isConnected_iff_isPathConnected.mp hVc), h⟩


/-! ## Assembly

The two lemmas below are the *assembly* of the pieces delegated in the companion modules; they are
proved here, so that once the pieces land the target is a short application. -/

/-- **From the Jordan criterion to the simple-grid-loop hypothesis.**  If `V` contains the closed
region of every Jordan curve it contains (`hJ`) and every Jordan curve is null-homotopic in its own
closed region (`hJor`), then every embedded grid loop in `V` is null-homotopic in `V`. -/
theorem simpleGridLoopsNullhomotopic_of_jordan {V : Set ℂ} (hJ : JordanCriterion V)
    (hJor : ∀ {γ : C(Circle, ℂ)}, Function.Injective γ →
      ∃ w : ↥(jordanRegion γ), ContinuousMap.Homotopic
        (⟨fun t => (⟨γ t, Or.inl ⟨t, rfl⟩⟩ : ↥(jordanRegion γ)),
          Continuous.subtype_mk γ.continuous _⟩ : C(Circle, ↥(jordanRegion γ)))
        (ContinuousMap.const Circle w))
    (n : ℕ) : SimpleGridLoopsNullhomotopic n V := by
  intro γ hγ E hE hrange
  have hrangeV : Set.range γ ⊆ V := fun z hz => gridSkeleton_subset hE (hrange hz)
  obtain ⟨w, hw⟩ := hJor hγ
  have hincl : ∀ z : ↥(jordanRegion γ), (z : ℂ) ∈ V :=
    fun z => jordanRegion_subset hJ hγ hrangeV z.2
  let inc : C(↥(jordanRegion γ), ↥V) :=
    ⟨fun z => ⟨(z : ℂ), hincl z⟩, Continuous.subtype_mk continuous_subtype_val hincl⟩
  let γJ : C(Circle, ↥(jordanRegion γ)) :=
    ⟨fun t => ⟨γ t, Or.inl ⟨t, rfl⟩⟩, Continuous.subtype_mk γ.continuous _⟩
  have hcomp : (inc.comp γJ).Homotopic (inc.comp (ContinuousMap.const Circle w)) :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl inc) hw
  refine ⟨(w : ℂ), hincl w, ?_⟩
  have h1 : (inc.comp γJ) = (⟨fun t => (⟨γ t, hincl ⟨γ t, Or.inl ⟨t, rfl⟩⟩⟩ : ↥V),
      Continuous.subtype_mk γ.continuous _⟩ : C(Circle, ↥V)) := by
    ext t; rfl
  have h2 : (inc.comp (ContinuousMap.const Circle w))
      = (ContinuousMap.const Circle (⟨(w : ℂ), hincl w⟩ : ↥V)) := by
    ext t; rfl
  rw [h1, h2] at hcomp
  exact hcomp

/-- **Assembly.**  If the loops of `V` can be approximated by grid loops (`hApx`), grid loops can be
reduced to their simple sub-cycles (`hDec`), and the simple grid loops are null-homotopic (`hDec`'s
hypothesis is supplied from `hS`), then `V` is simply connected. -/
theorem simplyConnectedSpace_of_grid_pieces {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V)
    (hApx : ∀ (x : ↥V) (p : Path x x),
      ∃ (n : ℕ) (v : ↥V) (α : Path v x) (q : Path v v),
        IsGridLoop n V (q.map continuous_subtype_val) ∧ Path.Homotopic (α.symm.trans (q.trans α)) p)
    (hDec : ∀ {n : ℕ} (v : ↥V) {q : Path v v}, IsGridLoop n V (q.map continuous_subtype_val) →
      Path.Homotopic q (Path.refl v)) :
    SimplyConnectedSpace V := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp (hVo.isConnected_iff_isPathConnected.mp hVc), ?_⟩
  intro x p
  obtain ⟨n, v, α, q, hq, hp⟩ := hApx x p
  have hq' : Path.Homotopic q (Path.refl v) := hDec v hq
  have h1 : Path.Homotopic (α.symm.trans (q.trans α)) (α.symm.trans ((Path.refl v).trans α)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl α.symm)
      (Path.Homotopic.hcomp hq' (Path.Homotopic.refl α))
  have h2 : Path.Homotopic (α.symm.trans ((Path.refl v).trans α)) (Path.refl x) :=
    (Path.Homotopic.hcomp (Path.Homotopic.refl α.symm) (Path.Homotopic.refl_trans α)).trans
      (Path.Homotopic.symm_trans α)
  exact hp.symm.trans (h1.trans h2)
