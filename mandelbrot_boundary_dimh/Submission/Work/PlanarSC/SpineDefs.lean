import Mathlib
import Submission.Work.PlanarSC.PolyTools
import Submission.Lib.Unif2.Work.Spine.Basic
import Submission.Lib.Unif2.Work.Mori.ArgumentPeriod
import Submission.Lib.Unif2.Commons.Topology.Plane.retract_union_accumulate_of_retracts

/-!
# The spine of a polyomino: definitions and basic facts

`Work.PlanarSC.spine S ⊆ Commons.Topology.Plane.polyK S` is the union of the lattice edges of the
polyomino `polyK S`; it is the library's `Commons.Topology.Plane.spineSet S S` and `polyK S`
strongly deformation retracts onto it.  This module (sorry-free) collects the definitions
(`spine`, `spineG`, `HasBuildingOrder`) and the elementary facts about them used by
`Work.PlanarSC.polyK_holefree_simplyConnected`.
-/

namespace Work.PlanarSC

open Set

noncomputable section

/-- The spine of `polyK S` — the union of its lattice edges.  It agrees with the library's
`Commons.Topology.Plane.spineSet S S`. -/
def spine (S : Finset (ℤ × ℤ)) : Set ℂ :=
  ⋃ e ∈ Commons.Topology.Plane.gEdges 0 S, segment ℝ e.1 e.2

theorem gVerts_subset_spine (S : Finset (ℤ × ℤ)) :
    (↑(Commons.Topology.Plane.gVerts 0 S) : Set ℂ) ⊆ spine S := by
  intro v hv
  rw [Finset.mem_coe, Commons.Topology.Plane.mem_gVerts] at hv
  obtain ⟨p, hp, hcase⟩ := hv
  rcases hcase with h | h | h | h
  · refine mem_iUnion₂.mpr ⟨(Commons.Topology.Plane.gcorner 0 p.1 p.2,
      Commons.Topology.Plane.gcorner 0 p.1 (p.2 + 1)), ?_, ?_⟩
    · exact Finset.mem_union_left _ (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inl ⟨p, hp, rfl⟩))
    · rw [h]; exact left_mem_segment ℝ _ _
  · refine mem_iUnion₂.mpr ⟨(Commons.Topology.Plane.gcorner 0 (p.1 + 1) p.2,
      Commons.Topology.Plane.gcorner 0 (p.1 + 1) (p.2 + 1)), ?_, ?_⟩
    · exact Finset.mem_union_left _ (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inr ⟨p, hp, rfl⟩))
    · rw [h]; exact left_mem_segment ℝ _ _
  · refine mem_iUnion₂.mpr ⟨(Commons.Topology.Plane.gcorner 0 p.1 p.2,
      Commons.Topology.Plane.gcorner 0 p.1 (p.2 + 1)), ?_, ?_⟩
    · exact Finset.mem_union_left _ (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inl ⟨p, hp, rfl⟩))
    · rw [h]; exact right_mem_segment ℝ _ _
  · refine mem_iUnion₂.mpr ⟨(Commons.Topology.Plane.gcorner 0 (p.1 + 1) p.2,
      Commons.Topology.Plane.gcorner 0 (p.1 + 1) (p.2 + 1)), ?_, ?_⟩
    · exact Finset.mem_union_left _ (Commons.Topology.Plane.mem_gVEdges.mpr (Or.inr ⟨p, hp, rfl⟩))
    · rw [h]; exact right_mem_segment ℝ _ _

theorem dsc_zero : Commons.Topology.Plane.dsc 0 = id := by
  funext z
  apply Complex.ext
  · change z.re / (2 : ℝ) ^ 0 = z.re
    rw [pow_zero, div_one]
  · change z.im / (2 : ℝ) ^ 0 = z.im
    rw [pow_zero, div_one]

/-- The spine as defined here is the library's `spineSet S S` (the union of the `U`-cores). -/
theorem spine_eq_spineSet (S : Finset (ℤ × ℤ)) : spine S = Commons.Topology.Plane.spineSet S S := by
  have h : Commons.Topology.Plane.spineSet S S = Commons.Topology.Plane.YSet 0 S S := by
    have h' := Commons.Topology.Plane.image_dsc_spineSet 0 S S
    rw [dsc_zero] at h'
    simpa using h'
  have h2 : Commons.Topology.Plane.YSet 0 S S = spine S := by
    rw [Commons.Topology.Plane.YSet_eq_segments]
    exact Set.union_eq_right.mpr (gVerts_subset_spine S)
  exact (h.trans h2).symm

theorem spine_eq_spineSet' (S : Finset (ℤ × ℤ)) :
    Commons.Topology.Plane.spineSet S S = spine S := (spine_eq_spineSet S).symm

/-- The spine, viewed as a subspace of `↥(polyK S)`. -/
def spineG (S : Finset (ℤ × ℤ)) : Set ↥(Commons.Topology.Plane.polyK S) :=
  {x | (x : ℂ) ∈ Commons.Topology.Plane.spineSet S S}

/-- **`polyK S` strongly deformation retracts onto its spine**, so the two are homotopy
equivalent. -/
theorem nonempty_homotopyEquiv_polyK_spineG (S : Finset (ℤ × ℤ)) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Commons.Topology.Plane.polyK S) ↥(spineG S)) := by
  obtain ⟨Φ, h0, h1, hfix⟩ := Commons.Topology.Plane.exists_spine_retraction S
  refine Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
    (X := ↥(Commons.Topology.Plane.polyK S)) (spineG S)
    (fun q : ↥(Commons.Topology.Plane.polyK S) × unitInterval => Φ q) Φ.continuous ?_ ?_ ?_
  · intro x; exact Subtype.ext (h0 x)
  · intro x; exact h1 x
  · intro x hx t; exact Subtype.ext (hfix x hx t)

/-- `↥(spineG S)` and `↥(spineSet S S)` are canonically the same space. -/
theorem simplyConnectedSpace_spineG_iff (S : Finset (ℤ × ℤ)) :
    SimplyConnectedSpace ↥(spineG S) ↔
      SimplyConnectedSpace ↥(Commons.Topology.Plane.spineSet S S) := by
  have himg : (Subtype.val : ↥(Commons.Topology.Plane.polyK S) → ℂ) '' spineG S =
      Commons.Topology.Plane.spineSet S S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz, rfl⟩
  have h := (Topology.IsEmbedding.subtypeVal
      (p := fun z : ℂ => z ∈ Commons.Topology.Plane.polyK S)).isSimplyConnected_image (s := spineG S)
  have h' : IsSimplyConnected (Commons.Topology.Plane.spineSet S S) ↔ IsSimplyConnected (spineG S) := by
    rw [← himg]
    exact h
  exact h'.symm

/-- **Simple connectivity transfers from the spine to the polyomino.** -/
theorem simplyConnectedSpace_polyK_of_spineSet (S : Finset (ℤ × ℤ))
    (h : SimplyConnectedSpace ↥(Commons.Topology.Plane.spineSet S S)) :
    SimplyConnectedSpace ↥(Commons.Topology.Plane.polyK S) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_polyK_spineG S
  haveI : SimplyConnectedSpace ↥(spineG S) := (simplyConnectedSpace_spineG_iff S).mpr h
  exact e.simplyConnectedSpace

/-- A retract of the contractible space `ℂ` is simply connected. -/
theorem simplyConnectedSpace_spine_of_retract (S : Finset (ℤ × ℤ))
    (h : Commons.Topology.Plane.IsRetract (Commons.Topology.Plane.spineSet S S)) :
    SimplyConnectedSpace ↥(Commons.Topology.Plane.spineSet S S) := by
  obtain ⟨r, hr⟩ := h
  refine Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction
    ⟨Subtype.val, continuous_subtype_val⟩ r ?_
  ext x : 1
  exact hr x

/-! ## Building orders -/

/-- **A building order for the edge family of `S`.**  The edges of `gEdges 0 S` are enumerated
as `f 0, f 1, …, f (N-1)`, and each `f k` with `k ≥ 1` meets the union of its predecessors in
exactly one point. -/
def HasBuildingOrder (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ (N : ℕ) (f : ℕ → ℂ × ℂ),
    0 < N ∧
    (∀ e : ℂ × ℂ, e ∈ Commons.Topology.Plane.gEdges 0 S ↔ ∃ k : ℕ, k < N ∧ f k = e) ∧
    (∀ k : ℕ, 0 < k → k < N → ∃ p : ℂ,
      segment ℝ (f k).1 (f k).2 ∩ (⋃ j : ℕ, ⋃ (_ : j < k), segment ℝ (f j).1 (f j).2) = {p})

/-- The spine is connected as soon as the polyomino is. -/
theorem isPreconnected_spine (S : Finset (ℤ × ℤ))
    (hpre : IsPreconnected (Commons.Topology.Plane.polyK S)) : IsPreconnected (spine S) := by
  obtain ⟨Φ, h0, h1, hfix⟩ := Commons.Topology.Plane.exists_spine_retraction S
  haveI : PreconnectedSpace ↥(Commons.Topology.Plane.polyK S) :=
    isPreconnected_iff_preconnectedSpace.mp hpre
  let g : ↥(Commons.Topology.Plane.polyK S) → ↥(Commons.Topology.Plane.spineSet S S) :=
    fun x => ⟨(Φ (x, (1 : ↥Commons.Topology.Plane.uI)) : ℂ), h1 x⟩
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ (fun x => h1 x)
    exact continuous_subtype_val.comp (Φ.continuous.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ↥(Commons.Topology.Plane.polyK S) =>
        (1 : ↥Commons.Topology.Plane.uI))))
  have hsurj : Function.Surjective g := by
    intro y
    exact ⟨⟨(y : ℂ), y.2.1⟩, Subtype.ext (hfix ⟨(y : ℂ), y.2.1⟩ y.2 1)⟩
  have himg : IsPreconnected (g '' (Set.univ : Set ↥(Commons.Topology.Plane.polyK S))) :=
    isPreconnected_univ.image g hgc.continuousOn
  have hsp : IsPreconnected (Set.univ : Set ↥(Commons.Topology.Plane.spineSet S S)) := by
    have h1 : (g '' (Set.univ : Set ↥(Commons.Topology.Plane.polyK S))) = Set.univ := by
      rw [Set.image_univ]
      exact Set.range_eq_univ.mpr hsurj
    rw [← h1]
    exact himg
  have h2 := hsp.image (Subtype.val : ↥(Commons.Topology.Plane.spineSet S S) → ℂ)
    continuous_subtype_val.continuousOn
  have h3 : Subtype.val '' (Set.univ : Set ↥(Commons.Topology.Plane.spineSet S S)) =
      Commons.Topology.Plane.spineSet S S := by
    ext z
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hz; exact ⟨⟨z, hz⟩, trivial, rfl⟩
  rw [spine_eq_spineSet, ← h3]
  exact h2

end

end Work.PlanarSC
