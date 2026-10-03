import Mathlib
import Submission.Work.PlanarSC.SpineDefs
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleAux

/-!
# Building orders for the spine of a polyomino (lattice-step vocabulary)

This module sets up the vocabulary for `Work.PlanarSC.building_order_of_no_jordan`: the
combinatorial core "a connected spine without Jordan curves admits a building order"
(`Work.PlanarSC.HasBuildingOrder`).

We describe the spine `Work.PlanarSC.spine S = ⋃ e ∈ gEdges 0 S, segment ℝ e.1 e.2` in terms of
*unit lattice steps* `(ℤ × ℤ) × (ℤ × ℤ)` in the namespace `Work.HornSC.CellBoundaryJordan`
(`IsUnitStep`, `stepSeg`, `lpt`, `adjSeg`, `IsUnitAdj`):

* `SpineSteps S` — the steps of the spine: the two vertical sides of every occupied cell, and the
  horizontal sides of the cells whose southern neighbour is empty;

* `stepVerts A` — the lattice points occurring as endpoints of the steps of `A`;

* `StepAdj A v w` — `v ≠ w` are joined by a step of `A`;

* `HasStepOrder A` — the lattice-level building order: an enumeration of `A` in which every step
  after the first meets the union of its predecessors in exactly one point.

All the lemmas in this file are elementary; the geometry of unit grid segments lives in
`Submission/Work/HornSC/CellBoundaryJordan/GridCycleAux.lean` (`adjSeg_east`, `eq_lpt_of_mem_adjSeg`,
`adjSeg_eq_of_mem_of_not_lattice`, …).

NB: the namespace is nested inside `Work.HornSC.CellBoundaryJordan` on purpose, so that the
unqualified names `stepSeg`, `lpt`, `adjSeg`, `IsUnitStep`, `IsUnitAdj` refer to the HornSC notions
(inside `namespace Work.PlanarSC` they would resolve to the unrelated same-named definitions of
`Submission/Work/PlanarSC/jordan_criterion_simplyConnected.lean`, `.../GridWalk.lean`).
-/

open Set

namespace Work.HornSC.CellBoundaryJordan.BO

noncomputable section

/-! ## The steps of a spine -/

/-- The unit steps of the spine of `S`: the two vertical sides of each occupied cell, together with
the horizontal (bottom) side of each occupied cell whose southern neighbour is empty. -/
def SpineSteps (S : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (S.image fun p => ((p.1, p.2), (p.1, p.2 + 1))) ∪
  (S.image fun p => ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1))) ∪
  ((S.filter fun p => (p.1, p.2 - 1) ∉ S).image fun p => ((p.1, p.2), (p.1 + 1, p.2)))

theorem mem_SpineSteps {S : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ SpineSteps S ↔
      (∃ p ∈ S, e = ((p.1, p.2), (p.1, p.2 + 1))) ∨
      (∃ p ∈ S, e = ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1))) ∨
      (∃ p ∈ S, (p.1, p.2 - 1) ∉ S ∧ e = ((p.1, p.2), (p.1 + 1, p.2))) := by
  simp only [SpineSteps, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ((⟨p, hp, h⟩ | ⟨p, hp, h⟩) | ⟨p, ⟨hp, hne⟩, he⟩)
    · exact Or.inl ⟨p, hp, h.symm⟩
    · exact Or.inr (Or.inl ⟨p, hp, h.symm⟩)
    · exact Or.inr (Or.inr ⟨p, hp, hne, he.symm⟩)
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, hne, h⟩)
    · exact Or.inl (Or.inl ⟨p, hp, h.symm⟩)
    · exact Or.inl (Or.inr ⟨p, hp, h.symm⟩)
    · exact Or.inr ⟨p, ⟨hp, hne⟩, h.symm⟩

theorem isUnitStep_of_mem_SpineSteps {S : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ SpineSteps S) : IsUnitStep e := by
  rcases mem_SpineSteps.mp he with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, hne, rfl⟩
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem SpineSteps_nonempty {S : Finset (ℤ × ℤ)} (hne : S.Nonempty) :
    (SpineSteps S).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨((p.1, p.2), (p.1, p.2 + 1)), mem_SpineSteps.mpr (Or.inl ⟨p, hp, rfl⟩)⟩

/-! ## Elementary geometry of the steps -/

/-- The closed segment of a unit step, described by its endpoints. -/
theorem stepSeg_eq_segment {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e) :
    stepSeg e = segment ℝ (lpt e.1) (lpt e.2) := by
  obtain ⟨u, v⟩ := e
  change stepSeg (u, v) = segment ℝ (lpt u) (lpt v)
  have h' : v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) := he
  rcases h' with h | h
  · rw [stepSeg_of_eq_east (u := u) (v := v) h, h]
    exact (adjSeg_east u).symm
  · rw [stepSeg_of_eq_north (u := u) (v := v) h, h]
    exact (adjSeg_north u).symm

theorem stepSeg_isClosed (e : (ℤ × ℤ) × (ℤ × ℤ)) : IsClosed (stepSeg e) := by
  rw [stepSeg]
  split
  · exact isClosed_hSeg _
  · exact isClosed_vSeg _

theorem isClosed_biUnion_stepSeg (A : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    IsClosed (⋃ e ∈ A, stepSeg e) :=
  Set.Finite.isClosed_biUnion A.finite_toSet (fun e _ => stepSeg_isClosed e)

theorem stepSeg_nonempty (e : (ℤ × ℤ) × (ℤ × ℤ)) : (stepSeg e).Nonempty := by
  rw [stepSeg]
  split
  · exact ⟨lpt e.1, lpt_mem_hSeg e.1⟩
  · exact ⟨lpt e.1, lpt_mem_vSeg e.1⟩

theorem lpt_mem_stepSeg {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e) : lpt e.1 ∈ stepSeg e := by
  rw [stepSeg_eq_segment he]
  exact left_mem_segment ℝ _ _

theorem isStep_ne {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e) : e.1 ≠ e.2 := by
  rcases he with h | h
  · intro hc
    have hf1 : e.2.1 = e.1.1 + 1 := by simpa using congrArg Prod.fst h
    have hf2 : e.2.1 = e.1.1 := by simpa using (congrArg Prod.fst hc).symm
    omega
  · intro hc
    have hs1 : e.2.2 = e.1.2 + 1 := by simpa using congrArg Prod.snd h
    have hs2 : e.2.2 = e.1.2 := by simpa using (congrArg Prod.snd hc).symm
    omega

theorem isUnitAdj_of_isUnitStep {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : IsUnitStep e) :
    IsUnitAdj e.1 e.2 := by
  rcases he with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

theorem isUnitAdj_symm {u v : ℤ × ℤ} (h : IsUnitAdj u v) : IsUnitAdj v u := by
  rcases h with h | h | h | h
  · subst h; exact Or.inr (Or.inl (by simp))
  · subst h; exact Or.inl (by simp)
  · subst h; exact Or.inr (Or.inr (Or.inr (by simp)))
  · subst h; exact Or.inr (Or.inr (Or.inl (by simp)))

/-! ## The vertex set and the adjacency relation of a family of steps -/

/-- The lattice points occurring as endpoints of the steps of `A`. -/
def stepVerts (A : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Finset (ℤ × ℤ) :=
  A.biUnion fun e => {e.1, e.2}

theorem mem_stepVerts {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {v : ℤ × ℤ} :
    v ∈ stepVerts A ↔ ∃ e ∈ A, v = e.1 ∨ v = e.2 := by
  simp only [stepVerts, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]

/-- Two lattice points are joined by a step of `A`. -/
def StepAdj (A : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (v w : ℤ × ℤ) : Prop :=
  ∃ e ∈ A, (e.1 = v ∧ e.2 = w) ∨ (e.1 = w ∧ e.2 = v)

theorem stepAdj_symm {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {v w : ℤ × ℤ}
    (h : StepAdj A v w) : StepAdj A w v := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr ⟨h.1, h.2⟩⟩
  · exact ⟨e, he, Or.inl ⟨h.1, h.2⟩⟩

theorem stepVerts_of_stepAdj {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {v w : ℤ × ℤ}
    (h : StepAdj A v w) : v ∈ stepVerts A ∧ w ∈ stepVerts A := by
  obtain ⟨e, he, h | h⟩ := h
  · rw [← h.1, ← h.2]
    exact ⟨mem_stepVerts.mpr ⟨e, he, Or.inl rfl⟩, mem_stepVerts.mpr ⟨e, he, Or.inr rfl⟩⟩
  · rw [← h.2, ← h.1]
    exact ⟨mem_stepVerts.mpr ⟨e, he, Or.inr rfl⟩, mem_stepVerts.mpr ⟨e, he, Or.inl rfl⟩⟩

theorem stepAdj_of_mem {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ A) : StepAdj A e.1 e.2 :=
  ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

theorem stepVerts_mem_fst {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ A) : e.1 ∈ stepVerts A :=
  mem_stepVerts.mpr ⟨e, he, Or.inl rfl⟩

theorem stepVerts_mem_snd {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ A) : e.2 ∈ stepVerts A :=
  mem_stepVerts.mpr ⟨e, he, Or.inr rfl⟩

theorem stepAdj_ne {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} (hunit : ∀ e ∈ A, IsUnitStep e)
    {v w : ℤ × ℤ} (h : StepAdj A v w) : v ≠ w := by
  obtain ⟨e, he, h | h⟩ := h
  · rw [← h.1, ← h.2]; exact isStep_ne (hunit e he)
  · rw [← h.2, ← h.1]; exact (isStep_ne (hunit e he)).symm

theorem isUnitAdj_of_stepAdj {A : Finset ((ℤ × ℤ) × (ℤ × ℤ))} (hunit : ∀ e ∈ A, IsUnitStep e)
    {v w : ℤ × ℤ} (h : StepAdj A v w) : IsUnitAdj v w := by
  obtain ⟨e, he, h | h⟩ := h
  · rw [← h.1, ← h.2]; exact isUnitAdj_of_isUnitStep (hunit e he)
  · rw [← h.2, ← h.1]; exact isUnitAdj_symm (isUnitAdj_of_isUnitStep (hunit e he))

/-! ## The building order for a family of steps -/

/-- **A building order for a family of unit steps.**  The steps of `A` are enumerated as
`f 0, f 1, …, f (N-1)` and each `f k` with `k ≥ 1` meets the union of its predecessors in exactly
one point (necessarily a lattice point). -/
def HasStepOrder (A : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Prop :=
  ∃ (N : ℕ) (f : ℕ → (ℤ × ℤ) × (ℤ × ℤ)), 0 < N ∧
    (∀ e, e ∈ A ↔ ∃ k : ℕ, k < N ∧ f k = e) ∧
    (∀ k : ℕ, 0 < k → k < N → ∃ p : ℤ × ℤ, stepSeg (f k) ∩
      (⋃ j : ℕ, ⋃ (_ : j < k), stepSeg (f j)) = {lpt p})

end

end Work.HornSC.CellBoundaryJordan.BO
