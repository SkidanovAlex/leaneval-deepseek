import Mathlib
import Submission.Work.RatHurewicz.cellDefs

/-!
# Closedness of the sublevel sets of the raw weight `rawWeight`

`Work.RatHurewicz.rawWeight D a` is the size of the support of a point of the raw model `Raw D`
when `a` lies in a copy of `Δ^{n+1}`, and `1` when `a` lies in a copy of the arc
(`Submission/Work/RatHurewicz/cellDefs.lean`).  Here we show that every sublevel set
`{a | rawWeight D a ≤ m}` is closed in `Raw D`.

The raw model is a disjoint union of two parts: `Raw D = (Σ i, Δ^{n+1}) ⊕ (Σ i, I)` carries the
sum of the sigma topologies, so by `isClosed_sum_iff` it suffices to treat the two parts
separately.

* The simplex part `Σ i, Δ^{n+1}`, where `rawWeight` counts the nonzero barycentric coordinates.
  A bound on that number is a finite union of the conditions "the support is contained in a fixed
  finite set", and each of those is a finite intersection of coordinate hyperplanes, hence closed
  (`isClosed_ptSupport_subset`, `isClosed_ptSupport_card_le`).
* The arc part `Σ i, I`, where `rawWeight` is constantly `1`, so the sublevel set is either
  everything or empty.

Closedness is then assembled through `isClosed_sum_iff` and `isClosed_sigma_iff`.

This closedness is the input of the "cell push" argument: the co-weight set
`A ∪ {a | k + 1 < rawWeight a}` is open in `Raw D` because it is the complement of the closed
set `{rawWeight ≤ k + 1} ∖ A` inside the closed set `{rawWeight ≤ k + 1}`.

Note the trap: under `open scoped Simplicial unitInterval` the *typed* set-builder
`{w : σ | p w}` does not parse; use untyped `{w | p w}` or `Set.ofPred (fun w : σ => p w)`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The set of points of the standard simplex whose support is contained in a fixed finite set is
closed: it is the finite intersection, over the vertices outside that set, of the corresponding
coordinate hyperplanes. -/
theorem isClosed_ptSupport_subset (n : ℕ) (T : Finset (Fin (n + 2))) :
    IsClosed (Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => ptSupport w ⊆ T)) := by
  have h : Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => ptSupport w ⊆ T)
      = ⋂ k : {k : Fin (n + 2) // k ∉ T},
          Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => (w : Fin (n + 2) → ℝ) k.1 = 0) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hw k
      by_contra h
      exact k.2 (hw (mem_ptSupport.mpr h))
    · intro hw k hk
      by_contra hkT
      exact (mem_ptSupport.mp hk) (hw ⟨k, hkT⟩)
  rw [h]
  exact isClosed_iInter fun k =>
    isClosed_eq ((continuous_apply k.1).comp continuous_subtype_val) continuous_const

/-- The set of points of the standard simplex whose support has at most `m` elements is closed. -/
theorem isClosed_ptSupport_card_le_raw (n m : ℕ) :
    IsClosed (Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => (ptSupport w).card ≤ m)) := by
  have h : Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => (ptSupport w).card ≤ m)
      = ⋃ T : Finset (Fin (n + 2)),
          if T.card ≤ m then Set.ofPred (fun w : stdSimplex ℝ (Fin (n + 2)) => ptSupport w ⊆ T)
          else (∅ : Set (stdSimplex ℝ (Fin (n + 2)))) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hw
      refine ⟨ptSupport w, ?_⟩
      rw [if_pos hw]
      exact Set.Subset.refl _
    · rintro ⟨T, hT⟩
      by_cases hTm : T.card ≤ m
      · rw [if_pos hTm] at hT
        exact le_trans (Finset.card_le_card hT) hTm
      · rw [if_neg hTm] at hT
        exact absurd hT (Set.notMem_empty w)
  rw [h]
  refine isClosed_iUnion_of_finite fun T => ?_
  by_cases hTm : T.card ≤ m
  · rw [if_pos hTm]; exact isClosed_ptSupport_subset n T
  · rw [if_neg hTm]; exact isClosed_empty

/-- **The sublevel sets of the raw weight are closed.** -/
theorem isClosed_rawWeight_le {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : MData X n x₀) (m : ℕ) : IsClosed (rawWeight D ⁻¹' Set.Iic m) := by
  rw [isClosed_sum_iff]
  constructor
  · have h1 : Sum.inl ⁻¹' (rawWeight D ⁻¹' Set.Iic m)
        = Set.ofPred (fun p : Sigma (fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) =>
            (ptSupport p.2).card ≤ m) := rfl
    rw [h1, isClosed_sigma_iff]
    intro i
    exact isClosed_ptSupport_card_le_raw n m
  · have h2 : Sum.inr ⁻¹' (rawWeight D ⁻¹' Set.Iic m)
        = Set.ofPred (fun _ : Sigma (fun _ : D.Idx => unitInterval) => (1 : ℕ) ≤ m) := rfl
    rw [h2]
    by_cases h : (1 : ℕ) ≤ m
    · have hp : Set.ofPred (fun _ : Sigma (fun _ : D.Idx => unitInterval) => (1 : ℕ) ≤ m)
          = (Set.univ : Set (Sigma (fun _ : D.Idx => unitInterval))) := by
        ext p; simp [h]
      rw [hp]
      exact isClosed_univ
    · have hp : Set.ofPred (fun _ : Sigma (fun _ : D.Idx => unitInterval) => (1 : ℕ) ≤ m)
          = (∅ : Set (Sigma (fun _ : D.Idx => unitInterval))) := by
        ext p; simp [h]
      rw [hp]
      exact isClosed_empty

end

end Work.RatHurewicz
