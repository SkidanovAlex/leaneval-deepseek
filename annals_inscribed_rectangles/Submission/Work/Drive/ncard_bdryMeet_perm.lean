import Mathlib
import Submission.Work.Drive.TripleMeetDefs

namespace Work.Drive

/-- **The labelled boundary triple counts are invariant under permuting the three chains.**  For a permutation `σ` of the three chains, the `0`-th boundary count of the permuted triple `fun i => D (σ i)` equals the `σ 0`-th boundary count of `D`.  The parameter triples correspond under the bijection `x ↦ (fun j => x (σ⁻¹ j))`, which carries the box and meet conditions to themselves and the boundary predicate `P (x 0)` to `P (y (σ 0))`.  Instantiating `P z := z ∈ unitBoxBdry 2 ∧ z 2 = 1` (resp. `z 2 = 0`) gives the permutation invariance of `Work.Drive.topBdryMeet` (resp. `bottomBdryMeet`), which is what lets the `0`-th block multiplicativity be applied to all three blocks of Hugelmeyer's parity identity. -/
theorem ncard_bdryMeet_perm (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (P : EuclideanSpace ℝ (Fin 3) → Prop)
    (σ : Equiv.Perm (Fin 3)) :
    ({x : Fin 3 → EuclideanSpace ℝ (Fin 3) |
        (∀ k : Fin 3, x k ∈ Submission.Drive.unitBox 2) ∧
        D (σ 0) (x 0) = D (σ 1) (x 1) ∧ D (σ 0) (x 0) = D (σ 2) (x 2) ∧ P (x 0)}).ncard
      = ({y : Fin 3 → EuclideanSpace ℝ (Fin 3) |
        (∀ k : Fin 3, y k ∈ Submission.Drive.unitBox 2) ∧
        D 0 (y 0) = D 1 (y 1) ∧ D 0 (y 0) = D 2 (y 2) ∧ P (y (σ 0))}).ncard := by
  classical
  -- The reindexing bijection `x ↦ (fun j => x (σ⁻¹ j))` maps the left-hand triple set onto the
  -- right-hand one: it satisfies the box and meet conditions identically, and carries the boundary
  -- predicate `P (x 0)` (at `x 0`) to `P (y (σ 0))`.
  refine Set.ncard_congr (fun x _ => fun j => x (σ.symm j)) ?_ ?_ ?_
  · -- every left-hand triple is carried to a right-hand triple.
    intro x hx
    obtain ⟨hxbox, hx01, hx02, hxP⟩ := hx
    -- all three chains meet in the single point `D (σ 0) (x 0)`.
    have key : ∀ i : Fin 3, D (σ i) (x i) = D (σ 0) (x 0) := by
      intro i
      fin_cases i
      · rfl
      · exact hx01.symm
      · exact hx02.symm
    refine ⟨fun k => hxbox (σ.symm k), ?_, ?_, ?_⟩
    · simpa using (key (σ.symm 0)).trans (key (σ.symm 1)).symm
    · simpa using (key (σ.symm 0)).trans (key (σ.symm 2)).symm
    · simpa using hxP
  · -- the reindexing is injective.
    intro x x' hx hx' h
    funext i
    have := congrFun h (σ i)
    simpa using this
  · -- and surjective onto the right-hand triple set, with inverse `y ↦ (fun i => y (σ i))`.
    intro y hy
    obtain ⟨hybox, hy01, hy02, hyP⟩ := hy
    have key : ∀ j : Fin 3, D j (y j) = D 0 (y 0) := by
      intro j
      fin_cases j
      · rfl
      · exact hy01.symm
      · exact hy02.symm
    refine ⟨fun i => y (σ i), ?_, ?_⟩
    · refine ⟨fun k => hybox (σ k), ?_, ?_, ?_⟩
      · simpa using (key (σ 0)).trans (key (σ 1)).symm
      · simpa using (key (σ 0)).trans (key (σ 2)).symm
      · exact hyP
    · funext j
      simp

end Work.Drive
