/-
  Work.WilE2 — helpers for `variety_components_bound` (GV Corollary 3.3 on the cube).

  Basic topology of `cubeC` and `Zset` that the assembly of `variety_components_bound` needs.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE5.Flat.strictFDeriv_eaEval

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical Set
open WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-- `Zset c g` is closed: it is a finite intersection of zero sets of continuous functions. -/
theorem isClosed_Zset (c : EAChain k r) (g : Finset (EAPoly k r)) : IsClosed (Zset c g) := by
  have : Zset c g = ⋂ f ∈ g, {x | eaEval c f x = 0} := by
    ext x; simp [Zset]
  rw [this]
  exact isClosed_biInter fun f _ =>
    isClosed_eq (Work.WilE5.Flat.continuous_eaEval c f) continuous_const

/-- `cubeC k` is the product of the unit intervals, hence compact and closed. -/
theorem isCompact_cubeC (k : ℕ) : IsCompact (cubeC k) := by
  have hp : cubeC k = Set.pi Set.univ (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [cubeC, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩
  rw [hp]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_cubeC (k : ℕ) : IsClosed (cubeC k) := (isCompact_cubeC k).isClosed

/-- The interior of the cube is the set of points all of whose coordinates have absolute value
strictly less than one. -/
theorem interior_cubeC (k : ℕ) :
    interior (cubeC k) = {x | ∀ i, |x i| < 1} := by
  have hp : cubeC k = Set.pi Set.univ (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [cubeC, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩
  rw [hp, interior_pi_set (Set.finite_univ)]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, interior_Icc,
    Set.mem_Ioo]
  exact ⟨fun h i => abs_lt.mpr (h i), fun h i => abs_lt.mp (h i)⟩

/-- A point of the cube whose coordinates are all strictly less than one in absolute value lies in
the interior. -/
theorem mem_interior_cubeC {x : Fin k → ℝ} (h : ∀ i, |x i| < 1) : x ∈ interior (cubeC k) := by
  rw [interior_cubeC]; exact h

/-- A point of the frontier of the cube has some coordinate equal to `1` or to `-1`. -/
theorem frontier_cubeC_subset {x : Fin k → ℝ} (hx : x ∈ frontier (cubeC k)) :
    ∃ j : Fin k, x j = 1 ∨ x j = -1 := by
  have hxC : x ∈ cubeC k := (isClosed_cubeC k).closure_subset (frontier_subset_closure hx)
  have hxI : x ∉ interior (cubeC k) := (mem_frontier_iff_notMem_interior hxC).mp hx
  rw [interior_cubeC] at hxI
  simp only [Set.mem_setOf_eq] at hxI
  push Not at hxI
  obtain ⟨j, hj⟩ := hxI
  have hj1 : |x j| ≤ 1 := hxC j
  have hge : 1 ≤ |x j| := hj
  have habs : |x j| = 1 := le_antisymm hj1 hge
  exact ⟨j, (abs_eq zero_le_one).mp habs⟩

/-- A connected component of `X = cubeC k ∩ Zset c g` either meets the frontier of the cube, or is
contained in its interior. -/
theorem component_or_frontier {c : EAChain k r} {g : Finset (EAPoly k r)} (x : Fin k → ℝ) :
    (connectedComponentIn (cubeC k ∩ Zset c g) x ∩ frontier (cubeC k)).Nonempty ∨
      connectedComponentIn (cubeC k ∩ Zset c g) x ⊆ interior (cubeC k) := by
  by_cases h : (connectedComponentIn (cubeC k ∩ Zset c g) x ∩ frontier (cubeC k)).Nonempty
  · exact Or.inl h
  · refine Or.inr fun y hy => ?_
    have hyC : y ∈ cubeC k := (connectedComponentIn_subset _ _ hy).1
    have hyI : y ∈ interior (cubeC k) := by
      by_contra hcontra
      exact h ⟨y, hy, (mem_frontier_iff_notMem_interior hyC).mpr hcontra⟩
    exact hyI

end Work.WilE2
