/-
Basic cell/dimension calculus for CW complexes, used to prove that a compact subset of a
CW complex is contained in a finite skeleton.
-/
import Mathlib
import Submission.Work.CWTOP.Basic

namespace Work.CWTOP

open Set Topology

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- Skeletons are monotone in the dimension. -/
lemma skel_mono {a b : ℕ} (h : a ≤ b) : skel C a ⊆ skel C b := by
  intro x hx
  rw [SetLike.mem_coe, CWComplex.mem_skeleton_iff] at hx ⊢
  obtain ⟨m, hm, j, hj⟩ := hx
  exact ⟨m, hm.trans (by exact_mod_cast h), j, hj⟩

/-- Every point of a CW complex lies in an open cell. -/
lemma exists_openCell_of_mem {x : X} (hx : x ∈ C) :
    ∃ (n : ℕ) (j : RelCWComplex.cell C n), x ∈ RelCWComplex.openCell n j := by
  have h : x ∈ ⋃ (n : ℕ) (j : RelCWComplex.cell C n), RelCWComplex.openCell n j := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    exact hx
  simpa only [mem_iUnion] using h

/-- A point of an open `n`-cell is not in any skeleton of dimension `< n`. -/
lemma notMem_skel_of_mem_openCell {n d : ℕ} {j : RelCWComplex.cell C n} {x : X}
    (hx : x ∈ RelCWComplex.openCell n j) (h : d < n) : x ∉ skel C d := by
  have hd := RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (d : ℕ∞)) (m := n) (j := j)
    (by exact_mod_cast h)
  exact fun hxs => Set.disjoint_left.mp hd hxs hx

/-- Conversely: a point of an open `n`-cell that lies in the `d`-skeleton has `n ≤ d`. -/
lemma le_of_mem_openCell_of_mem_skel {n d : ℕ} {j : RelCWComplex.cell C n} {x : X}
    (hx : x ∈ RelCWComplex.openCell n j) (h : x ∈ skel C d) : n ≤ d := by
  by_contra hlt
  exact notMem_skel_of_mem_openCell hx (Nat.lt_of_not_le hlt) h

end Work.CWTOP
