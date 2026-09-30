import Mathlib
import Submission.Work.BW.Minkowski2.adapted_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The real span of the saturation is the real span of the generators

`Ksat z j = ℤⁿ ∩ ⟨z 0, …, z j⟩_ℚ` is the saturation of the `ℤ`-span of the first `j+1` vectors
`z k`.  Its real cast spans the same space as the `z k` themselves:

`span_ℝ (castR '' Ksat z j) = Wr z j`.

The inclusion `⊇` is immediate (`z k ∈ Ksat z j` for `k ≤ j`).  For `⊆` one uses that
`castQ x ∈ Wq z j` writes the rational cast of `x` as a `ℚ`-linear combination of the casts of the
`z k`; mapping the coefficients through `ℚ ↪ ℝ` turns it into an `ℝ`-linear combination, so
`castR x ∈ Wr z j`.  This is the content of `castR_mem_Wr_of_mem_Wq` below.
-/

namespace Work.BW.Minkowski2

open Module

variable {n : ℕ}

/-- If a rational vector `v` lies in the `ℚ`-span `Wq z j` of the casts of `z 0, …, z j`, then its
componentwise real cast lies in the `ℝ`-span `Wr z j`. -/
theorem castR_mem_Wr_of_mem_Wq {z : Fin n → (Fin n → ℤ)} {j : ℕ} {v : Fin n → ℚ}
    (hv : v ∈ Wq z j) : (fun i => (v i : ℝ)) ∈ Wr z j := by
  classical
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simpa using z_mem_Wr z k.2
  | zero =>
      have h : (fun i => ((0 : Fin n → ℚ) i : ℝ)) = (0 : Fin n → ℝ) := by funext i; simp
      rw [h]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      have h : (fun i => ((a + b) i : ℝ)) = (fun i => (a i : ℝ)) + (fun i => (b i : ℝ)) := by
        funext i; simp
      rw [h]
      exact Submodule.add_mem _ iha ihb
  | smul q a _ iha =>
      have h : (fun i => ((q • a) i : ℝ)) = (q : ℝ) • (fun i => (a i : ℝ)) := by
        funext i; simp
      rw [h]
      exact Submodule.smul_mem _ (q : ℝ) iha

theorem span_castR_Ksat {n : ℕ} (z : Fin n → (Fin n → ℤ)) (j : ℕ) :
    Submodule.span ℝ (Set.range (fun x : Work.BW.Minkowski2.Ksat z j =>
      Work.BW.Minkowski2.castR n x.1)) = Work.BW.Minkowski2.Wr z j := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    show Work.BW.Minkowski2.castR n x.1 ∈ Wr z j
    have hx : (fun i => (x.1 i : ℚ)) ∈ Wq z j := mem_Ksat.mp x.2
    have hmem := castR_mem_Wr_of_mem_Wq (z := z) (j := j) hx
    have heq : Work.BW.Minkowski2.castR n x.1 = fun i => ((x.1 i : ℚ) : ℝ) := by
      funext i; simp
    rw [heq]; exact hmem
  · rw [Wr, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨⟨z k.1, z_mem_Ksat z k.2⟩, rfl⟩

end Work.BW.Minkowski2
