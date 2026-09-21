import Mathlib
import Submission.Work.OddRadon.Core

/-!
# Norm of the paper's normal direction `ξ(α)`

`radonXi d α` is the paper's vector `ξ(α) = (sin α, 0, …, 0, -cos α) ∈ ℝ^d`
(`Work.OddRadon.Core`).  For `d ≥ 2` its two possibly nonzero coordinates `0` and `d - 1`
are distinct, so its Euclidean norm is `√(sin²α + cos²α) = 1`.  The hypothesis `2 ≤ d`
is essential: for `d = 1` the two slots coincide and the vector is `(sin α)`.
-/

namespace Work.OddRadon

open scoped RealInnerProductSpace

lemma radonXi_norm (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α : ℝ) : ‖radonXi d α‖ = 1 := by
  -- the two special indices `0` and `d - 1` are distinct because `d ≥ 2`
  have hane0 : (⟨d - 1, by omega⟩ : Fin d) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [EuclideanSpace.norm_eq]
  have hterm0 : ‖(radonXi d α) (0 : Fin d)‖ ^ 2 = Real.sin α ^ 2 := by
    rw [radonXi_apply]; simp
  have hterm1 : ‖(radonXi d α) (⟨d - 1, by omega⟩ : Fin d)‖ ^ 2 = Real.cos α ^ 2 := by
    rw [radonXi_apply]
    have : ((⟨d - 1, by omega⟩ : Fin d) : ℕ) ≠ 0 := by simp; omega
    simp [this]
  -- only the two special coordinates contribute to the sum of squares
  have hsplit : ∑ i : Fin d, ‖(radonXi d α) i‖ ^ 2 = Real.sin α ^ 2 + Real.cos α ^ 2 := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin d))
      (fun i => ‖(radonXi d α) i‖ ^ 2) (Finset.mem_univ (0 : Fin d))]
    rw [hterm0]
    congr 1
    rw [Finset.sum_eq_single_of_mem (⟨d - 1, by omega⟩ : Fin d)
      (Finset.mem_erase.mpr ⟨hane0, Finset.mem_univ _⟩)]
    · exact hterm1
    · intro b hb hbne
      rw [radonXi_apply]
      have hb0 : (b : ℕ) ≠ 0 := by
        have hbne0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
        simpa using hbne0
      have hb1 : (b : ℕ) ≠ d - 1 := by
        intro h
        exact hbne (Fin.ext (by simp [h]))
      simp [hb0, hb1]
  rw [hsplit, Real.sin_sq_add_cos_sq]
  simp

end Work.OddRadon
