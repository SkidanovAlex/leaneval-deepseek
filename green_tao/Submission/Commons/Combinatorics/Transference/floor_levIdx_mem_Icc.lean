import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

namespace Commons.Combinatorics.Transference

/-- Auxiliary bound for `Int.floor`: if `|y| ≤ K + 1` then `⌊y⌋` lies in
`[-(⌈K⌉+2), ⌈K⌉+2]`. -/
lemma floor_mem_Icc_abs_aux {y K : ℝ} (h : |y| ≤ K + 1) :
    ⌊y⌋ ∈ Finset.Icc (-(⌈K⌉ + 2)) (⌈K⌉ + 2) := by
  obtain ⟨hyl, hyu⟩ := abs_le.mp h
  have hK : K ≤ ((⌈K⌉ : ℤ) : ℝ) := Int.le_ceil K
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith
  · rw [Int.floor_le_iff]
    push_cast
    linarith

theorem floor_levIdx_mem_Icc {X : Type*} (g : X → ℝ) {ε : ℝ} (hε : 0 < ε) {α : ℝ}
    (hα0 : 0 ≤ α) (hαε : α < ε) {M : ℝ} {x : X} (hx : |g x| ≤ M) :
    ⌊(g x - α) / ε⌋ ∈ Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2) := by
  obtain ⟨hg1, hg2⟩ := abs_le.mp hx
  have h1 : |g x - α| ≤ M + α := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |(g x - α) / ε| ≤ M / ε + 1 := by
    rw [abs_div, abs_of_pos hε]
    rw [div_le_iff₀ hε]
    have heq : (M / ε + 1) * ε = M + ε := by
      field_simp
    rw [heq]
    linarith
  exact floor_mem_Icc_abs_aux h2

end Commons.Combinatorics.Transference