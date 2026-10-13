import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-- The position `frA2 y` carries the value `frV y`. -/
lemma frA2_apply {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) : y (frA2 y hy hh) = frV y hy hh := by
  unfold frA2
  exact (Finset.mem_filter.mp (Finset.max'_mem
    (Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh)) _)).2

/-- ``Between the first repeat and the last occurrence of the repeated value, `y` is constantly
`frV y`''': for a nondecreasing tuple `y` which is not strictly increasing, every position `i`
with `frA y ≤ i ≤ frA2 y` carries the value `frV y`.

Indeed `frV y = y (frA y).castSucc ≤ y i` by monotonicity (as `(frA y).castSucc ≤ i`), while
`y i ≤ y (frA2 y) = frV y` again by monotonicity (as `i ≤ frA2 y`); antisymmetry gives equality. -/
theorem frV_eq_of_between {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (i : Fin (k + 2))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ (i : ℕ))
    (h2 : (i : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ)) :
    y i = Work.DSCOH.Norm.frV y hy hh := by
  have hA2 : y (frA2 y hy hh) = frV y hy hh := frA2_apply y hy hh
  have hle1 : frV y hy hh ≤ y i := by
    rw [frV]
    exact hy (by simp only [Fin.le_def, Fin.val_castSucc]; exact h1)
  have hle2 : y i ≤ frV y hy hh := by
    rw [← hA2]
    exact hy (by simp only [Fin.le_def]; exact h2)
  exact le_antisymm hle2 hle1

end Work.DSCOH.Struct
