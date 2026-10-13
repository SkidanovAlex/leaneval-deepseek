import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Struct

theorem frV_lt_of_gt {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (i : Fin (k + 2))
    (h : (Work.DSCOH.Norm.frA2 y hy hh : ℕ) < (i : ℕ)) :
    Work.DSCOH.Norm.frV y hy hh < y i := by
  -- `frA2 y` is the last position at which `y` takes the value `frV y`.
  have hspec : y (Work.DSCOH.Norm.frA2 y hy hh) = Work.DSCOH.Norm.frV y hy hh := by
    have hH : (Finset.univ.filter (fun j : Fin (k + 2) =>
        y j = Work.DSCOH.Norm.frV y hy hh)).Nonempty :=
      ⟨(Work.DSCOH.Norm.frA y hy hh).castSucc,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    unfold Work.DSCOH.Norm.frA2
    exact (Finset.mem_filter.mp (Finset.max'_mem _ hH)).2
  have hmax : ∀ j : Fin (k + 2),
      y j = Work.DSCOH.Norm.frV y hy hh → j ≤ Work.DSCOH.Norm.frA2 y hy hh := by
    intro j hj
    unfold Work.DSCOH.Norm.frA2
    exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  -- Monotonicity gives `y (frA2 y) ≤ y i`.
  have hle : y (Work.DSCOH.Norm.frA2 y hy hh) ≤ y i :=
    hy (Fin.le_def.mpr h.le)
  -- If `y i` were also equal to `frV y`, then `i ≤ frA2 y`, contradicting the hypothesis.
  have hne : y (Work.DSCOH.Norm.frA2 y hy hh) ≠ y i := by
    intro hcontra
    have hile : i ≤ Work.DSCOH.Norm.frA2 y hy hh := hmax i (hcontra.symm.trans hspec)
    have : (i : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) := Fin.le_def.mp hile
    omega
  rw [← hspec]
  exact lt_of_le_of_ne hle hne

end Work.DSCOH.Struct
