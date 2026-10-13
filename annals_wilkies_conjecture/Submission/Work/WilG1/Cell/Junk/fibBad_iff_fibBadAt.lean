import Mathlib
import Submission.Work.WilG1.Cell.Junk.fibBad_thin_defs

namespace Work.WilG1.Cell.Junk

theorem fibBad_iff_fibBadAt (m : ℕ) (i : Fin (m + 1)) (h : (Fin (m + 1) → ℝ) → ℝ)
    (y : Fin (m + 1) → ℝ) :
    Work.WilG1.Cell.fibBad h i y ↔
      Work.WilG1.fibBadAt
          (fun x : Fin (m + 1) → ℝ =>
            h (x ∘ (Work.WilG1.Cell.Junk.insPerm m i : Fin (m + 1) → Fin (m + 1))))
          (Fin.snoc (Fin.removeNth i y) (y i)) := by
  have hz : Fin.init ((Fin.snoc (Fin.removeNth i y) (y i) : Fin (m + 1) → ℝ)) =
      Fin.removeNth i y := by
    simp
  have hl : (Fin.snoc (Fin.removeNth i y) (y i) : Fin (m + 1) → ℝ) (Fin.last m) = y i := by
    simp
  have hfun : (fun s : ℝ =>
        h ((Fin.snoc (Fin.removeNth i y) s) ∘
          (insPerm m i : Fin (m + 1) → Fin (m + 1)))) =
      (fun t : ℝ => h (Function.update y i t)) := by
    funext s
    congr 1
    rw [comp_insPerm_eq_insertNth]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.insertNth_removeNth]
  change (¬ DifferentiableAt ℝ (fun t : ℝ => h (Function.update y i t)) (y i)) ↔
    (¬ DifferentiableAt ℝ
      (fun s : ℝ => h ((Fin.snoc (Fin.init (Fin.snoc (Fin.removeNth i y) (y i) : Fin (m + 1) → ℝ)) s) ∘
        (insPerm m i : Fin (m + 1) → Fin (m + 1))))
      ((Fin.snoc (Fin.removeNth i y) (y i) : Fin (m + 1) → ℝ) (Fin.last m)))
  rw [hz, hl, hfun]

end Work.WilG1.Cell.Junk
