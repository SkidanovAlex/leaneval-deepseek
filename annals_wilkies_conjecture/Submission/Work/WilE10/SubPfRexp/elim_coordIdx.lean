import Mathlib
import Submission.Work.WilE10.SubPfRexp.Defs

namespace Work.WilE10.SubPfRexp

theorem elim_coordIdx {n m r P : ℕ} (x : Fin n → ℝ) (y : Work.WilE10.SubPfRexp.Wit n m r P → ℝ)
    (u : Fin n → ℝ) (w : Fin m → ℝ)
    (hu : ∀ a, y (Work.WilE10.SubPfRexp.Wit.uIdx a) = u a)
    (hw : ∀ b, y (Work.WilE10.SubPfRexp.Wit.wIdx b) = w b) (i : Fin (n + m)) :
    Sum.elim x y (Work.WilE10.SubPfRexp.coordIdx (P := P) i) = Fin.append u w i := by
  rw [Work.WilE10.SubPfRexp.coordIdx]
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    simp [Sum.elim, hu, hw]

end Work.WilE10.SubPfRexp
