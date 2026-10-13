import Mathlib
import Submission.Work.WilE5.Cells

namespace Work.WilE5.Cells

open WilkiesDesign WilkiesDesign.E

/-- The total degree of the atoms of a concatenation of lists is the sum of the per-list
totals. (General list bookkeeping used to unfold `atomsOf` against `SemiPf.deg`.) -/
theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]

theorem khovDegEq {k : ℕ} (X : WilkiesDesign.E.SemiPf k) :
    ((Work.WilE5.atomsOf X).map WilkiesDesign.E.atomDeg).sum = X.deg := by
  obtain ⟨r, c, bs⟩ := X
  simp only [Work.WilE5.atomsOf, WilkiesDesign.E.SemiPf.deg]
  exact sum_flatMap_map bs (fun A : Basic k r => A.eqs ++ A.pos)
    (WilkiesDesign.E.atomDeg : EAPoly k r → ℕ)

end Work.WilE5.Cells
