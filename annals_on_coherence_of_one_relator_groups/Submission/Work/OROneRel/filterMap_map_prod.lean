import Mathlib

namespace Work.OROneRel

theorem filterMap_map_prod {δ β M : Type*} [Monoid M] (l : List δ)
    (G : δ → Option (β × Bool)) (F : β × Bool → M) :
    ((l.filterMap G).map F).prod = (l.map (fun d => (G d).elim 1 F)).prod := by
  induction l with
  | nil => simp
  | cons d t ih =>
    cases h : G d with
    | none => simp [h, ih]
    | some x => simp [h, ih]

end Work.OROneRel
