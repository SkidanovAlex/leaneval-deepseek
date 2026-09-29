import Mathlib

namespace Work.Resample

/-- Sliding a length-`L` window by `g ≤ L` splits it into the part that stays and the part that
comes in from beyond the window: the `g` elements dropped from the front of `l[a..a+L)` are
replaced by the `g` elements of `l[a+L..a+L+g)`. -/
theorem auSlideList {α : Type} (l : List α) (a L g : ℕ) (hg : g ≤ L) :
    ((l.drop a).take L).drop g ++ (l.drop (a + L)).take g = (l.drop (a + g)).take L := by
  rw [List.drop_take, List.drop_drop]
  conv_rhs => rw [← Nat.sub_add_cancel hg]
  rw [List.take_add, List.drop_drop]
  have h2 : (a + g) + (L - g) = a + L := by omega
  rw [h2]

end Work.Resample
