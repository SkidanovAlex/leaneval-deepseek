import Mathlib

namespace Work.Resample

lemma dropAppTakeCongr {β : Type*} (A : List β) (x y : β) (L d : ℕ) (hA : A.length = L)
    (hd : d ≤ 1) (h : d = 1 → x = y) :
    (A.drop d ++ [x]).take L = (A.drop d ++ [y]).take L := by
  interval_cases d
  · simp [hA]
  · simp [h rfl]

end Work.Resample
