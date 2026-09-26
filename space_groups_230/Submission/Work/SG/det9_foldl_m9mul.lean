import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.det9_spec
import Submission.Work.SG.det9_mul

namespace Work.SG

/-- Auxiliary statement: folding `m9mul` over `w` starting from any length-9 accumulator. -/
theorem det9_foldl_m9mul_aux (w : List (List ℤ)) (acc : List ℤ) (hacc : acc.length = 9)
    (h : ∀ g ∈ w, g.length = 9) :
    det9 (w.foldl m9mul acc) = det9 acc * (w.map det9).prod := by
  induction w generalizing acc with
  | nil => simp
  | cons g t ih =>
      rw [List.foldl_cons, List.map_cons, List.prod_cons,
        ih (m9mul acc g) (length_m9mul acc g) (fun x hx => h x (List.mem_cons_of_mem g hx)),
        det9_mul hacc (h g List.mem_cons_self)]
      ring

/-- `det9` of a product of length-9 flat matrices is the product of the determinants. -/
theorem det9_foldl_m9mul (w : List (List ℤ)) (h : ∀ g ∈ w, g.length = 9) :
    det9 (w.foldl m9mul [1, 0, 0, 0, 1, 0, 0, 0, 1]) = (w.map det9).prod := by
  rw [det9_foldl_m9mul_aux w [1, 0, 0, 0, 1, 0, 0, 0, 1] (by decide) h,
    show det9 [1, 0, 0, 0, 1, 0, 0, 0, 1] = 1 by decide]
  ring

end Work.SG
