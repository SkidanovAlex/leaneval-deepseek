import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.IntLib.chunksAPI

namespace Work.KronP

open HvdH

/-- `((max x 0).toNat : ℤ) - ((max (-x) 0).toNat : ℤ) = x`: the positive/negative-part
decomposition of an integer. -/
theorem int_toNat_pos_sub_neg (x : ℤ) :
    ((max x 0).toNat : ℤ) - ((max (-x) 0).toNat : ℤ) = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by omega)]
    rw [show (0 : ℤ).toNat = 0 from rfl, Int.toNat_of_nonneg hx]
    ring
  · have hx' : x < 0 := by omega
    rw [max_eq_right (le_of_lt hx'), max_eq_left (by omega)]
    rw [show (0 : ℤ).toNat = 0 from rfl, Int.toNat_of_nonneg (by omega : 0 ≤ -x)]
    ring

/-- Recursion step for `pack`. -/
theorem pack_cons (a : ℤ) (t : List ℤ) (b : ℕ) :
    pack (a :: t) b = a + (2 : ℤ) ^ b * pack t b := by
  unfold pack
  rw [show (a :: t).length = t.length + 1 from rfl, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
  rw [show (a :: t).getD 0 0 * (2 : ℤ) ^ (b * 0) = a from by simp]
  rw [show List.map ((fun j => (a :: t).getD j 0 * (2 : ℤ) ^ (b * j)) ∘ Nat.succ)
            (List.range t.length)
        = List.map (fun j => (t.getD j 0 * (2 : ℤ) ^ (b * j)) * (2 : ℤ) ^ b)
            (List.range t.length) from by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, List.getD_cons_succ]
      rw [Nat.mul_succ, pow_add]
      ring]
  rw [List.sum_map_mul_right]
  ring

theorem packEvalSub (l : List ℤ) (b : ℕ) :
    Work.KronP.pack l b =
      ((HvdH.evalChunks (l.map (fun x => (max x 0).toNat)) b : ℕ) : ℤ) -
      ((HvdH.evalChunks (l.map (fun x => (max (-x) 0).toNat)) b : ℕ) : ℤ) := by
  induction l with
  | nil => simp [pack, HvdH.evalChunks]
  | cons a t ih =>
    rw [pack_cons, List.map_cons, List.map_cons, Work.IntLib.evalChunks_cons,
        Work.IntLib.evalChunks_cons]
    push_cast
    rw [ih]
    have hkey := int_toNat_pos_sub_neg a
    rw [show ((max a 0).toNat : ℤ) = a + ((max (-a) 0).toNat : ℤ) from by linarith]
    ring

end Work.KronP
