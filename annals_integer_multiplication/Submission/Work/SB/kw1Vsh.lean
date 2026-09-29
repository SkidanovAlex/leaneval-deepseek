import Mathlib
import Submission.Work.Params.steps

namespace Work.SB

/-- Sum of `vsz` over a list of values, bounded by the length times a uniform bound. -/
theorem sum_map_vsz_le (l : List HvdH.Val) (B : ℕ) (h : ∀ x ∈ l, HvdH.vsz x ≤ B) :
    (l.map HvdH.vsz).sum ≤ l.length * B := by
  calc (l.map HvdH.vsz).sum ≤ (l.map (fun _ => B)).sum := List.sum_le_sum (fun x hx => h x hx)
    _ = l.length * B := by simp

/-- `vsh n (P ++ Tr) ≤ n * Bv` when the first `n` values all come from `P`, which is bounded
by `Bv` elementwise. -/
theorem kw1Vsh {n Bv : ℕ} {P Tr : List HvdH.Val} (hn : n ≤ P.length)
    (h : ∀ x ∈ P, HvdH.vsz x ≤ Bv) : Work.Params.vsh n (P ++ Tr) ≤ n * Bv := by
  rw [Work.Params.vsh_eq, List.take_append_of_le_length hn]
  calc ((P.take n).map HvdH.vsz).sum
      ≤ ((P.take n).map (fun _ => Bv)).sum :=
        List.sum_le_sum (fun x hx => h x (List.mem_of_mem_take hx))
    _ = (P.take n).length * Bv := by simp
    _ ≤ n * Bv := Nat.mul_le_mul_right _ (List.length_take_le n P)

end Work.SB
