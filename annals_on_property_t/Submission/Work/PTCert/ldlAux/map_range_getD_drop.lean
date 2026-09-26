import Mathlib
import Submission.Work.PTCert.ldlAux

namespace Work.PTCert.ldlAux

theorem map_range_getD_drop {α : Type} (l : List α) (a : α) (i : ℕ) :
    (List.range (l.length - i)).map (fun d => l.getD (i + d) a) = l.drop i := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.length_cons, Nat.sub_zero, List.drop_zero]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hfun : ((fun d => (x :: xs).getD (0 + d) a) ∘ Nat.succ) =
          fun d => xs.getD (0 + d) a := by
        funext d
        simp
      rw [hfun]
      simp only [Nat.add_zero, List.getD_cons_zero, Nat.zero_add]
      have ih0 : List.map (fun d => xs.getD d a) (List.range xs.length) = xs := by
        simpa using ih 0
      rw [ih0]
    | succ i =>
      simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]
      have h1 : ∀ d, (x :: xs).getD (i + 1 + d) a = xs.getD (i + d) a := by
        intro d
        rw [show i + 1 + d = (i + d) + 1 by omega, List.getD_cons_succ]
      simp only [h1, ih i, List.drop_succ_cons]

end Work.PTCert.ldlAux
