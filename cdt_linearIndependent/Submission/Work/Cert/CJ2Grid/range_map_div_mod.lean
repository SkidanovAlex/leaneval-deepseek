import Mathlib

namespace Work.Cert.CJ2Grid

theorem range_map_div_mod (n m : ℕ) (hm : 0 < m) :
    (List.range (n*m)).map (fun i => (i/m, i%m))
      = (List.range n).flatMap (fun k => (List.range m).map (fun j => (k,j))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul]
    rw [List.range_add, List.map_append]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [ih]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    have hxm : x < m := List.mem_range.mp hx
    congr 1
    · rw [Nat.mul_comm n m, Nat.add_comm, Nat.add_mul_div_left x n hm, Nat.div_eq_of_lt hxm, Nat.zero_add]
    · rw [Nat.mul_comm n m, Nat.add_comm, Nat.add_mul_mod_self_left x m n, Nat.mod_eq_of_lt hxm]

end Work.Cert.CJ2Grid
