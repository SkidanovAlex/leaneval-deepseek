import Mathlib

namespace Work.TMC16Core.NrFinal

/-- Product comparison: if `a ≤ c` then the block of `d` consecutive factors
`(a+1)···(a+d)` is dominated by `(c+1)···(c+d)`; equivalently
`(a+d)! · c! ≤ a! · (c+d)!`. -/
lemma factorial_mul_factorial_le_aux (a c d : ℕ) (h : a ≤ c) :
    (a + d).factorial * c.factorial ≤ a.factorial * (c + d).factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : a + (d + 1) = a + d + 1 := by omega
    have h2 : c + (d + 1) = c + d + 1 := by omega
    rw [h1, h2, Nat.factorial_succ (a + d), Nat.factorial_succ (c + d)]
    calc (a + d + 1) * (a + d).factorial * c.factorial
        = (a + d + 1) * ((a + d).factorial * c.factorial) := by ring
      _ ≤ (a + d + 1) * (a.factorial * (c + d).factorial) :=
            Nat.mul_le_mul_left _ ih
      _ ≤ (c + d + 1) * (a.factorial * (c + d).factorial) :=
            Nat.mul_le_mul_right _ (by omega)
      _ = a.factorial * ((c + d + 1) * (c + d).factorial) := by ring

/-- The case `a ≤ b` of the central factorial inequality. -/
lemma factorial_central_aux (a b : ℕ) (h : a ≤ b) :
    ((a + b) / 2).factorial ^ 2 ≤ a.factorial * b.factorial := by
  set m := (a + b) / 2 with hm
  set c := (a + b) - m with hc
  set d := m - a with hd
  have hma : a ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 2)]
    omega
  have hmm : m + m ≤ a + b := by
    have h' := Nat.div_mul_le_self (a + b) 2
    rw [← hm] at h'
    omega
  have hcadd : c + m = a + b := by
    rw [hc]
    exact Nat.sub_add_cancel (by rw [hm]; exact Nat.div_le_self (a + b) 2)
  have hmc : m ≤ c := by
    rw [hc]
    exact Nat.le_sub_of_add_le hmm
  have hac : a ≤ c := le_trans hma hmc
  have hb : b = c + d := by
    have h1 : b = (c + m) - a := by rw [hcadd, Nat.add_sub_cancel_left]
    rw [h1, Nat.add_sub_assoc hma, hd]
  have hkey := factorial_mul_factorial_le_aux a c d hac
  have had : a + d = m := by rw [hd]; exact Nat.add_sub_of_le hma
  have hcd : c + d = b := hb.symm
  rw [had, hcd] at hkey
  calc m.factorial ^ 2 = m.factorial * m.factorial := by ring
    _ ≤ m.factorial * c.factorial := Nat.mul_le_mul_left _ (Nat.factorial_le hmc)
    _ ≤ a.factorial * b.factorial := hkey

/-- The factorial is log-convex: for all `a b`, `((a+b)/2)! ^ 2 ≤ a! * b!`.
I.e. the middle term `m = ⌊(a+b)/2⌋` has the largest `m! · (a+b-m)!`. -/
theorem factorial_central (a b : ℕ) :
    ((a + b) / 2).factorial ^ 2 ≤ a.factorial * b.factorial := by
  rcases Nat.le_total a b with h | h
  · exact factorial_central_aux a b h
  · rw [Nat.add_comm a b, Nat.mul_comm a.factorial b.factorial]
    exact factorial_central_aux b a h

end Work.TMC16Core.NrFinal
