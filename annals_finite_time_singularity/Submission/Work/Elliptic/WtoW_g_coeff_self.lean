import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.Elliptic.WtoW_g_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- The coefficients `c_{q,j} = A_{q,j} + B_{q,j} X` of the paper's recursion vanish above the
diagonal, and equal `1` on the diagonal: `WtoW_cA q j = WtoW_cB q j = 0` for `j > q`, while
`WtoW_cA q q = 1` and `WtoW_cB q q = 0`.  In particular `c_{q,q} ≡ 1`. -/
theorem WtoW_coeff_self_aux :
    ∀ q, (∀ j, q < j → WtoW_cA q j = 0 ∧ WtoW_cB q j = 0) ∧
      WtoW_cA q q = 1 ∧ WtoW_cB q q = 0 := by
  intro q
  induction q with
  | zero =>
    refine ⟨?_, WtoW_cA_zero_zero, WtoW_cB_zero_zero⟩
    intro j hj
    have hj0 : j ≠ 0 := by omega
    constructor <;>
    · simp only [WtoW_cA, WtoW_cB, WtoW_AB.eq_1, hj0, ite_false]
      norm_num
  | succ q ih =>
    obtain ⟨ih_upper, ih_diagA, ih_diagB⟩ := ih
    have h0 : q + 1 ≠ 0 := by omega
    have h2 : q < q + 1 := by omega
    obtain ⟨_, hb2⟩ := ih_upper (q + 1) h2
    obtain ⟨ha2, _⟩ := ih_upper (q + 1) h2
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j ≠ 0 := by omega
      have h1 : q < j - 1 := by omega
      have h2' : q < j := by omega
      obtain ⟨ha1, hb1⟩ := ih_upper (j - 1) h1
      obtain ⟨ha2', hb2'⟩ := ih_upper j h2'
      constructor
      · rw [WtoW_cA_succ, if_neg hj0, ha1, hb2']; ring
      · rw [WtoW_cB_succ, if_neg hj0, hb1, ha2']; ring
    · rw [WtoW_cA_succ, if_neg h0, Nat.add_sub_cancel, ih_diagA, hb2]; ring
    · rw [WtoW_cB_succ, if_neg h0, Nat.add_sub_cancel, ih_diagB, ha2]; ring

theorem WtoW_g_coeff_self (q : ℕ) : Work.Elliptic.WtoW_ccoeff q q = fun _ => 1 := by
  obtain ⟨_, hA, hB⟩ := WtoW_coeff_self_aux q
  funext θ
  simp [WtoW_ccoeff, hA, hB]

end Work.Elliptic
