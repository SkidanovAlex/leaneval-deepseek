import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdDefs

namespace Work.IntLib.SqrtGcd

/-- Stripping all factors of `2` from a nonzero natural number leaves an odd number, and the
removed factors are exactly a power of two. -/
theorem oddPartVal (n : ℕ) (hn : n ≠ 0) :
    ∃ k : ℕ, n = Work.IntLib.SG.oddPart n * 2 ^ k ∧ Work.IntLib.SG.oddPart n % 2 = 1 ∧
      0 < Work.IntLib.SG.oddPart n := by
  induction n using Work.IntLib.SG.oddPart.induct with
  | case1 x hx ih =>
      -- `x` is nonzero and even: `oddPart x = oddPart (x / 2)` and `x = 2 * (x / 2)`.
      rw [Work.IntLib.SG.oddPart.eq_def, if_pos hx]
      obtain ⟨k, hk, hodd, hpos⟩ := ih (by omega)
      refine ⟨k + 1, ?_, hodd, hpos⟩
      have hx2 : 2 ∣ x := by omega
      have hxeq : x / 2 * 2 = x := Nat.div_mul_cancel hx2
      have hk2 : x / 2 * 2 = (Work.IntLib.SG.oddPart (x / 2) * 2 ^ k) * 2 :=
        congrArg (· * 2) hk
      calc x = x / 2 * 2 := hxeq.symm
        _ = (Work.IntLib.SG.oddPart (x / 2) * 2 ^ k) * 2 := hk2
        _ = Work.IntLib.SG.oddPart (x / 2) * 2 ^ (k + 1) := by rw [pow_succ]; ring
  | case2 x hx =>
      -- `oddPart x = x` here, and `x` is nonzero and odd.
      rw [Work.IntLib.SG.oddPart.eq_def, if_neg hx]
      refine ⟨0, by simp, ?_, Nat.pos_of_ne_zero hn⟩
      omega

end Work.IntLib.SqrtGcd
