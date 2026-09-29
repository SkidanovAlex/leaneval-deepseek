import Mathlib
import Submission.Work.ADcl.asym_setup
import Submission.Work.ADcl.ode_H

/-!
# `T k = A^k (T 0)` for the Theorem-A pullbacks

`Work.ADcl.Tz a b c k = ((d/dy)^[k] (Gz a b c)) ∘ y` and `Work.CDcl.Aop f = ρ · dL f` is the
`y`-derivative acting on the `x`-side.  Here: `Aop` is additive, `Tz 0` is `Hfun + Hwfun`
(since `(Sym⁺H)∘y = H + H∘φ`), and `Tz k = Aop^[k] (Tz 0)` (the generic iterated chain rule
`Work.CDcl.xco_iter_aux`).
-/

namespace Work.ADcl

noncomputable section

/-- `Aop` is additive. -/
lemma Aop_add (f g : Work.CDcl.LF) :
    Work.CDcl.Aop (f + g) = Work.CDcl.Aop f + Work.CDcl.Aop g := by
  unfold Work.CDcl.Aop
  rw [Work.CDcl.dL_add]
  ring

/-- iterated additivity of `Aop`. -/
lemma Aop_iterate_add (k : ℕ) (f g : Work.CDcl.LF) :
    Work.CDcl.Aop^[k] (f + g) = Work.CDcl.Aop^[k] f + Work.CDcl.Aop^[k] g := by
  induction k generalizing f g with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, Aop_add]

/-- `Tz a b c 0 = (Hfun + Hwfun)`: the pullback of `Sym⁺H` is `H + H∘φ`. -/
theorem Tfun_zero (a b c : ℚ) :
    Tfun a b c 0 = Hfun a b c + Hwfun a b c := by
  unfold Tfun Tz Gz Hfun Hwfun
  rw [Function.iterate_zero_apply, Submission.CDT.sympSym_subst, map_add]

/-- `Tz k = Aop^[k] (Tz 0)`. -/
theorem Tfun_iter (a b c : ℚ) (k : ℕ) :
    Tfun a b c k = Work.CDcl.Aop^[k] (Tfun a b c 0) := by
  unfold Tfun Tz Gz
  exact (Work.CDcl.xco_iter_aux (Submission.CDT.sympSym (Submission.CDT.ZagierH a b c)) k).symm

end

end Work.ADcl
