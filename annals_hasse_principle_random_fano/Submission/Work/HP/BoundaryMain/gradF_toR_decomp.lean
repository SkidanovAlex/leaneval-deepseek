import Mathlib
import Submission.Work.HP.BoundaryMain.bm_defs
import Submission.Work.HP.GradDecomp.gradF_decomp

/-!
# `∂_k f_{toR a}(y)` split along `zeroSInt`

This is the integer-coefficient version of `Work.HP.GradDecomp.gradF_decomp`: for
`f = zeroSInt d n hd1 j a` (the coefficient vector `a` with the `n+1` special monomials
`smon d n hd1 j ·` set to zero), the partial derivative of `f_{toR a}` in direction `k` equals the
partial derivative of `f_{toR f}` plus the explicit contribution of the special monomials.

It is obtained from `gradF_decomp` applied to the real coefficient vector `toR a` by transporting
`zeroS d n hd1 j (toR a)` back along `toR_zeroSInt` and using `hf`.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.HP.BoundaryMain

theorem gradF_toR_decomp (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d)
    (a : Work.HP.Mon d n → ℤ) (y : Fin (n + 1) → ℝ) (j k : Fin (n + 1)) (f : Work.HP.Mon d n → ℤ)
    (hf : Work.HP.BoundaryMain.zeroSInt d n hd1 j a = f) :
    Work.HP.gradF d n (Work.HP.toR a) y k = Work.HP.gradF d n (Work.HP.toR f) y k +
      (if k = j then y j ^ (d - 2) * ((d : ℝ) * (a (Work.HP.smon d n hd1 j j) : ℝ) * y j
          + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (a (Work.HP.smon d n hd1 j i) : ℝ) * y i)
        else (a (Work.HP.smon d n hd1 j k) : ℝ) * y j ^ (d - 1)) := by
  have h := Work.HP.GradDecomp.gradF_decomp d n hd1 hd2 (Work.HP.toR a) y j k
  rw [← Work.HP.BoundaryMain.toR_zeroSInt d n hd1 j a, hf] at h
  simpa only [Work.HP.toR] using h

end Work.HP.BoundaryMain
