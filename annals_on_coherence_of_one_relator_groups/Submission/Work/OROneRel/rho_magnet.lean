/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

The rewritten relator `magnet r t` represents the original relator `r` under `rho`, whenever the
exponent sum of `t` in `r` is zero: the `t`-letters of `r` cancel against the frame corrections.
-/

import Mathlib
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.rho_magRew

namespace Work.OROneRel

universe u

/-- If the exponent sum of `t` in `r` is zero, the Magnus rewriting `magnet r t` of the relator is
mapped back to `r` by `rho`: the `t`-letters of `r` reappear as the frame corrections. -/
theorem rho_magnet {α : Type u} (r : FreeGroup α) (t : α) (h : eps t r = 0) :
    rho t (magnet r t) = r := by
  classical
  have hmain := rho_magRew t 0 r.toWord
  rw [show wordEps t r.toWord = 0 from h, add_zero] at hmain
  rw [magnet, hmain, zpow_zero, one_mul, neg_zero, zpow_zero, mul_one]
  exact (FreeGroup.mk_toWord (x := r)).symm ▸ rfl

end Work.OROneRel
