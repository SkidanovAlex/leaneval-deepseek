import Mathlib
import Submission.Work.Pi6.MSS.mssMulCompat
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The normalization of a page of the assembled spectral sequence is the identity

`mssNorm 𝕜 W r s q` is the identification `mssE 𝕜 W r (s,q) ≅ pEraw 𝕜 W r s (s+q)` of the
bidegree-indexed page with the concrete page, i.e. the transport `pCast` of the identity along the
index equalities `EI (s,q) = s`, `EN (s,q) = s + q` (`Submission/Work/Pi6/MSS/AssembleCore.lean`).

Since `EI` and `EN` are *definitionally* the identity on a pair of natural numbers (the truncated
subtraction/`if` in their definitions reduce on `((s : ℤ), (q : ℤ))`), the transport is the identity:
this is the general form of `Work.Pi6.MSS.mssNorm_hom_self` (the case `s = 0`).
-/

namespace Work.Pi6.MSS

theorem mssNorm_hom_eq_self (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s q : ℕ)
    (x : mssE 𝕜 W r ((s : ℤ), (q : ℤ))) :
    (mssNorm 𝕜 W r s q).hom x = x := by
  rw [mssNorm_hom_apply]
  -- `EI (s,q) = s` and `EN (s,q) = s + q` are reflexive on a pair of natural numbers, so the
  -- transport is the transport along the reflexive index equalities, i.e. the identity.
  rw [pCast_congr 𝕜 W r (EI_pair s q) rfl (EN_pair s q) rfl]
  exact pCast_apply_self 𝕜 W r x

end Work.Pi6.MSS
