import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.C17adj.phi_identity

/-!
# Clearing the denominators of Zagier's operator

`PhiNumZ W` is *defined* as the denominator-cleared numerator `DZ³·(LZf (W/DZ))`
of Zagier's operator `LZf` (in self-adjoint form) applied to `β = W/DZ`,
`DZ = x²(x−1)`.  The theorem `Zadj_clearing` records that the definition does
compute that object:

`algebraMap (PhiNumZ W) = (algebraMap DZ)³ · LZf β`   in `ℂ(x)`.

The mathematical content is the quotient rule, applied twice:

* `β  = nn/d`,   `β' = (nn'·d − nn·d')/d²`,
* `β'' = (nn''·d² − 2·nn'·d·d' + nn·(2·d'² − d·d''))/d³`,

which after multiplying by `d³` gives exactly the polynomial defining `PhiNumZ`.
This is the general clearing identity `Work.C17adj.dRat_adj_clearing_general`
specialised to `P2 = P2Z`, `P1 = P1Z`, `P0 = P0Z`, `nn = W`, `d = DZ`.
-/

open Polynomial

namespace Work.A14D

/-- **Clearing the denominators of Zagier's operator at `β = W/DZ`.** -/
theorem Zadj_clearing {W : Polynomial ℂ} {β : RatFunc ℂ}
    (hβW : algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ * β) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNumZ W)
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ) ^ 3 * (LZf β) := by
  have hDZ' : (algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ) ≠ 0 := fun h =>
    DZ_ne_zero (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by rw [h, map_zero]))
  have hβ : β
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) W
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) DZ := by
    rw [eq_div_iff hDZ', mul_comm]
    exact hβW.symm
  subst hβ
  unfold PhiNumZ LZf
  exact Work.C17adj.dRat_adj_clearing_general P2Z P1Z P0Z W DZ DZ_ne_zero

end Work.A14D
