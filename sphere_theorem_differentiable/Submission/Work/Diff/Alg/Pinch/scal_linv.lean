import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature of the Böhm–Wilking inverse `linv a b`

`scal (ℓ_{a,b} R) = (1 + 2(n-1)a) · scal R` for algebraic curvature tensors (`Work.Diff.Alg.Pinch`,
`ell_inv.lean`), so the inverse `linv a b` (`Work.Diff.Alg.Pinch.Linv`) scales the scalar curvature
by the reciprocal factor:

`scal (linv a b Y) = scal Y / (1 + 2(n-1)a)`.

Since `linv a b Y = Y − β • (Ric₀ Y ∧ id) − γ • (id ∧ id)` with `β = b/(1+(n-2)b)` and
`γ = (a/n)/(1+2(n-1)a) · scal Y`, the computation is termwise: `scal` is linear, the two
correction terms have scalar curvatures `scal (Ric₀ Y ∧ id) = 0` (the trace of `Ric₀ Y` vanishes)
and `scal (id ∧ id) = (2n-2)·n` (`scalAlg_knProd`), and then

`scal Y − ((a/n)/(1+2(n-1)a) · scal Y)·(2n-2)·n
   = scal Y · (1 − 2(n-1)a/(1+2(n-1)a)) = scal Y / (1 + 2(n-1)a)`.

Note that only `1 + 2(n-1)a ≠ 0` is needed: the `Ric₀`-correction term drops out of the scalar
curvature for *any* coefficient `β`, in particular also when the `b`-denominator vanishes (in which
case Lean's `b / 0 = 0` makes the term vacuous but the conclusion is unaffected).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The scalar curvature of the Böhm–Wilking inverse: `scal (linv a b Y) = scal Y / (1 + 2(n-1)a)`
for every algebraic curvature tensor `Y`. -/
theorem scal_linv (n : ℕ) (a b : ℝ) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    {Y : Submission.Diff.Alg.Curv4 n} (hY : Submission.Diff.Alg.IsAlgCurv Y) :
    Submission.Diff.Alg.scalAlg (Work.Diff.Alg.Pinch.linv a b Y)
      = Submission.Diff.Alg.scalAlg Y / (1 + 2 * ((n : ℝ) - 1) * a) := by
  have hscalfun : scalAlg (linv a b Y)
      = scalAlg Y - (b / (1 + ((n : ℝ) - 2) * b)) * scalAlg (knProd (ric0 Y) (id2 n))
        - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y)
            * scalAlg (knProd (id2 n) (id2 n)) := by
    rw [linv, ellinv_scalAlg_sub, ellinv_scalAlg_sub, ellinv_scalAlg_smul, ellinv_scalAlg_smul]
  rw [hscalfun, ellinv_scalAlg_knProd_ric0 hY, ellinv_scalAlg_knProd_id2_id2, mul_zero, sub_zero]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [scalAlg]
  · have hn' : ((n : ℝ)) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
    have hkey : (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y
          * ((2 * (n : ℝ) - 2) * (n : ℝ))
        = (2 * ((n : ℝ) - 1) * a) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y := by
      field_simp
    rw [hkey]
    field_simp
    ring

end Work.Diff.Alg.Pinch
