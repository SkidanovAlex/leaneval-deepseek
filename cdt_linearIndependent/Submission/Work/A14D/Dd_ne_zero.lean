import Mathlib
import Submission.Work.A14D.classZ_defs

/-!
# Non-vanishing of the determinant `Dd = Z2·Y3 − Z3·Y2`

`Dd` (see `Submission.Work.A14D.classZ_defs`) is the determinant of the `2 × 2` system for the
coefficients `Q 2, Q 3` of the order-three class relation.  This file proves `Work.A14D.Dd ≠ 0`
from the four local-expansion hypotheses at `x = 0` on `u2, w2, u3, w3`.

The argument is a computation with leading terms at `0`.  Writing `σ` for the deck involution
`Work.C17.sigmaQ` (`x ↦ x/(x−1)`), `Lead2At f e l m` says `f = x^e·(l + m·x + O(x²))` with
`l ≠ 0`, and `Work.C17.sigma_lead` transports it to `σ f = x^e·((−1)^e l + (−1)^e(e l − m)x + O(x²))`
(the order is unchanged).  From the four hypotheses:

* `u2 = x^{-3}(3/4 + 3x + …)` and `σu2 = x^{-3}(−3/4 + 21/4·x + …)` give `Z2 = x^{-3}(3/2 + …)`;
* `u3 = x^{-5}(15/8 + …)` and `σu3 = x^{-5}(−15/8 + 75/8·x + …)` give `Z3 = x^{-5}(15/4 + …)`;
* `w2 = x^{-2}(1 − 23/4·x + …)` and `σw2 = x^{-2}(1 + 15/4·x + …)`: the leading terms cancel, and
  the *second* order terms give `Y2 = w2 − σw2 = x^{-1}(−19/2 + …)`;
* `w3 = x^{-4}(2 − 121/8·x + …)` and `σw3 = x^{-4}(2 + 57/8·x + …)` give `Y3 = x^{-3}(−89/4 + …)`.

Hence `Z2·Y3 = x^{-6}(−267/8 + …)` and `Z3·Y2 = x^{-6}(−285/8 + …)`, so the leading coefficient
`9/4` of `Dd` at order `−6` does not vanish and `Dd ≠ 0`.

The extraction of a `LeadAt` from a two-term expansion whose *leading* coefficient vanishes (the
case of `Y2` and `Y3`) is the auxiliary lemma `leadAt_of_exp2_zero` below.
-/

open Commons.FieldTheory.RatFunc
open Work.C17

namespace Work.A14D

/-- If `f = x^e·(0 + l·x + O(x²))` with `l ≠ 0` at `x = 0`, then `f = x^{e+1}·(l + O(x))`.
Concretely: `f·x^{-(e+1)} − l = x^{-1}·(f·x^{-e} − l·x)` and `f·x^{-e} − l·x` vanishes to
order at least two. -/
theorem leadAt_of_exp2_zero {f : RatFunc ℚ} {e : ℤ} {l : ℚ}
    (h : Work.C17.Exp2 f e 0 l) (hl : l ≠ 0) : Work.C17.LeadAt f (e + 1) l := by
  refine ⟨hl, ?_⟩
  set B : RatFunc ℚ := f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l * xQ with hB
  have hExp : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) 0 - algebraMap ℚ (RatFunc ℚ) l * xQ) := h
  have hBord : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) B := by
    rw [hB]
    simpa only [map_zero, sub_zero] using hExp
  have hz : (xQ : RatFunc ℚ) ^ (-(e + 1)) = xQ ^ (-e) * xQ ^ (-1 : ℤ) := by
    rw [show (-(e + 1) : ℤ) = -e + (-1 : ℤ) by ring, zpow_add₀ xQ_ne_zero]
  have hx1 : (xQ : RatFunc ℚ) ^ (-1 : ℤ) * xQ = 1 := by
    rw [zpow_neg_one, inv_mul_cancel₀ xQ_ne_zero]
  have hkey : f * xQ ^ (-(e + 1)) - algebraMap ℚ (RatFunc ℚ) l = xQ ^ (-1 : ℤ) * B := by
    rw [hz, hB,
      show (xQ : RatFunc ℚ) ^ (-1 : ℤ) * (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l * xQ)
        = xQ ^ (-1 : ℤ) * f * xQ ^ (-e)
          - (xQ ^ (-1 : ℤ) * xQ) * algebraMap ℚ (RatFunc ℚ) l by ring,
      hx1, one_mul]
    ring
  rw [hkey]
  have hxq : (((-1 : ℤ)) : WithTop ℤ) ≤ ordAtT (0 : ℚ) ((xQ : RatFunc ℚ) ^ (-1 : ℤ)) := by
    rw [ordAtT_xQ_zpow]
  exact le_trans (withTop_coe_le_coe_int (by norm_num : (1 : ℤ) ≤ -1 + 2))
    (ordAtT_mul_ge hxq hBord)

theorem Dd_ne_zero
    (hu2 : Work.C17.Lead2At Work.A14D.u2 (-3) (3 / 4) 3)
    (hw2 : Work.C17.Lead2At Work.A14D.w2 (-2) 1 (-23 / 4))
    (hu3 : Work.C17.Lead2At Work.A14D.u3 (-5) (15 / 8) 0)
    (hw3 : Work.C17.Lead2At Work.A14D.w3 (-4) 2 (-121 / 8)) :
    Work.A14D.Dd ≠ 0 := by
  -- the `σ`-companions, via `sigma_lead`
  have hs2 : Work.C17.Lead2At (Work.C17.sigmaQ Work.A14D.u2) (-3) (-3/4) (21/4) := by
    have h := (Work.C17.sigma_lead Work.A14D.u2 (-3) (3/4) 3
      (Work.C17.Lead2At.to_LeadAt hu2) hu2).2
    convert h using 2 <;> norm_num
  have ht2 : Work.C17.Lead2At (Work.C17.sigmaQ Work.A14D.w2) (-2) 1 (15/4) := by
    have h := (Work.C17.sigma_lead Work.A14D.w2 (-2) 1 (-23/4)
      (Work.C17.Lead2At.to_LeadAt hw2) hw2).2
    convert h using 2 <;> norm_num
  have hs3 : Work.C17.Lead2At (Work.C17.sigmaQ Work.A14D.u3) (-5) (-15/8) (75/8) := by
    have h := (Work.C17.sigma_lead Work.A14D.u3 (-5) (15/8) 0
      (Work.C17.Lead2At.to_LeadAt hu3) hu3).2
    convert h using 2 <;> norm_num
  have ht3 : Work.C17.Lead2At (Work.C17.sigmaQ Work.A14D.w3) (-4) 2 (57/8) := by
    have h := (Work.C17.sigma_lead Work.A14D.w3 (-4) 2 (-121/8)
      (Work.C17.Lead2At.to_LeadAt hw3) hw3).2
    convert h using 2 <;> norm_num
  -- anti-invariant parts: leading terms
  have hZ2 : Work.C17.LeadAt Work.A14D.Z2 (-3) (3/2) := by
    have h := Work.C17.LeadAt.sub_of_eq (Work.C17.Lead2At.to_LeadAt hu2)
      (Work.C17.Lead2At.to_LeadAt hs2) (by norm_num : (3/4 : ℚ) - (-3/4) ≠ 0)
    rwa [show (3/4 : ℚ) - (-3/4) = 3/2 by norm_num] at h
  have hZ3 : Work.C17.LeadAt Work.A14D.Z3 (-5) (15/4) := by
    have h := Work.C17.LeadAt.sub_of_eq (Work.C17.Lead2At.to_LeadAt hu3)
      (Work.C17.Lead2At.to_LeadAt hs3) (by norm_num : (15/8 : ℚ) - (-15/8) ≠ 0)
    rwa [show (15/8 : ℚ) - (-15/8) = 15/4 by norm_num] at h
  have hY2 : Work.C17.LeadAt Work.A14D.Y2 (-1) (-19/2) := by
    have h := Work.C17.Exp2.sub (Work.C17.Lead2At.to_exp2 hw2) (Work.C17.Lead2At.to_exp2 ht2)
    rw [show (1 : ℚ) - 1 = 0 by norm_num,
      show (-23/4 : ℚ) - 15/4 = -19/2 by norm_num] at h
    exact leadAt_of_exp2_zero h (by norm_num : (-19/2 : ℚ) ≠ 0)
  have hY3 : Work.C17.LeadAt Work.A14D.Y3 (-3) (-89/4) := by
    have h := Work.C17.Exp2.sub (Work.C17.Lead2At.to_exp2 hw3) (Work.C17.Lead2At.to_exp2 ht3)
    rw [show (2 : ℚ) - 2 = 0 by norm_num,
      show (-121/8 : ℚ) - 57/8 = -89/4 by norm_num] at h
    exact leadAt_of_exp2_zero h (by norm_num : (-89/4 : ℚ) ≠ 0)
  -- the two products and the determinant
  have hP1 : Work.C17.LeadAt (Work.A14D.Z2 * Work.A14D.Y3) (-6) (3/2 * (-89/4)) :=
    Work.C17.LeadAt.mul hZ2 hY3
  have hP2 : Work.C17.LeadAt (Work.A14D.Z3 * Work.A14D.Y2) (-6) (15/4 * (-19/2)) :=
    Work.C17.LeadAt.mul hZ3 hY2
  have hDd : Work.C17.LeadAt Work.A14D.Dd (-6) (9/4) := by
    have h := Work.C17.LeadAt.sub_of_eq hP1 hP2
      (by norm_num : (3/2 : ℚ) * (-89/4) - 15/4 * (-19/2) ≠ 0)
    rwa [show (3/2 : ℚ) * (-89/4) - 15/4 * (-19/2) = 9/4 by norm_num] at h
  exact Work.C17.LeadAt.ne_zero hDd

end Work.A14D
