import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.ellAt_sq_mul_d_pow_le`

The third conjunct of `Work.BoseFixB3.Conv.dilute_consequences`: in the dilute
regime `μa³ ≤ 1` the box side `ℓ = ellAt μ a` and the parameter `d` satisfy

  `ℓ² d^{80} ≤ a²`.

Both quantities are monomials in the diluteness `t = μa³`:
`ellAt μ a = a·t^{-163/323}` (closed form `sideAt_eq_rpow`) and `d = t^{6/323}`
(`patAt_d`), so

  `ℓ² d^{80} = a² · t^{-326/323} · t^{480/323} = a² · t^{154/323} ≤ a²`,

the last step because `0 < t ≤ 1` and the exponent `154/323` is positive
(`fsXp_le_one`).

All the constituent facts are shipped (`Work.BoseBox.sideAt_eq_rpow`,
`Work.BoseBox.fsXp_pow`, `Work.BoseBox.fsXp_mul`, `Work.BoseBox.fsXp_le_one`);
this file only does the exponent arithmetic.
-/

namespace Work.BoseFixB3.Conv

open scoped Real Topology BigOperators

lemma ellAt_sq_mul_d_pow_le (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (h1 : μ * a ^ 3 ≤ 1) :
    (Work.BoseFixB3.ellAt μ a) ^ 2 * ((Work.BoseFixB3.patAt μ a).d) ^ 80 ≤ a ^ 2 := by
  have ht : 0 < μ * a ^ 3 := by positivity
  -- closed form of the box side: `ℓ = a·(μa³)^{-163/323}`
  have hℓ : Work.BoseFixB3.ellAt μ a = Work.BoseBox.fsXp (μ * a ^ 3) (-163) * a := by
    rw [Work.BoseFixB3.ellAt, Work.BoseBox.sideAt_eq_rpow ha hμ, Work.BoseBox.fsXp,
      mul_comm a _]
    congr 1
    norm_num
  -- the parameter `d = (μa³)^{6/323}`
  have hd : (Work.BoseFixB3.patAt μ a).d = Work.BoseBox.fsXp (μ * a ^ 3) 6 := by
    simp [Work.BoseFixB3.patAt, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  -- collected exponents
  have e2 : (Work.BoseBox.fsXp (μ * a ^ 3) (-163)) ^ 2
      = Work.BoseBox.fsXp (μ * a ^ 3) (-326) := by
    rw [Work.BoseBox.fsXp_pow ht.le]
    norm_num
  have e80 : (Work.BoseBox.fsXp (μ * a ^ 3) 6) ^ 80
      = Work.BoseBox.fsXp (μ * a ^ 3) 480 := by
    rw [Work.BoseBox.fsXp_pow ht.le]
    norm_num
  rw [hℓ, hd, mul_pow, e2, e80]
  have hprod : Work.BoseBox.fsXp (μ * a ^ 3) (-326) * Work.BoseBox.fsXp (μ * a ^ 3) 480
      = Work.BoseBox.fsXp (μ * a ^ 3) 154 := by
    rw [Work.BoseBox.fsXp_mul ht]
    norm_num
  have h154 : Work.BoseBox.fsXp (μ * a ^ 3) 154 ≤ 1 :=
    Work.BoseBox.fsXp_le_one ht h1 (by norm_num)
  calc Work.BoseBox.fsXp (μ * a ^ 3) (-326) * a ^ 2 * Work.BoseBox.fsXp (μ * a ^ 3) 480
      = a ^ 2 * (Work.BoseBox.fsXp (μ * a ^ 3) (-326)
          * Work.BoseBox.fsXp (μ * a ^ 3) 480) := by ring
    _ = a ^ 2 * Work.BoseBox.fsXp (μ * a ^ 3) 154 := by rw [hprod]
    _ ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left h154 (sq_nonneg a)
    _ = a ^ 2 := by ring

end Work.BoseFixB3.Conv
