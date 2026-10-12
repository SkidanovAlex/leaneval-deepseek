import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Basic
import Submission.Work.BoseFixB3.Conv.ellAt_kapAt_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Conv

/-- **The `(-40)`-power of the product `ℓκ` is the `80`-th power of `d`.**

Since `ellAt_kapAt_eq` gives `ℓκ = X^{-12}` with `X = fsXp (μa³) 1` and
`d = X⁶`, one has `(ℓκ)^{-40} = X^{480} = (X⁶)^{80} = d^{80}`.  The two
`fsXp`-forms are converted into powers of the single monomial `X` by
`fsXp_one_zpow`, and the integer powers are collected with `zpow_mul`
(and `zpow_ofNat` to read the outer `^80` of the right-hand side as an
integer power). -/
lemma ellAt_mul_kapAt_zpow_neg40 (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ (-(40 : ℤ))
      = ((Work.BoseFixB3.patAt μ a).d) ^ 80 := by
  obtain ⟨-, -, hprod⟩ := ellAt_kapAt_eq μ a hμ ha
  have ht : 0 < μ * a ^ 3 := by positivity
  -- `d = fsXp (μa³) 6`
  have hd : (Work.BoseFixB3.patAt μ a).d = Work.BoseBox.fsXp (μ * a ^ 3) 6 := by
    simp [Work.BoseFixB3.patAt, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [hprod, hd]
  -- both `fsXp`-values are powers of the single monomial `X = fsXp (μa³) 1`
  have h2 : Work.BoseBox.fsXp (μ * a ^ 3) 6
      = (Work.BoseBox.fsXp (μ * a ^ 3) 1) ^ (6 : ℤ) := by
    rw [fsXp_one_zpow (μ * a ^ 3) ht 6]
    norm_num
  rw [h2]
  -- `(X^{-12})^{-40} = X^{480} = (X⁶)^{80}`
  rw [← zpow_mul (Work.BoseBox.fsXp (μ * a ^ 3) 1) (-12) (-40)]
  rw [zpow_ofNat]
  rw [← pow_mul]
  norm_num

end Work.BoseFixB3.Conv
