import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.ellAt_kapAt_eq`

The closed form of the two `B3` parameter abbreviations in terms of the single
diluteness monomial `X = fsXp (μa³) 1 = (μa³)^{1/323}`:

* `ellAt μ a = ℓ = K_ℓ(μa)^{-1/2} = a·X^{-163} = a·(μa³)^{-163/323}`,
* `kapAt μ a = κ = (d²ℓ)^{-1} = X^{151}/a = (μa³)^{151/323}/a`
  (since `d = X⁶`, so `d²ℓ = X^{12}·a·X^{-163} = a·X^{-151}`),
* hence `ℓκ = X^{-12}` (the two `a`-factors cancel).

The exponents add up as `12 + (-163) = -151` and `-163 + 151 = -12`; the only
inputs are `sideAt_eq_rpow` (`ℓ = a·(μa³)^{-163/323}`), `fsXp_mul`, `fsXp_inv`
and `a > 0`.
-/

namespace Work.BoseFixB3.Conv

/-- The zpow form of the diluteness monomial: `(X)^n = (μa³)^{n/323}`, i.e. the
integer powers of `fsXp t 1 = t^{1/323}` are again `fsXp`s.  (`rpow_intCast`
converts the zpow into an `rpow`, `fsXp_rpow` collects the exponents.) -/
lemma fsXp_one_zpow (t : ℝ) (ht : 0 < t) (n : ℤ) :
    (Work.BoseBox.fsXp t 1) ^ n = Work.BoseBox.fsXp t (n : ℝ) := by
  rw [← Real.rpow_intCast, Work.BoseBox.fsXp_rpow ht.le, one_mul]

theorem ellAt_kapAt_eq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseFixB3.ellAt μ a = (Work.BoseBox.fsXp (μ * a ^ 3) 1) ^ (-163 : ℤ) * a ∧
    Work.BoseFixB3.kapAt μ a = (Work.BoseBox.fsXp (μ * a ^ 3) 1) ^ (151 : ℤ) / a ∧
    Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a
      = (Work.BoseBox.fsXp (μ * a ^ 3) 1) ^ (-12 : ℤ) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  -- `a·(μa³)^{-163/323}` is `a·fsXp (μa³) (-163)`
  have he : (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) = Work.BoseBox.fsXp (μ * a ^ 3) (-163) := by
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hside : Work.BoseBox.sideAt μ a = Work.BoseBox.fsXp (μ * a ^ 3) (-163) * a := by
    rw [Work.BoseBox.sideAt_eq_rpow ha hμ, he, mul_comm]
  have hℓ : Work.BoseFixB3.ellAt μ a = Work.BoseBox.fsXp (μ * a ^ 3) (-163) * a := by
    rw [Work.BoseFixB3.ellAt, hside]
  -- `d = fsXp (μa³) 6`, so `d² = fsXp (μa³) 12`
  have hd : (Work.BoseBox.paramsAt μ a).d = Work.BoseBox.fsXp (μ * a ^ 3) 6 := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  have hD : (Work.BoseBox.paramsAt μ a).d ^ 2 = Work.BoseBox.fsXp (μ * a ^ 3) 12 := by
    rw [hd, pow_two, Work.BoseBox.fsXp_mul ht]
    norm_num
  -- `d²ℓ = fsXp (μa³) (-151)·a`
  have hprod : (Work.BoseBox.paramsAt μ a).d ^ 2 * Work.BoseBox.sideAt μ a
      = Work.BoseBox.fsXp (μ * a ^ 3) (-151) * a := by
    rw [hD, hside, ← mul_assoc, Work.BoseBox.fsXp_mul ht]
    norm_num
  -- `κ = (d²ℓ)^{-1} = fsXp (μa³) 151 / a`
  have hκ : Work.BoseFixB3.kapAt μ a = Work.BoseBox.fsXp (μ * a ^ 3) 151 / a := by
    rw [Work.BoseFixB3.kapAt, hprod, mul_inv, Work.BoseBox.fsXp_inv ht, div_eq_mul_inv]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hℓ, fsXp_one_zpow (μ * a ^ 3) ht (-163)]
    norm_num
  · rw [hκ, fsXp_one_zpow (μ * a ^ 3) ht (151)]
    norm_num
  · rw [hℓ, hκ, fsXp_one_zpow (μ * a ^ 3) ht (-12)]
    have h3 : Work.BoseBox.fsXp (μ * a ^ 3) (-163) * a
          * (Work.BoseBox.fsXp (μ * a ^ 3) 151 / a)
        = Work.BoseBox.fsXp (μ * a ^ 3) (-163) * Work.BoseBox.fsXp (μ * a ^ 3) 151 := by
      field_simp
    rw [h3, Work.BoseBox.fsXp_mul ht]
    norm_num

end Work.BoseFixB3.Conv
