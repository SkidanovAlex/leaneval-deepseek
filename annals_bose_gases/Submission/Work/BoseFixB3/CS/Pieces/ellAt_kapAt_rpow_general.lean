import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB3.CS.Pieces.ellAt_kapAt_zpow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.ellAt_kapAt_rpow_general`

The `Real.rpow` (arbitrary **real** exponent `c`) companion of
`ellAt_kapAt_zpow`.  At FS's parameters
`ℓ = K_ℓ(μa)^{-1/2}`, `κ = (d²ℓ)^{-1}` with `d = (μa³)^{6/323}`, the two base
identities are

    ℓ = a·(μa³)^{-163/323},        ℓκ = (μa³)^{-12/323},

(the exponents add up as `6·2 - 163 = -151`, `-163 + 151 = -12`; the two
`a`-factors of `ℓ` and `κ = (d²ℓ)^{-1}` cancel).  Raising them to the real power
`c` with `Real.mul_rpow` / `Real.rpow_mul` and the rational arithmetic
`(-12/323)·c = -12c/323`, `(-163/323)·c = -163c/323` gives the statement.

Note that only `μ, a > 0` are needed: the base `μa³` is then positive, so the
`rpow`s are the honest ones (`Real.rpow_mul`, `Real.mul_rpow` apply).
-/

namespace Work.BoseFixB3.CS.Pieces

/-! ## 1. The two base identities -/

/-- `ℓ = a·(μa³)^{-163/323}` (`Work.BoseBox.sideAt_eq_rpow`, in the order used below). -/
private lemma ellAt_eq_rpow (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseFixB3.ellAt μ a = (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) * a := by
  rw [Work.BoseFixB3.ellAt, Work.BoseBox.sideAt_eq_rpow ha hμ, mul_comm]

/-- `ℓκ = (μa³)^{-12/323}`: `κ = (d²ℓ)^{-1}` with `d = (μa³)^{6/323}`, so
`d² = (μa³)^{12/323}` and the `ℓ` of `κ` cancels the `ℓ` of `ℓ`. -/
private lemma ellAt_mul_kapAt_eq_rpow (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a
      = (μ * a ^ 3) ^ (-(12 / 323 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  -- `d² = (μa³)^{12/323}`
  have hd2 : (Work.BoseBox.paramsAt μ a).d ^ 2 = (μ * a ^ 3) ^ ((12 : ℝ) / 323) := by
    rw [show (Work.BoseBox.paramsAt μ a).d = (μ * a ^ 3) ^ ((6 : ℝ) / 323) from rfl,
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  -- `ℓ ≠ 0`, so `ℓ·(d²ℓ)^{-1} = (d²)^{-1}`
  have hs : Work.BoseBox.sideAt μ a ≠ 0 := by
    rw [Work.BoseBox.sideAt_eq_rpow ha hμ]
    exact mul_ne_zero ha.ne' (ne_of_gt (Real.rpow_pos_of_pos ht _))
  have hkey : Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a
      = ((Work.BoseBox.paramsAt μ a).d ^ 2)⁻¹ := by
    rw [Work.BoseFixB3.ellAt, Work.BoseFixB3.kapAt]
    field_simp
  rw [hkey, hd2, ← Real.rpow_neg ht.le]

/-! ## 2. The target -/

theorem ellAt_kapAt_rpow_general (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (c : ℝ) :
    (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ c
        = (μ * a ^ 3) ^ (-(12 * c) / 323)
      ∧ (Work.BoseFixB3.ellAt μ a) ^ c
        = (μ * a ^ 3) ^ (-(163 * c) / 323) * a ^ c := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hA := ellAt_eq_rpow μ a hμ ha
  have hB := ellAt_mul_kapAt_eq_rpow μ a hμ ha
  constructor
  · rw [hB, ← Real.rpow_mul ht.le,
      show (-(12 / 323 : ℝ)) * c = -(12 * c) / 323 by ring]
  · rw [hA, Real.mul_rpow (Real.rpow_nonneg ht.le _) ha.le, ← Real.rpow_mul ht.le,
      show (-(163 / 323 : ℝ)) * c = -(163 * c) / 323 by ring]

end Work.BoseFixB3.CS.Pieces
