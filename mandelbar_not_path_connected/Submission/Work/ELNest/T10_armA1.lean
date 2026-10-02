/-
# The tenth iterate on the level-`n` arm-`A` angle of the nest at `b₂`

This file proves `T10_armA1`: the tenth iterate of the angle-doubling map
`Work.EL.T θ = Int.fract (-2 * θ)` sends the first angle `armA1 n` of the level-`n`
arm-`A` pair of the nest at `b₂` to the first angle `armC1 (n - 1)` of the level-`(n-1)`
arm-`C` pair.  This is the arithmetic half of the statement that the degree-`1024` map
`F c = (T_c)^{10}` rotates the piece of the level-`n` arm `A` below the cut point `cutA n`
onto the piece of the level-`(n-1)` arm `C` below `cutC (n-1)` (see
`Submission/Work/ELNest/rot_cut.lean`, whose proof consumes exactly this identity through
`landsN_iterate_F`).

## The mathematics

`contract t fix N = fract (fix + centred (t - fix) / N)` is the point of the level-`N`
neighbourhood of `fix` lying over the angle `t`; here `N = 64^n`.  The two relevant
`centred` values are the exact rationals

    centred (α₁ - 22/63) = 289/21483,        centred (821/1023 - 37/63) = 4624/21483,

so that, with `64^n ≥ 1` squeezing the fractional part into `[0,1)`,

    armA1 n = 22/63 + (289/21483)/64^n,      armC1 n = 37/63 + (4624/21483)/64^n.

Since `T^[10] θ = fract (1024 θ)` (`T_iterate_ten`) and `1024 = 16 · 64`, one round of the
`b₂`-nest shrinks the `A`-angle by the factor `64`, and then

    1024 · (22/63 + (289/21483)/64^{m+1}) = 357 + 37/63 + (4624/21483)/64^m

because `1024 · 22/63 = 357 + 37/63` and `1024 · 289 = 16 · 4624`.  The integer `357`
disappears in the fractional part and `37/63 + (4624/21483)/64^m < 1`, so
`T^[10] (armA1 (m+1)) = armC1 m`, which is the statement for `n = m + 1 ≥ 1`.

The arithmetic is a specialisation of the general `b₂`-nest rotation
`T^[10] (armX (n+1)) = arm(next of X) n`, which has three instances
(`A → C`, `B → A`, `C → B`); the file below proves the `A → C` instance only.
-/
import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-! ## `centred` on the two exact differences -/

/-- On the open interval `(-1/2, 1/2)` the map `centred` is the identity: `x + 1/2` lies in
`(0, 1)`, so it is its own fractional part. -/
private theorem centred_eq_self' {x : ℝ} (h1 : -(1 / 2) < x) (h2 : x < 1 / 2) :
    centred x = x := by
  rw [centred, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, add_sub_cancel_right]

/-- `α₁ - 22/63 = 289/21483` lies strictly inside `(-1/2, 1/2)`, hence is `centred`-fixed. -/
private theorem centred_alpha1 : centred (alpha1 - 22 / 63) = 289 / 21483 := by
  have h : alpha1 - 22 / 63 = 289 / 21483 := by unfold alpha1; norm_num
  rw [h, centred_eq_self' (by norm_num) (by norm_num)]

/-- `821/1023 - 37/63 = 4624/21483` lies strictly inside `(-1/2, 1/2)`, hence is
`centred`-fixed. -/
private theorem centred_821 : centred (821 / 1023 - 37 / 63) = 4624 / 21483 := by
  have h : (821 : ℝ) / 1023 - 37 / 63 = 4624 / 21483 := by norm_num
  rw [h, centred_eq_self' (by norm_num) (by norm_num)]

/-! ## Closed forms of the arm angles at `b₂` -/

/-- The level-`n` arm-`A` angle, in closed form: the level-`0` value `22/63` plus the
geometrically shrinking correction `(289/21483)/64ⁿ`. -/
private theorem armA1_eq (n : ℕ) : armA1 n = 22 / 63 + (289 : ℝ) / 21483 / (64 : ℝ) ^ n := by
  have h : ((64 ^ n : ℕ) : ℝ) = (64 : ℝ) ^ n := by push_cast; ring
  rw [armA1, contract, centred_alpha1, h]
  rw [Int.fract_eq_self.mpr ⟨?_, ?_⟩]
  · positivity
  · have hn1 : (1 : ℝ) ≤ (64 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hle : (289 / 21483 : ℝ) / (64 : ℝ) ^ n ≤ 289 / 21483 := by
      rw [div_le_iff₀ (by positivity)]
      calc (289 : ℝ) / 21483 = 289 / 21483 * 1 := by ring
        _ ≤ 289 / 21483 * (64 : ℝ) ^ n := mul_le_mul_of_nonneg_left hn1 (by norm_num)
    have hlt : (22 : ℝ) / 63 + 289 / 21483 < 1 := by norm_num
    linarith

/-- The level-`n` arm-`C` angle, in closed form: `37/63` plus `(4624/21483)/64ⁿ`. -/
private theorem armC1_eq (n : ℕ) : armC1 n = 37 / 63 + (4624 : ℝ) / 21483 / (64 : ℝ) ^ n := by
  have h : ((64 ^ n : ℕ) : ℝ) = (64 : ℝ) ^ n := by push_cast; ring
  rw [armC1, contract, centred_821, h]
  rw [Int.fract_eq_self.mpr ⟨?_, ?_⟩]
  · positivity
  · have hn1 : (1 : ℝ) ≤ (64 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hle : (4624 / 21483 : ℝ) / (64 : ℝ) ^ n ≤ 4624 / 21483 := by
      rw [div_le_iff₀ (by positivity)]
      calc (4624 : ℝ) / 21483 = 4624 / 21483 * 1 := by ring
        _ ≤ 4624 / 21483 * (64 : ℝ) ^ n := mul_le_mul_of_nonneg_left hn1 (by norm_num)
    have hlt : (37 : ℝ) / 63 + 4624 / 21483 < 1 := by norm_num
    linarith

/-! ## The exact congruence -/

/-- `1024 · (22/63 + (289/21483)/64^{m+1}) = 357 + (37/63 + (4624/21483)/64^m)`: the two
exact identities `1024 · 22 = 63 · 357 + 37` and `1024 · 289 = 64 · 16 · 289 = 64 · 4624`,
after clearing the common factor `64^{m+1}`. -/
private theorem ten_mul_armA1 (m : ℕ) :
    1024 * (22 / 63 + (289 : ℝ) / 21483 / (64 : ℝ) ^ (m + 1))
      = (357 : ℝ) + (37 / 63 + (4624 : ℝ) / 21483 / (64 : ℝ) ^ m) := by
  rw [pow_succ]
  have h64m : ((64 : ℝ) ^ m) ≠ 0 := by positivity
  field_simp
  ring

/-- The tenth iterate of `T` on the arm-`A` angle: the integral part `357` is absorbed by
`Int.fract`, and the remaining angle `37/63 + (4624/21483)/64^m` already lies in `[0,1)`,
where it equals its own fractional part. -/
private theorem fract_ten_armA1 (m : ℕ) :
    Int.fract (1024 * (22 / 63 + (289 : ℝ) / 21483 / (64 : ℝ) ^ (m + 1)))
      = 37 / 63 + (4624 : ℝ) / 21483 / (64 : ℝ) ^ m := by
  rw [ten_mul_armA1 m, Int.fract_ofNat_add]
  rw [Int.fract_eq_self.mpr ⟨by positivity, ?_⟩]
  have hn1 : (1 : ℝ) ≤ (64 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hle : (4624 : ℝ) / 21483 / (64 : ℝ) ^ m ≤ 4624 / 21483 := by
    rw [div_le_iff₀ (by positivity)]
    calc (4624 : ℝ) / 21483 = 4624 / 21483 * 1 := by ring
      _ ≤ 4624 / 21483 * (64 : ℝ) ^ m := mul_le_mul_of_nonneg_left hn1 (by norm_num)
  have hlt : (37 : ℝ) / 63 + 4624 / 21483 < 1 := by norm_num
  linarith

/-! ## The statement -/

theorem T10_armA1 (n : ℕ) (hn : 1 ≤ n) :
    Work.EL.T^[10] (Work.ELNest.armA1 n) = Work.ELNest.armC1 (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Nat.succ_sub_one, T_iterate_ten, armA1_eq, armC1_eq]
    exact fract_ten_armA1 m

end Work.ELNest
