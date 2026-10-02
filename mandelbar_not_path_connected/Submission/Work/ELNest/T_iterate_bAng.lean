/-
# `T_iterate_bAng`: the tenth iterate of the angle map on the `z₁`-nest angles

The angle-doubling map of the antiholomorphic quadratic family is
`T θ = -2θ mod 1 = Int.fract (-2 * θ)` (`Work.EL.T`).  The angles of the
`z₁`-nest of the equator-leak argument are the two sequences

* `bAng n  = α₁ − (α₁ − β₀)/1024ⁿ`   (close to the root angle `α₁ = 371/1023`),
* `bAng' n = α₂ + (β₀' − α₂)/1024ⁿ`  (close to the root angle `α₂ = 404/1023`),

of `Submission/Work/ELNest/Defs.lean`.  The nesting is produced by the degree-`1024`
map `F c = (T_c)^{10}`, whose action on rays is the tenth iterate `T^[10]` of `T`;
accordingly the level-`(n+1)` pair of each nest maps to the level-`n` pair:

    T^[10] (bAng (n+1)) = bAng n,      T^[10] (bAng' (n+1)) = bAng' n.

Both are pure arithmetic.  The proof has two halves.

* **Modulo `ℤ`.**  In the Böttcher coordinate the dynamics is `w ↦ conj w ^ 2`, so one step
  of `T` multiplies the angle by `-2` *modulo* `1`; iterating ten times,
  `T^[10] θ = fract ((-2)^10 θ) = fract (1024 θ)` (`T_iterate_succ` below, the `k + 1`-fold
  version of `Work.ELRig.T_iterate_eq_add_int` in the sharper form of an equality of
  fractional parts).
* **The exact congruence.**  Because `1024ⁿ⁺¹ = 1024ⁿ · 1024`,

      1024 · bAng (n+1) = 1024 α₁ − (α₁ − β₀)/1024ⁿ = bAng n + 1023 α₁ = bAng n + 371,

  and likewise `1024 · bAng' (n+1) = bAng' n + 1023 α₂ = bAng' n + 404`; the integer
  `371 = 1023·(371/1023)` resp. `404 = 1023·(404/1023)` disappears in `Int.fract`.
  What remains is `fract (bAng n) = bAng n`, i.e. the elementary bounds
  `β₀ ≤ bAng n ≤ α₁` and `α₂ ≤ bAng' n ≤ β₀'` (with `0 < β₀`, `α₁ < 1`, `0 < α₂`,
  `β₀' < 1`), which hold because `1024ⁿ ≥ 1` squeezes each nest angle between its
  level-`0` angle and the root angle it accumulates at.
-/
import Mathlib
import Submission.Work.ELNest.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate

namespace Work.ELNest

/-! ## The iterate `T^[k]` as a fractional part -/

/-- The `(n+1)`-fold iterate of the angle-doubling map `T θ = Int.fract (-2θ)` is the
fractional part of `(-2)^{n+1} θ`: the integer part produced at each step is absorbed
by `Int.fract` (`Int.fract_eq_fract`).  (The restriction `n + 1 ≥ 1` is genuine: for
`n = 0` steps one would need `fract θ = θ`, which is false in general.) -/
theorem T_iterate_succ (n : ℕ) (θ : ℝ) :
    Work.EL.T^[n + 1] θ = Int.fract (((-2 : ℝ) ^ (n + 1)) * θ) := by
  induction n with
  | zero => norm_num [Work.EL.T]
  | succ n ih =>
    have hstep : Work.EL.T^[n + 1 + 1] θ = Work.EL.T (Work.EL.T^[n + 1] θ) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep]
    show Int.fract (-2 * (Work.EL.T^[n + 1] θ)) = Int.fract (((-2 : ℝ) ^ (n + 1 + 1)) * θ)
    rw [ih]
    -- `fract (-2 * fract x) = fract (-2 * x)`: the two arguments differ by the integer
    -- `2 * ⌊x⌋`.
    have hshift : Int.fract ((-2 : ℝ) * Int.fract (((-2 : ℝ) ^ (n + 1)) * θ))
        = Int.fract ((-2 : ℝ) * (((-2 : ℝ) ^ (n + 1)) * θ)) := by
      rw [Int.fract_eq_fract]
      refine ⟨2 * ⌊((-2 : ℝ) ^ (n + 1)) * θ⌋, ?_⟩
      have h := Int.fract_sub_self (((-2 : ℝ) ^ (n + 1)) * θ)
      push_cast
      linarith
    rw [hshift]
    congr 1
    ring

/-- The tenth iterate of `T` is the fractional part of `1024 θ = (-2)^{10} θ`. -/
theorem T_iterate_ten (θ : ℝ) : Work.EL.T^[10] θ = Int.fract (1024 * θ) := by
  have h := T_iterate_succ 9 θ
  rw [h]
  norm_num

/-! ## The exact congruences of the nest angles -/

/-- Multiplying the level-`(n+1)` angle `bAng (n+1)` of the `z₁`-nest by `1024` gives the
level-`n` angle `bAng n` up to the integer `1023 α₁ = 371`. -/
theorem bAng_succ_mul (n : ℕ) : (1024 : ℝ) * bAng (n + 1) = bAng n + 371 := by
  have h : (1024 : ℝ) ≠ 0 := by norm_num
  have hp : (1024 : ℝ) ^ (n + 1) = 1024 ^ n * 1024 := pow_succ 1024 n
  simp only [bAng, alpha1, beta0, hp, div_mul_eq_div_div]
  field_simp
  ring

/-- Multiplying the level-`(n+1)` angle `bAng' (n+1)` of the `z₁`-nest by `1024` gives the
level-`n` angle `bAng' n` up to the integer `1023 α₂ = 404`. -/
theorem bAng'_succ_mul (n : ℕ) : (1024 : ℝ) * bAng' (n + 1) = bAng' n + 404 := by
  have h : (1024 : ℝ) ≠ 0 := by norm_num
  have hp : (1024 : ℝ) ^ (n + 1) = 1024 ^ n * 1024 := pow_succ 1024 n
  simp only [bAng', alpha2, beta0', hp, div_mul_eq_div_div]
  field_simp
  ring

/-! ## The elementary bounds on the nest angles -/

/-- The nest angles `bAng n` accumulate at `α₁` from below, starting at `β₀`. -/
theorem beta0_le_bAng (n : ℕ) : beta0 ≤ bAng n := by
  rw [bAng]
  have h0 : 0 ≤ alpha1 - beta0 := by unfold alpha1 beta0; norm_num
  have h1 : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h2 : (alpha1 - beta0) / (1024 : ℝ) ^ n ≤ alpha1 - beta0 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h0, h1]
  linarith

/-- The nest angles `bAng n` never exceed the root angle `α₁` they accumulate at. -/
theorem bAng_le_alpha1 (n : ℕ) : bAng n ≤ alpha1 := by
  rw [bAng]
  have h0 : 0 ≤ alpha1 - beta0 := by unfold alpha1 beta0; norm_num
  have h1 : 0 ≤ (alpha1 - beta0) / (1024 : ℝ) ^ n := div_nonneg h0 (by positivity)
  linarith

/-- The nest angles `bAng' n` accumulate at `α₂` from above, starting at `β₀'`. -/
theorem bAng'_le_beta0' (n : ℕ) : bAng' n ≤ beta0' := by
  rw [bAng']
  have h0 : 0 ≤ beta0' - alpha2 := by unfold beta0' alpha2; norm_num
  have h1 : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h2 : (beta0' - alpha2) / (1024 : ℝ) ^ n ≤ beta0' - alpha2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h0, h1]
  linarith

/-- The nest angles `bAng' n` never drop below the root angle `α₂` they accumulate at. -/
theorem alpha2_le_bAng' (n : ℕ) : alpha2 ≤ bAng' n := by
  rw [bAng']
  have h0 : 0 ≤ beta0' - alpha2 := by unfold beta0' alpha2; norm_num
  have h1 : 0 ≤ (beta0' - alpha2) / (1024 : ℝ) ^ n := div_nonneg h0 (by positivity)
  linarith

/-- Every `bAng n` lies in `(0, 1)`. -/
theorem bAng_pos (n : ℕ) : 0 < bAng n :=
  lt_of_lt_of_le (by unfold beta0; norm_num) (beta0_le_bAng n)

/-- Every `bAng n` lies in `(0, 1)`. -/
theorem bAng_lt_one (n : ℕ) : bAng n < 1 :=
  lt_of_le_of_lt (bAng_le_alpha1 n) (by unfold alpha1; norm_num)

/-- Every `bAng' n` lies in `(0, 1)`. -/
theorem bAng'_pos (n : ℕ) : 0 < bAng' n :=
  lt_of_lt_of_le (by unfold alpha2; norm_num) (alpha2_le_bAng' n)

/-- Every `bAng' n` lies in `(0, 1)`. -/
theorem bAng'_lt_one (n : ℕ) : bAng' n < 1 :=
  lt_of_le_of_lt (bAng'_le_beta0' n) (by unfold beta0'; norm_num)

/-- The fractional part of a nest angle situated in `[0, 1)` is the angle itself. -/
theorem fract_bAng (n : ℕ) : Int.fract (bAng n) = bAng n :=
  Int.fract_eq_self.mpr ⟨(bAng_pos n).le, bAng_lt_one n⟩

/-- The fractional part of a nest angle situated in `[0, 1)` is the angle itself. -/
theorem fract_bAng' (n : ℕ) : Int.fract (bAng' n) = bAng' n :=
  Int.fract_eq_self.mpr ⟨(bAng'_pos n).le, bAng'_lt_one n⟩

/-! ## The iterate of the nest angles -/

theorem T_iterate_bAng (n : ℕ) :
    Work.EL.T^[10] (Work.ELNest.bAng (n + 1)) = Work.ELNest.bAng n ∧
    Work.EL.T^[10] (Work.ELNest.bAng' (n + 1)) = Work.ELNest.bAng' n := by
  constructor
  · rw [T_iterate_ten, bAng_succ_mul, Int.fract_eq_iff]
    exact ⟨(bAng_pos n).le, bAng_lt_one n, 371, by push_cast; ring⟩
  · rw [T_iterate_ten, bAng'_succ_mul, Int.fract_eq_iff]
    exact ⟨(bAng'_pos n).le, bAng'_lt_one n, 404, by push_cast; ring⟩

end Work.ELNest
