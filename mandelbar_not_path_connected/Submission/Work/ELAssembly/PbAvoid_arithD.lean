/-
# `PbAvoid_arithD`: the rational arithmetic of `hcvD` (`NOTES_LEAD_mandelbar_pbavoid.md` §3.4)

The `b₂`-nest is the three-chain nest of arm pairs `Za n = (armA1 n, armA2 n)`,
`Zb n = (armB1 n, armB2 n)`, `Zc n = (armC1 n, armC2 n + 1)`, and the two conditions that the
`hcvD` certificate needs from pure rational arithmetic are

* **(W)** each wake arc `W_j = (wakeLo j, wakeHi j)` of the root portrait lies in the *far* arc
  `(p.1, p.2)` of the arm pair used at the orbit point `k = j + 1` of the `F6`-critical orbit:
  `W₀ ⊆ Za n`, `W₂ ⊆ Zb n`, `W₁, W₃, W₄ ⊆ Zc n` (`W = (215,281)/1023` and `W₃ = (860,1124)/1023`
  lie only in `Zc`'s far arc, `W₄ = (821,1349)/1023` is `Zc`'s far arc at `n = 0`);
* **(ND)** neither endpoint of the relevant arm pair has fractional part equal to one of the two
  portrait angles `T^j α₁`, `T^j α₂` of that pair — the degeneracies at `n = 0`
  (`Za 0 = P₀`, `Zb 0 = P₂`, `Zc 0 = P₄`) are precisely excluded by the `n ≥ 1` hypotheses.

## The mathematics

With `y = 64⁻ⁿ ∈ (0,1]` the `contract` definition gives the closed forms (`armChain_nest`)

| arm | closed form | range |
|---|---|---|
| `armA1 n` | `22/63 + (289/21483)·y` | `[22/63, α₁]`  (`= α₁` iff `n = 0`) |
| `armA2 n` | `25/63 - (41/21483)·y` | `[α₂, 25/63]`  (`= α₂` iff `n = 0`) |
| `armB1 n` | `25/63 + (1156/21483)·y` | `[25/63, 461/1023]` (`= 461/1023` iff `n = 0`) |
| `armB2 n` | `37/63 - (164/21483)·y` | `[593/1023, 37/63]` (`= 593/1023` iff `n = 0`) |
| `armC1 n` | `37/63 + (4624/21483)·y` | `[37/63, 821/1023]` (`= 821/1023` iff `n = 0`) |
| `armC2 n` | `22/63 - (656/21483)·y` | `[326/1023, 22/63]` (`= 326/1023` iff `n = 0`) |

so every arm angle lies in `(0,1)` (`Int.fract` of it is itself, and for `armC2` also
`Int.fract (armC2 n + 1) = armC2 n`), the `n = 0` equalities are exactly the cases excluded by
`1 ≤ n`, and the (W) statements are the endpoint comparisons

* `armA1 n ≤ α₁`, `α₂ ≤ armA2 n`; `armB1 n ≤ 461/1023`, `593/1023 ≤ armB2 n`;
* `armC1 n ≤ 821/1023 ≤ 860/1023` and `101/1023 ≤ 326/1023 ≤ armC2 n`;
* `armC1 n < 1 + 215/1023` and `1 + 281/1023 ≤ 1 + armC2 n`.

The (W) conjuncts are consequences of the closed forms through the cyclic-arc transfer lemma
`pbD_inArc_of_lift`: given `lo < hi` with `arcLen lo hi = hi - lo`, if
`hi + m ≤ p + arcLen p q` and `p ≤ lo + m` then the open arc `(lo,hi)` lies in the open arc
`(p,q)`; apply it to `lo, hi = wakeLo j, wakeHi j` and the arm pair of the row, with the lift
`m = 1` for `W₁` and `m = 0` otherwise.

The (ND) conjuncts are the strict versions of the same endpoint comparisons, together with the
evaluation of the portrait angles by `norm_num`
(`T^[1] α = (281,215)/1023`, `T^[2] α = (461,593)/1023`, `T^[3] α = (101,860)/1023`,
`T^[4] α = (821,326)/1023`, `Work.EL.T θ = Int.fract (-2θ)`).
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## The cyclic arc: transfer along a lift -/

/-- `InArc` only sees its angle modulo `1`. -/
theorem pbD_inArc_add_int (θ a b : ℝ) (k : ℤ) :
    Work.EL.InArc θ a b ↔ Work.EL.InArc (θ + (k : ℝ)) a b := by
  unfold Work.EL.InArc
  rw [show θ + (k : ℝ) - a = (θ - a) + (k : ℝ) by ring, Int.fract_add_intCast]

/-- `arcLen a b` is the difference when the difference is already a fractional part. -/
theorem pbD_arcLen_eq_sub {a b : ℝ} (h0 : 0 ≤ b - a) (h1 : b - a < 1) :
    Work.EL.arcLen a b = b - a := by
  rw [Work.EL.arcLen, Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- **The cyclic-arc transfer.**  If the *unwrapped* interval `[lo + m, hi + m]` of length
`arcLen lo hi = hi - lo` sits inside the unwrapped interval `[p, p + arcLen p q]`, then the open
cyclic arc `(lo, hi)` lies in the open cyclic arc `(p, q)`. -/
theorem pbD_inArc_of_lift {lo hi p q : ℝ} (m : ℤ)
    (hlo : Work.EL.arcLen lo hi = hi - lo)
    (hp : p ≤ lo + (m : ℝ)) (hq : hi + (m : ℝ) ≤ p + Work.EL.arcLen p q) :
    ∀ θ : ℝ, Work.EL.InArc θ lo hi → Work.EL.InArc θ p q := by
  intro θ hθ
  set θ' : ℝ := θ - ((⌊θ - lo⌋ - m : ℤ) : ℝ) with hθ'
  have hθ'eq : θ' = lo + (m : ℝ) + Int.fract (θ - lo) := by
    rw [hθ']
    have h := Int.fract_add_floor (θ - lo)
    push_cast
    linarith
  have hf_lt : Int.fract (θ - lo) < hi - lo := by rw [← hlo]; exact hθ.2
  have hp' : p < θ' := by rw [hθ'eq]; linarith [hθ.1]
  have hq' : θ' < p + Work.EL.arcLen p q := by rw [hθ'eq]; linarith
  have hself : Int.fract (θ' - p) = θ' - p := by
    rw [Int.fract_eq_self]
    exact ⟨le_of_lt (sub_pos.mpr hp'), by have := Work.EL.arcLen_lt_one p q; linarith⟩
  have hgoal : Work.EL.InArc θ' p q := by
    rw [Work.EL.InArc, hself]
    exact ⟨sub_pos.mpr hp', by linarith⟩
  have hθeq : θ = θ' + ((⌊θ - lo⌋ - m : ℤ) : ℝ) := by rw [hθ']; ring
  rw [hθeq]
  exact (pbD_inArc_add_int θ' p q _).mp hgoal

/-! ## The six arm angles: bounds and arc lengths

All are read off the closed forms `armA1_closed`, …, `armC2_closed` of
`Submission.Work.ELNest.armChain_nest` with `y = 64⁻ⁿ ∈ (0,1]`. -/

/-- `armA1 n ∈ [22/63, α₁]`. -/
theorem pbD_armA1_bounds (n : ℕ) :
    (22:ℝ)/63 ≤ Work.ELNest.armA1 n ∧ Work.ELNest.armA1 n ≤ (371:ℝ)/1023 := by
  rw [Work.ELNest.armA1_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 289/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (371:ℝ)/1023 = 22/63 + 289/21483 := by norm_num
  constructor <;> linarith

/-- `armA2 n ∈ [α₂, 25/63]`. -/
theorem pbD_armA2_bounds (n : ℕ) :
    (404:ℝ)/1023 ≤ Work.ELNest.armA2 n ∧ Work.ELNest.armA2 n ≤ 25/63 := by
  rw [Work.ELNest.armA2_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 41/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (404:ℝ)/1023 = 25/63 - 41/21483 := by norm_num
  constructor <;> linarith

/-- `armB1 n ∈ [25/63, 461/1023]`. -/
theorem pbD_armB1_bounds (n : ℕ) :
    (25:ℝ)/63 ≤ Work.ELNest.armB1 n ∧ Work.ELNest.armB1 n ≤ (461:ℝ)/1023 := by
  rw [Work.ELNest.armB1_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 1156/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (461:ℝ)/1023 = 25/63 + 1156/21483 := by norm_num
  constructor <;> linarith

/-- `armB2 n ∈ [593/1023, 37/63]`. -/
theorem pbD_armB2_bounds (n : ℕ) :
    (593:ℝ)/1023 ≤ Work.ELNest.armB2 n ∧ Work.ELNest.armB2 n ≤ 37/63 := by
  rw [Work.ELNest.armB2_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 164/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (593:ℝ)/1023 = 37/63 - 164/21483 := by norm_num
  constructor <;> linarith

/-- `armC1 n ∈ [37/63, 821/1023]`. -/
theorem pbD_armC1_bounds (n : ℕ) :
    (37:ℝ)/63 ≤ Work.ELNest.armC1 n ∧ Work.ELNest.armC1 n ≤ (821:ℝ)/1023 := by
  rw [Work.ELNest.armC1_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (4624:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 4624/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (821:ℝ)/1023 = 37/63 + 4624/21483 := by norm_num
  constructor <;> linarith

/-- `armC2 n ∈ [326/1023, 22/63]`. -/
theorem pbD_armC2_bounds (n : ℕ) :
    (326:ℝ)/1023 ≤ Work.ELNest.armC2 n ∧ Work.ELNest.armC2 n ≤ 22/63 := by
  rw [Work.ELNest.armC2_closed n]
  have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : (656:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 656/21483 :=
    mul_le_of_le_one_right (by norm_num) hy1
  have h : (326:ℝ)/1023 = 22/63 - 656/21483 := by norm_num
  constructor <;> linarith

/-- For `n ≥ 1`, `64⁻ⁿ ≤ 1/64`. -/
theorem pbD_inv_pow64_le (n : ℕ) (hn : 1 ≤ n) : ((64:ℝ)^n)⁻¹ ≤ 1/64 := by
  rw [one_div, inv_le_inv₀ (by positivity) (by norm_num)]
  calc (64:ℝ) = (64:ℝ)^1 := by rw [pow_one]
    _ ≤ (64:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn

/-- For `n ≥ 1`, `armA1 n < α₁` strictly. -/
theorem pbD_armA1_lt (n : ℕ) (hn : 1 ≤ n) :
    Work.ELNest.armA1 n < (371:ℝ)/1023 := by
  rw [Work.ELNest.armA1_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (289:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 289/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (289:ℝ)/21483 * (1/64) < 289/21483 := by norm_num
  have h : (371:ℝ)/1023 = 22/63 + 289/21483 := by norm_num
  linarith

/-- For `n ≥ 1`, `α₂ < armA2 n` strictly. -/
theorem pbD_armA2_gt (n : ℕ) (hn : 1 ≤ n) :
    (404:ℝ)/1023 < Work.ELNest.armA2 n := by
  rw [Work.ELNest.armA2_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (41:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 41/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (41:ℝ)/21483 * (1/64) < 41/21483 := by norm_num
  have h : (404:ℝ)/1023 = 25/63 - 41/21483 := by norm_num
  linarith

/-- For `n ≥ 1`, `armB1 n < 461/1023` strictly. -/
theorem pbD_armB1_lt (n : ℕ) (hn : 1 ≤ n) :
    Work.ELNest.armB1 n < (461:ℝ)/1023 := by
  rw [Work.ELNest.armB1_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (1156:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 1156/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (1156:ℝ)/21483 * (1/64) < 1156/21483 := by norm_num
  have h : (461:ℝ)/1023 = 25/63 + 1156/21483 := by norm_num
  linarith

/-- For `n ≥ 1`, `593/1023 < armB2 n` strictly. -/
theorem pbD_armB2_gt (n : ℕ) (hn : 1 ≤ n) :
    (593:ℝ)/1023 < Work.ELNest.armB2 n := by
  rw [Work.ELNest.armB2_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (164:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 164/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (164:ℝ)/21483 * (1/64) < 164/21483 := by norm_num
  have h : (593:ℝ)/1023 = 37/63 - 164/21483 := by norm_num
  linarith

/-- For `n ≥ 1`, `armC1 n < 821/1023` strictly. -/
theorem pbD_armC1_lt (n : ℕ) (hn : 1 ≤ n) :
    Work.ELNest.armC1 n < (821:ℝ)/1023 := by
  rw [Work.ELNest.armC1_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (4624:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 4624/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (4624:ℝ)/21483 * (1/64) < 4624/21483 := by norm_num
  have h : (821:ℝ)/1023 = 37/63 + 4624/21483 := by norm_num
  linarith

/-- For `n ≥ 1`, `326/1023 < armC2 n` strictly. -/
theorem pbD_armC2_gt (n : ℕ) (hn : 1 ≤ n) :
    (326:ℝ)/1023 < Work.ELNest.armC2 n := by
  rw [Work.ELNest.armC2_closed n]
  have hy : ((64:ℝ)^n)⁻¹ ≤ 1/64 := pbD_inv_pow64_le n hn
  have h2 : (656:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 656/21483 * (1/64) :=
    mul_le_mul_of_nonneg_left hy (by norm_num)
  have h3 : (656:ℝ)/21483 * (1/64) < 656/21483 := by norm_num
  have h : (326:ℝ)/1023 = 22/63 - 656/21483 := by norm_num
  linarith

/-- The unwrapped arc `(armA1 n, armA2 n)` has length `armA2 n - armA1 n`. -/
theorem pbD_arcLen_armA (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armA1 n) (Work.ELNest.armA2 n)
      = Work.ELNest.armA2 n - Work.ELNest.armA1 n := by
  refine pbD_arcLen_eq_sub ?_ ?_
  · rw [Work.ELNest.armA1_closed n, Work.ELNest.armA2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h2 : (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 330/21483 :=
      mul_le_of_le_one_right (by norm_num) hy1
    linarith
  · rw [Work.ELNest.armA1_closed n, Work.ELNest.armA2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have h : (0:ℝ) ≤ (330:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by positivity
    linarith

/-- The unwrapped arc `(armB1 n, armB2 n)` has length `armB2 n - armB1 n`. -/
theorem pbD_arcLen_armB (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armB1 n) (Work.ELNest.armB2 n)
      = Work.ELNest.armB2 n - Work.ELNest.armB1 n := by
  refine pbD_arcLen_eq_sub ?_ ?_
  · rw [Work.ELNest.armB1_closed n, Work.ELNest.armB2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h2 : (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 1320/21483 :=
      mul_le_of_le_one_right (by norm_num) hy1
    linarith
  · rw [Work.ELNest.armB1_closed n, Work.ELNest.armB2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have h : (0:ℝ) ≤ (1320:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by positivity
    linarith

/-- The unwrapped arc `(armC1 n, armC2 n + 1)` has length `armC2 n + 1 - armC1 n`. -/
theorem pbD_arcLen_armC (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1)
      = Work.ELNest.armC2 n + 1 - Work.ELNest.armC1 n := by
  refine pbD_arcLen_eq_sub ?_ ?_
  · rw [Work.ELNest.armC1_closed n, Work.ELNest.armC2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h2 : (5280:ℝ)/21483 * ((64:ℝ)^n)⁻¹ ≤ 5280/21483 :=
      mul_le_of_le_one_right (by norm_num) hy1
    linarith
  · rw [Work.ELNest.armC1_closed n, Work.ELNest.armC2_closed n]
    have hy0 : (0:ℝ) ≤ ((64:ℝ)^n)⁻¹ := by positivity
    have h : (0:ℝ) ≤ (5280:ℝ)/21483 * ((64:ℝ)^n)⁻¹ := by positivity
    linarith

/-! ## (W): the five wake arcs lie in the far arcs of the arm pairs -/

/-- `W₀ = (α₁, α₂) ⊆ (armA1 n, armA2 n)`. -/
theorem pbD_W_wake0 (n : ℕ) : ∀ θ : ℝ,
    Work.EL.InArc θ (Work.EL.wakeLo 0) (Work.EL.wakeHi 0) →
      Work.EL.InArc θ (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) := by
  refine pbD_inArc_of_lift 0 ?_ ?_ ?_
  · exact pbD_arcLen_eq_sub (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
      (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
  · rw [show Work.EL.wakeLo 0 = (371:ℝ)/1023 by norm_num [Work.EL.wakeLo]]
    push_cast
    linarith [pbD_armA1_bounds n]
  · rw [pbD_arcLen_armA n, show Work.EL.wakeHi 0 = (404:ℝ)/1023 by norm_num [Work.EL.wakeHi]]
    push_cast
    linarith [pbD_armA2_bounds n]

/-- `W₂ = P₂ = (461, 593)/1023 ⊆ (armB1 n, armB2 n)`. -/
theorem pbD_W_wake2 (n : ℕ) : ∀ θ : ℝ,
    Work.EL.InArc θ (Work.EL.wakeLo 2) (Work.EL.wakeHi 2) →
      Work.EL.InArc θ (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) := by
  refine pbD_inArc_of_lift 0 ?_ ?_ ?_
  · exact pbD_arcLen_eq_sub (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
      (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
  · rw [show Work.EL.wakeLo 2 = (461:ℝ)/1023 by norm_num [Work.EL.wakeLo]]
    push_cast
    linarith [pbD_armB1_bounds n]
  · rw [pbD_arcLen_armB n, show Work.EL.wakeHi 2 = (593:ℝ)/1023 by norm_num [Work.EL.wakeHi]]
    push_cast
    linarith [pbD_armB2_bounds n]

/-- `W₁ = (215, 281)/1023`, `W₃ = (860, 1124)/1023` and `W₄ = (821, 1349)/1023` all lie in the far
arc `(armC1 n, armC2 n + 1)` of `Zc n`; the lift is `m = 1` for `W₁` (its endpoint `281/1023` is
*below* `armC2 n`) and `m = 0` for `W₃` and `W₄`. -/
theorem pbD_W_wakeC (n j : ℕ) (hj : j = 1 ∨ j = 3 ∨ j = 4) : ∀ θ : ℝ,
    Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j) →
      Work.EL.InArc θ (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1) := by
  rcases hj with rfl | rfl | rfl
  · refine pbD_inArc_of_lift 1 ?_ ?_ ?_
    · exact pbD_arcLen_eq_sub (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
        (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
    · rw [show Work.EL.wakeLo 1 = (215:ℝ)/1023 by norm_num [Work.EL.wakeLo]]
      push_cast
      linarith [pbD_armC1_bounds n]
    · rw [pbD_arcLen_armC n, show Work.EL.wakeHi 1 = (281:ℝ)/1023 by norm_num [Work.EL.wakeHi]]
      push_cast
      linarith [pbD_armC2_bounds n]
  · refine pbD_inArc_of_lift 0 ?_ ?_ ?_
    · exact pbD_arcLen_eq_sub (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
        (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
    · rw [show Work.EL.wakeLo 3 = (860:ℝ)/1023 by norm_num [Work.EL.wakeLo]]
      push_cast
      linarith [pbD_armC1_bounds n]
    · rw [pbD_arcLen_armC n, show Work.EL.wakeHi 3 = (1124:ℝ)/1023 by norm_num [Work.EL.wakeHi]]
      push_cast
      linarith [pbD_armC2_bounds n]
  · refine pbD_inArc_of_lift 0 ?_ ?_ ?_
    · exact pbD_arcLen_eq_sub (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
        (by norm_num [Work.EL.wakeLo, Work.EL.wakeHi])
    · rw [show Work.EL.wakeLo 4 = (821:ℝ)/1023 by norm_num [Work.EL.wakeLo]]
      push_cast
      linarith [pbD_armC1_bounds n]
    · rw [pbD_arcLen_armC n, show Work.EL.wakeHi 4 = (1349:ℝ)/1023 by norm_num [Work.EL.wakeHi]]
      push_cast
      linarith [pbD_armC2_bounds n]

/-! ## (ND): the arm angles against the portrait angles

The portrait angles as evaluated by `norm_num`, and the two `Int.fract` normal forms. -/

theorem pbD_T0_alpha1 : Work.EL.T^[0] Work.EL.alpha1 = (371:ℝ)/1023 := by
  rw [Function.iterate_zero_apply, Work.EL.alpha1]

theorem pbD_T0_alpha2 : Work.EL.T^[0] Work.EL.alpha2 = (404:ℝ)/1023 := by
  rw [Function.iterate_zero_apply, Work.EL.alpha2]

theorem pbD_T1_alpha1 : Work.EL.T^[1] Work.EL.alpha1 = (281:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T1_alpha2 : Work.EL.T^[1] Work.EL.alpha2 = (215:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T2_alpha1 : Work.EL.T^[2] Work.EL.alpha1 = (461:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T2_alpha2 : Work.EL.T^[2] Work.EL.alpha2 = (593:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T3_alpha1 : Work.EL.T^[3] Work.EL.alpha1 = (101:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T3_alpha2 : Work.EL.T^[3] Work.EL.alpha2 = (860:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T4_alpha1 : Work.EL.T^[4] Work.EL.alpha1 = (821:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

theorem pbD_T4_alpha2 : Work.EL.T^[4] Work.EL.alpha2 = (326:ℝ)/1023 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

/-- `Int.fract` is the identity on `(0,1)`. -/
theorem pbD_fract_eq_self {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : Int.fract x = x :=
  Int.fract_eq_self.mpr ⟨le_of_lt h0, h1⟩

/-- `Int.fract (x + 1) = x` for `x ∈ (0,1)`. -/
theorem pbD_fract_add_one {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : Int.fract (x + 1) = x := by
  rw [show x + 1 = x + ((1:ℤ):ℝ) by push_cast; ring, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨le_of_lt h0, h1⟩

/-- **(ND), arm `A`**: for `n ≥ 1`, neither `armA1 n` nor `armA2 n` has fractional part equal to
`α₁ = T^[0] α₁` or `α₂ = T^[0] α₂`. -/
theorem pbD_ND_A (n : ℕ) (hn : 1 ≤ n) :
    (Int.fract (Work.ELNest.armA1 n) ≠ (Work.EL.T^[0] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armA1 n) ≠ (Work.EL.T^[0] Work.EL.alpha2) ∧
      Int.fract (Work.ELNest.armA2 n) ≠ (Work.EL.T^[0] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armA2 n) ≠ (Work.EL.T^[0] Work.EL.alpha2)) := by
  obtain ⟨ha1lo, ha1hi⟩ := pbD_armA1_bounds n
  obtain ⟨ha2lo, ha2hi⟩ := pbD_armA2_bounds n
  have ha1lt := pbD_armA1_lt n hn
  have ha2gt := pbD_armA2_gt n hn
  have f1 : Int.fract (Work.ELNest.armA1 n) = Work.ELNest.armA1 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  have f2 : Int.fract (Work.ELNest.armA2 n) = Work.ELNest.armA2 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  rw [pbD_T0_alpha1, pbD_T0_alpha2, f1, f2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **(ND), arm `B`**: for `n ≥ 1`, neither `armB1 n` nor `armB2 n` has fractional part equal to
`T^[2] α₁ = 461/1023` or `T^[2] α₂ = 593/1023`. -/
theorem pbD_ND_B (n : ℕ) (hn : 1 ≤ n) :
    (Int.fract (Work.ELNest.armB1 n) ≠ (Work.EL.T^[2] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armB1 n) ≠ (Work.EL.T^[2] Work.EL.alpha2) ∧
      Int.fract (Work.ELNest.armB2 n) ≠ (Work.EL.T^[2] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armB2 n) ≠ (Work.EL.T^[2] Work.EL.alpha2)) := by
  obtain ⟨hb1lo, hb1hi⟩ := pbD_armB1_bounds n
  obtain ⟨hb2lo, hb2hi⟩ := pbD_armB2_bounds n
  have hb1lt := pbD_armB1_lt n hn
  have hb2gt := pbD_armB2_gt n hn
  have f1 : Int.fract (Work.ELNest.armB1 n) = Work.ELNest.armB1 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  have f2 : Int.fract (Work.ELNest.armB2 n) = Work.ELNest.armB2 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  rw [pbD_T2_alpha1, pbD_T2_alpha2, f1, f2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **(ND), arm `C` vs `P₁`**: for every `n`, neither `armC1 n` nor `armC2 n` is `T^[1] α₁ = 281/1023`
or `T^[1] α₂ = 215/1023`. -/
theorem pbD_ND_C1 (n : ℕ) :
    (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[1] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[1] Work.EL.alpha2) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[1] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[1] Work.EL.alpha2)) := by
  obtain ⟨hc1lo, hc1hi⟩ := pbD_armC1_bounds n
  obtain ⟨hc2lo, hc2hi⟩ := pbD_armC2_bounds n
  have f1 : Int.fract (Work.ELNest.armC1 n) = Work.ELNest.armC1 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  have f2 : Int.fract (Work.ELNest.armC2 n + 1) = Work.ELNest.armC2 n :=
    pbD_fract_add_one (by linarith) (by linarith)
  rw [pbD_T1_alpha1, pbD_T1_alpha2, f1, f2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **(ND), arm `C` vs `P₃`**: for every `n`, neither `armC1 n` nor `armC2 n` is `T^[3] α₁ = 101/1023`
or `T^[3] α₂ = 860/1023`. -/
theorem pbD_ND_C3 (n : ℕ) :
    (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[3] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[3] Work.EL.alpha2) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[3] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[3] Work.EL.alpha2)) := by
  obtain ⟨hc1lo, hc1hi⟩ := pbD_armC1_bounds n
  obtain ⟨hc2lo, hc2hi⟩ := pbD_armC2_bounds n
  have f1 : Int.fract (Work.ELNest.armC1 n) = Work.ELNest.armC1 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  have f2 : Int.fract (Work.ELNest.armC2 n + 1) = Work.ELNest.armC2 n :=
    pbD_fract_add_one (by linarith) (by linarith)
  rw [pbD_T3_alpha1, pbD_T3_alpha2, f1, f2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **(ND), arm `C` vs `P₄`**: for `n ≥ 1`, neither `armC1 n` nor `armC2 n` is `T^[4] α₁ = 821/1023`
or `T^[4] α₂ = 326/1023` (these are attained at `n = 0`). -/
theorem pbD_ND_C4 (n : ℕ) (hn : 1 ≤ n) :
    (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[4] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[4] Work.EL.alpha2) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[4] Work.EL.alpha1) ∧
      Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[4] Work.EL.alpha2)) := by
  obtain ⟨hc1lo, hc1hi⟩ := pbD_armC1_bounds n
  obtain ⟨hc2lo, hc2hi⟩ := pbD_armC2_bounds n
  have hc1lt := pbD_armC1_lt n hn
  have hc2gt := pbD_armC2_gt n hn
  have f1 : Int.fract (Work.ELNest.armC1 n) = Work.ELNest.armC1 n :=
    pbD_fract_eq_self (by linarith) (by linarith)
  have f2 : Int.fract (Work.ELNest.armC2 n + 1) = Work.ELNest.armC2 n :=
    pbD_fract_add_one (by linarith) (by linarith)
  rw [pbD_T4_alpha1, pbD_T4_alpha2, f1, f2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The rational arithmetic of `hcvD`** (`NOTES_LEAD_mandelbar_pbavoid.md` §3.4, "Z*_W, Z*_ND"),
bundled as one conjunction: the wake arcs `W_0 ⊆` the far arc of `Za n`, `W_2 ⊆` that of `Zb n`,
`W_1, W_3, W_4 ⊆` the far arc of `Zc n` (lifts `m = 0,0,1,0,0`), and the non-degeneracy of the
arm angles against the portrait angles `T^j αᵢ`: `Za n` (n ≥ 1) vs `P_0`, `Zb n` (n ≥ 1) vs `P_2`,
`Zc n` (n ≥ 1) vs `P_4`, and `Zc n` (all n) vs `P_1` and `P_3`.  All the arm angles are the closed
forms `armChain_nest` (`armA1 n = 22/63 + (289/21483)·64⁻ⁿ`, …, `armC2 n = 22/63 - (656/21483)·64⁻ⁿ`),
affine in `y = 64⁻ⁿ ∈ (0,1]` (`y ≤ 1/64` for `n ≥ 1`), and `T^j αᵢ` is evaluated by `norm_num`
(281,215 | 461,593 | 101,860 | 821,326 over 1023). -/
theorem PbAvoid_arithD :
    (∀ n : ℕ, ∀ θ : ℝ, Work.EL.InArc θ (Work.EL.wakeLo 0) (Work.EL.wakeHi 0) →
      Work.EL.InArc θ (Work.ELNest.armA1 n) (Work.ELNest.armA2 n)) ∧
    (∀ n : ℕ, ∀ θ : ℝ, Work.EL.InArc θ (Work.EL.wakeLo 2) (Work.EL.wakeHi 2) →
      Work.EL.InArc θ (Work.ELNest.armB1 n) (Work.ELNest.armB2 n)) ∧
    (∀ n j : ℕ, (j = 1 ∨ j = 3 ∨ j = 4) → ∀ θ : ℝ,
      Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j) →
        Work.EL.InArc θ (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (Int.fract (Work.ELNest.armA1 n) ≠ (Work.EL.T^[0] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armA1 n) ≠ (Work.EL.T^[0] Work.EL.alpha2) ∧
        Int.fract (Work.ELNest.armA2 n) ≠ (Work.EL.T^[0] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armA2 n) ≠ (Work.EL.T^[0] Work.EL.alpha2))) ∧
    (∀ n : ℕ, 1 ≤ n →
      (Int.fract (Work.ELNest.armB1 n) ≠ (Work.EL.T^[2] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armB1 n) ≠ (Work.EL.T^[2] Work.EL.alpha2) ∧
        Int.fract (Work.ELNest.armB2 n) ≠ (Work.EL.T^[2] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armB2 n) ≠ (Work.EL.T^[2] Work.EL.alpha2))) ∧
    (∀ n : ℕ,
      (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[1] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[1] Work.EL.alpha2) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[1] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[1] Work.EL.alpha2))) ∧
    (∀ n : ℕ,
      (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[3] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[3] Work.EL.alpha2) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[3] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[3] Work.EL.alpha2))) ∧
    (∀ n : ℕ, 1 ≤ n →
      (Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[4] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC1 n) ≠ (Work.EL.T^[4] Work.EL.alpha2) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[4] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.armC2 n + 1) ≠ (Work.EL.T^[4] Work.EL.alpha2))) :=
  ⟨pbD_W_wake0, pbD_W_wake2, fun n j hj => pbD_W_wakeC n j hj,
    fun n hn => pbD_ND_A n hn, fun n hn => pbD_ND_B n hn,
    pbD_ND_C1, pbD_ND_C3, fun n hn => pbD_ND_C4 n hn⟩

end Work.ELAssembly
