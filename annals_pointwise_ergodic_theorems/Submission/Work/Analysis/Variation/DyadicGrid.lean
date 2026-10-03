/-
# The dyadic grid on `[0,1]` and its arithmetic

This file sets up the vocabulary for `Work.Analysis.Variation.dyadicVariationLeGrid`: the
rounding `dyadPt l x = ⌊2 ^ l x⌋ / 2 ^ l` of a real number down to the dyadic grid of scale
`2 ^ (-l)`, the index `dyadQ l x = ⌊2 ^ l x⌋` of the dyadic cell containing `x`, the signed
increment `dyadJump h l m` of a function `h` across the level-`l` cell `[(m-1)/2^l, m/2^l]`
(killed for even `m`), and the `ℓ^r` norm `dyadGridLp r h l` of the level-`l` grid increments.

The arithmetic below is what a dyadic rounding argument needs: monotonicity of `dyadQ`,
`dyadPt l x ≤ x ≤ dyadPt l x + 2^{-l}` (so `dyadPt l x → x`), the floor-halving identity
`dyadQ (l+1) x / 2 = dyadQ l x`, and the bound `dyadQ l x < 2 ^ l + 1` for `x ≤ 1`.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal Topology
open Filter

namespace Work.Analysis.Variation

/-- The index of the dyadic cell of scale `2 ^ (-l)` containing `x`: `dyadQ l x = ⌊2 ^ l x⌋`. -/
noncomputable def dyadQ (l : ℕ) (x : ℝ) : ℕ := ⌊(2 : ℝ) ^ l * x⌋₊

/-- The point of the dyadic grid of scale `2 ^ (-l)` just below `x`:
`dyadPt l x = ⌊2 ^ l x⌋ / 2 ^ l`. -/
noncomputable def dyadPt (l : ℕ) (x : ℝ) : ℝ := (dyadQ l x : ℝ) / (2 : ℝ) ^ l

/-- The signed increment of `h` across the dyadic cell `[(m-1)/2^l, m/2^l]` of level `l` when `m`
is odd, and `0` for even `m` (so that only "right-hand children" of the dyadic tree contribute). -/
noncomputable def dyadJump (h : ℝ → ℂ) (l m : ℕ) : ℂ :=
  if Odd m then h ((m : ℝ) / (2 : ℝ) ^ l) - h (((m : ℝ) - 1) / (2 : ℝ) ^ l) else 0

/-- The `ℓ^r` norm of the grid increments of `h` at scale `2 ^ (-l)`. -/
noncomputable def dyadGridLp (r : ℝ) (h : ℝ → ℂ) (l : ℕ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ l),
      ‖h ((j : ℝ) / 2 ^ l) - h (((j : ℝ) - 1) / 2 ^ l)‖ₑ ^ r) ^ (1 / r)

lemma dyadQ_nonneg (l : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (2 : ℝ) ^ l * x :=
  mul_nonneg (pow_nonneg (by norm_num) l) hx

/-- `⌊2 ^ l x⌋ ≤ 2 ^ l x`. -/
lemma dyadQ_le_mul (l : ℕ) (x : ℝ) (hx : 0 ≤ x) : (dyadQ l x : ℝ) ≤ (2 : ℝ) ^ l * x :=
  Nat.floor_le (dyadQ_nonneg l x hx)

/-- `2 ^ l x < ⌊2 ^ l x⌋ + 1`. -/
lemma dyadQ_lt_mul_add (l : ℕ) (x : ℝ) : (2 : ℝ) ^ l * x < (dyadQ l x : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- Monotonicity of the cell index in the point. -/
lemma dyadQ_mono (l : ℕ) : Monotone (dyadQ l) := fun x y hxy =>
  Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (pow_nonneg (by norm_num) l))

/-- `dyadPt l x ≤ x`. -/
lemma dyadPt_le {l : ℕ} {x : ℝ} (hx : 0 ≤ x) : dyadPt l x ≤ x := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  rw [dyadPt, div_le_iff₀ hpos]
  calc (dyadQ l x : ℝ) ≤ (2 : ℝ) ^ l * x := dyadQ_le_mul l x hx
    _ = x * (2 : ℝ) ^ l := by ring

/-- `x - dyadPt l x ≤ 2 ^ (-l)`. -/
lemma dyadPt_sub_le (l : ℕ) (x : ℝ) : x - dyadPt l x ≤ 1 / (2 : ℝ) ^ l := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have h : x - dyadPt l x = ((2 : ℝ) ^ l * x - (dyadQ l x : ℝ)) / (2 : ℝ) ^ l := by
    rw [dyadPt]; field_simp
  rw [h, div_le_iff₀ hpos]
  have hlt : (2 : ℝ) ^ l * x < (dyadQ l x : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (1 : ℝ) / (2 : ℝ) ^ l * (2 : ℝ) ^ l = 1 := by
    field_simp
  rw [h2]
  linarith

lemma dyadPt_nonneg (l : ℕ) (x : ℝ) : 0 ≤ dyadPt l x :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The dyadic roundings of `x ≥ 0` converge to `x`. -/
lemma dyadPt_tendsto {x : ℝ} (hx : 0 ≤ x) : Tendsto (fun l : ℕ => dyadPt l x) atTop (𝓝 x) := by
  have h1 : Tendsto (fun l : ℕ => x - dyadPt l x) atTop (𝓝 0) := by
    refine squeeze_zero (f := fun l : ℕ => x - dyadPt l x) (g := fun l : ℕ => 1 / (2 : ℝ) ^ l)
      (fun l => sub_nonneg.mpr (dyadPt_le hx))
      (fun l => dyadPt_sub_le l x) ?_
    simpa only [one_div, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h2 : Tendsto (fun l : ℕ => x - (x - dyadPt l x)) atTop (𝓝 (x - 0)) :=
    tendsto_const_nhds.sub h1
  simpa using h2

/-- Floor-halving: `⌊2 ^ (l+1) x⌋ / 2 = ⌊2 ^ l x⌋`. -/
lemma dyadQ_succ_div (l : ℕ) (x : ℝ) : dyadQ (l + 1) x / 2 = dyadQ l x := by
  have key : ⌊(2 : ℝ) ^ l * x⌋₊ = ⌊(2 : ℝ) ^ (l + 1) * x⌋₊ / 2 := by
    have h := Nat.floor_div_natCast ((2 : ℝ) * ((2 : ℝ) ^ l * x)) 2
    simp only [Nat.cast_ofNat] at h
    have h1 : (2 : ℝ) * ((2 : ℝ) ^ l * x) / 2 = (2 : ℝ) ^ l * x := by ring
    rw [h1] at h
    have h2 : (2 : ℝ) ^ (l + 1) * x = 2 * ((2 : ℝ) ^ l * x) := by rw [pow_succ]; ring
    rw [← h2] at h
    exact h
  rw [dyadQ, dyadQ, ← key]

/-- For `x ≤ 1` the cell index of level `l` is at most `2 ^ l`. -/
lemma dyadQ_lt_two_pow_add_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (l : ℕ) :
    dyadQ l x < 2 ^ l + 1 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hle : (dyadQ l x : ℝ) ≤ (2 : ℝ) ^ l := by
    calc (dyadQ l x : ℝ) ≤ (2 : ℝ) ^ l * x := dyadQ_le_mul l x hx0
      _ ≤ (2 : ℝ) ^ l * 1 := mul_le_mul_of_nonneg_left hx1 h2pos.le
      _ = (2 : ℝ) ^ l := mul_one _
  have hlt : (dyadQ l x : ℝ) < ((2 ^ l + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hlt

/-- The level-`l` point `dyadPt l x` is the level-`(l+1)` grid point of index `2 * dyadQ l x`. -/
lemma dyadPt_eq_two_mul (l : ℕ) (x : ℝ) :
    dyadPt l x = ((2 * dyadQ l x : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1) := by
  rw [dyadPt, pow_succ]
  push_cast
  ring

/-- The enorm of a dyadic jump is at most the enorm of the corresponding grid increment. -/
lemma enorm_dyadJump_le (h : ℝ → ℂ) (l m : ℕ) :
    ‖dyadJump h l m‖ₑ ≤ ‖h ((m : ℝ) / 2 ^ l) - h (((m : ℝ) - 1) / 2 ^ l)‖ₑ := by
  rw [dyadJump]
  split_ifs with hm
  · exact le_of_eq rfl
  · simp

/-- For odd `m` the dyadic jump is the grid increment. -/
lemma dyadJump_eq_of_odd (h : ℝ → ℂ) (l m : ℕ) (hm : Odd m) :
    dyadJump h l m = h ((m : ℝ) / 2 ^ l) - h (((m : ℝ) - 1) / 2 ^ l) := by
  rw [dyadJump, if_pos hm]

/-- For even `m` the dyadic jump vanishes. -/
lemma dyadJump_eq_zero_of_even (h : ℝ → ℂ) (l m : ℕ) (hm : Even m) :
    dyadJump h l m = 0 := by
  rw [dyadJump, if_neg (Nat.not_odd_iff_even.mpr hm)]

end Work.Analysis.Variation
