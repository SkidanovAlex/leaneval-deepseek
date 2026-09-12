import Mathlib
import Submission.Section5DCount

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option linter.dupNamespace false

noncomputable section

/-!
# Section 5d: `cor: permutations`

Given a unit incompressible vector `x` with threshold `th ∈ [T/2, T]` and an
integer vector `spv` within sup-distance `1` of `(√n/th)·x`, the special
permutations lemma (`Commons.LinearAlgebra.Net.spread_permutations`)
produces a permutation after which the reordered `spv` lies in the
coordinate family `Acoord n δ ν T`.
-/

open scoped BigOperators ENNReal

namespace Submission.Section5D

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Commons.LinearAlgebra.Net

/-! ## small helpers on squares and powers of two -/

/-- nonnegative comparison from squares. -/
lemma nonneg_le_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have habs : |a| ≤ |b| := (sq_le_sq.mp h)
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at habs

/-- `((2)^((j+1)/2))² = 2^(j+1)`. -/
lemma rpow_sq_half (j : ℕ) :
    ((2 : ℝ) ^ (((j : ℝ) + 1) / 2)) ^ 2 = (2 : ℝ) ^ ((j : ℝ) + 1) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (((j : ℝ) + 1) / 2)) 2]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- `2^{(j:ℝ)+1} = 2·2^j`. -/
lemma two_rpow_add_one (j : ℕ) : (2 : ℝ) ^ ((j : ℝ) + 1) = 2 * (2 : ℝ) ^ j := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h1 : (2 : ℝ) ^ (1 : ℝ) = 2 := by
    rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  rw [h1]
  have hj : (2 : ℝ) ^ (j : ℝ) = (2 : ℝ) ^ j := by rw [Real.rpow_natCast]
  rw [hj]
  ring

/-- `2^{(j+1)/2} ≤ 2·√r` from `2^j ≤ 2r` (j ≥ 1). -/
lemma two_rpow_half_le_two_sqrt {j : ℕ} (hj : 1 ≤ j) {r : ℝ} (hr0 : 0 ≤ r)
    (h : (2 : ℝ) ^ j ≤ 2 * r) :
    (2 : ℝ) ^ (((j : ℝ) + 1) / 2) ≤ 2 * Real.sqrt r := by
  have hsq := rpow_sq_half j
  have hsq2 : (2 * Real.sqrt r) ^ 2 = 4 * r := by
    rw [mul_pow, Real.sq_sqrt hr0]
    norm_num
  apply nonneg_le_of_sq_le (by positivity) (by positivity)
  rw [hsq, two_rpow_add_one, hsq2]
  nlinarith [h]

/-- `2^{(j+1)/2} ≤ 2·√(δn/pos)` from `2^{j−1} ≤ δn/pos`, `j ≥ 1`. -/
lemma shell_half_bound {j : ℕ} (hj : 1 ≤ j) {δ : ℝ} {n pos : ℕ} (hδ0 : 0 < δ)
    (hpos0 : (0 : ℝ) < (pos : ℝ))
    (h : (2 : ℝ) ^ (j - 1) ≤ δ * (n : ℝ) / (pos : ℝ)) :
    (2 : ℝ) ^ (((j : ℝ) + 1) / 2) ≤ 2 * Real.sqrt (δ * (n : ℝ) / (pos : ℝ)) := by
  let r : ℝ := δ * (n : ℝ) / (pos : ℝ)
  have hd0 : 0 ≤ r := by positivity
  apply two_rpow_half_le_two_sqrt hj hd0
  have hmul : 2 * (2 : ℝ) ^ (j - 1) ≤ 2 * r := mul_le_mul_of_nonneg_left h (by norm_num)
  have hr : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    have hjn : (j : ℕ) = (j - 1) + 1 := (Nat.sub_add_cancel hj).symm
    conv_lhs => rw [hjn]
    rw [pow_succ]
    ring
  rwa [hr]

/-- `n < 2^n` for `1 ≤ n`. -/
lemma n_lt_two_pow (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) < (2 : ℝ) ^ n := by
  have hnat : n < 2 ^ n := by
    refine Nat.le_induction ?_ ?_ n hn
    · norm_num
    · intro m hm ih
      rw [pow_succ]
      have hA : 1 ≤ 2 ^ m := by
        have hpow : 2 ^ 1 ≤ 2 ^ m := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm
        norm_num at hpow ⊢
        omega
      omega
  exact_mod_cast hnat

/-! ## the shell lemma -/

/-- for a small position `pos ≥ 2` with `pos ≤ δn`, a dyadic shell `j` with
`1 ≤ j`, `2^j ≤ δn`, `δn/pos < 2^j` and `2^{j−1} ≤ δn/pos`. -/
lemma shell_of_pos {n pos : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn1 : 1 ≤ n)
    (hpos2 : 2 ≤ pos) (hposδn : (pos : ℝ) ≤ δ * (n : ℝ)) :
    ∃ j : ℕ, 1 ≤ j ∧
      (2 : ℝ) ^ j ≤ δ * (n : ℝ) ∧
      δ * (n : ℝ) / (pos : ℝ) < (2 : ℝ) ^ j ∧
      (2 : ℝ) ^ (j - 1) ≤ δ * (n : ℝ) / (pos : ℝ) := by
  let P (j : ℕ) : Prop := δ * (n : ℝ) / (pos : ℝ) < (2 : ℝ) ^ j
  have hposR : (0 : ℝ) < (pos : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hpos2)
  have hEx : ∃ j : ℕ, P j := by
    refine ⟨n, ?_⟩
    dsimp [P]
    have h1 : δ * (n : ℝ) / (pos : ℝ) ≤ δ * (n : ℝ) := by
      have hpos1 : (1 : ℝ) ≤ (pos : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hpos2)
      rw [div_le_iff₀ hposR]
      nlinarith
    have h2 : δ * (n : ℝ) ≤ (n : ℝ) := by
      have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [hδ1]
    have h3 : (n : ℝ) < (2 : ℝ) ^ n := n_lt_two_pow n hn1
    linarith
  have hP : P (Nat.find hEx) := Nat.find_spec hEx
  have hmin : ∀ m : ℕ, P m → Nat.find hEx ≤ m := by
    intro m hm
    exact Nat.find_min' hEx hm
  have hnotP0 : ¬ P 0 := by
    intro h0
    have hge : (1 : ℝ) ≤ δ * (n : ℝ) / (pos : ℝ) := by
      rw [le_div_iff₀ hposR]
      simpa using hposδn
    have h0' : δ * (n : ℝ) / (pos : ℝ) < (2 : ℝ) ^ 0 := by
      simpa [P] using h0
    norm_num at h0'
    linarith
  have hj1 : 1 ≤ Nat.find hEx := by
    by_contra h
    have hfind : Nat.find hEx = 0 := by omega
    exact hnotP0 (by simpa [hfind] using hP)
  have hprev : (2 : ℝ) ^ (Nat.find hEx - 1) ≤ δ * (n : ℝ) / (pos : ℝ) := by
    have hnP : ¬ P (Nat.find hEx - 1) := by
      intro hPm
      have hle := hmin (Nat.find hEx - 1) hPm
      omega
    exact le_of_not_gt hnP
  have hpow_le_δn : (2 : ℝ) ^ Nat.find hEx ≤ δ * (n : ℝ) := by
    have hmul : 2 * (2 : ℝ) ^ (Nat.find hEx - 1) ≤ 2 * (δ * (n : ℝ) / (pos : ℝ)) :=
      mul_le_mul_of_nonneg_left hprev (by norm_num)
    have hr : (2 : ℝ) ^ Nat.find hEx = 2 * (2 : ℝ) ^ (Nat.find hEx - 1) := by
      have hjn : (Nat.find hEx : ℕ) = (Nat.find hEx - 1) + 1 :=
        (Nat.sub_add_cancel hj1).symm
      conv_lhs => rw [hjn]
      rw [pow_succ]
      ring
    have htwo : 2 * (δ * (n : ℝ) / (pos : ℝ)) ≤ δ * (n : ℝ) := by
      have hA : 0 ≤ δ * (n : ℝ) := by positivity
      have hrew : 2 * (δ * (n : ℝ) / (pos : ℝ)) = (2 * δ * (n : ℝ)) / (pos : ℝ) := by
        field_simp [ne_of_gt hposR]
      rw [hrew]
      rw [div_le_iff₀ hposR]
      have hpos2R : (2 : ℝ) ≤ (pos : ℝ) := by exact_mod_cast hpos2
      have hm : 0 ≤ δ * (n : ℝ) * ((pos : ℝ) - 2) := by
        exact mul_nonneg hA (by nlinarith)
      nlinarith
    rw [hr]
    exact le_trans hmul htwo
  refine ⟨Nat.find hEx, hj1, hpow_le_δn, ?_, hprev⟩
  simpa [P] using hP


/-! ## cor: permutations -/

/-- a coordinate of a unit vector has absolute value at most `1`. -/
lemma coord_abs_le_one {n : ℕ} {x : Fin n → ℝ} (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
    (i : Fin n) : |x i| ≤ 1 := by
  have hsq : (x i) ^ 2 ≤ Commons.LinearAlgebra.Net.sqNorm x := by
    have hpos : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (x j) ^ 2 := by
      intro j hj; exact sq_nonneg (x j)
    have h1 := Finset.single_le_sum hpos (Finset.mem_univ i)
    simpa [Commons.LinearAlgebra.Net.sqNorm] using h1
  have hsq1 : (x i) ^ 2 ≤ 1 := by rwa [hx] at hsq
  have hsq1' : (x i) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hsq1
  have habs : |x i| ≤ |(1 : ℝ)| := (sq_le_sq.mp hsq1')
  simpa using habs

/-- integer `|a| ≥ k` from the real strict bound `k − 1 < |a|`. -/
lemma int_abs_ge_of_gt_sub_one {k : ℕ} {a : ℤ} (hk : 1 ≤ k)
    (h : (k : ℝ) - 1 < |(a : ℝ)|) : (k : ℤ) ≤ |a| := by
  by_contra hm
  have hm2 : |a| ≤ (k : ℤ) - 1 := by omega
  have hm3 : (|a| : ℝ) ≤ (k : ℝ) - 1 := by
    have hc : ((|a| : ℤ) : ℝ) ≤ (((k : ℤ) - 1) : ℝ) := by exact_mod_cast hm2
    have hc1 : (((k : ℤ) - 1) : ℝ) = (k : ℝ) - 1 := by
      norm_num [Int.cast_sub]
    rwa [Int.cast_abs, hc1] at hc
  linarith

/-- `|b| ≤ |a| + |a−b|`. -/
lemma abs_le_abs_add_abs_sub {a b : ℝ} : |b| ≤ |a| + |a - b| := by
  have h := abs_add_le (b - a) a
  have hrew : (b - a) + a = b := by ring
  have hc : |b - a| = |a - b| := abs_sub_comm b a
  rw [hrew, hc] at h
  linarith

/-- `1/th ≤ 2/T` from `T/2 ≤ th`. -/
lemma one_over_th_le_two_over_T {th T : ℝ} (hT0 : 0 < T) (hth0 : 0 < th)
    (hthhalf : T / 2 ≤ th) : (1 / th : ℝ) ≤ 2 / T := by
  have h1 : (1 / th) * T ≤ 2 := by
    field_simp [ne_of_gt hth0]
    nlinarith [hthhalf]
  have h2 : (1 / th : ℝ) ≤ 2 / T := (le_div_iff₀ hT0).mpr h1
  exact h2

/-- the real value of a position. -/
lemma pos_of_i_real {n : ℕ} (i : Fin n) : (posOf i : ℝ) = (i : ℝ) + 1 := by
  unfold posOf
  rw [Nat.cast_add, Nat.cast_one]

/-- `smallIndex` in terms of the position. -/
lemma smallIndex_pos_iff {n : ℕ} {δ : ℝ} (i : Fin n) :
    smallIndex n δ (i.val) ↔ (posOf i : ℝ) ≤ δ * (n : ℝ) := by
  unfold smallIndex posOf
  rw [Nat.cast_add, Nat.cast_one]

/-- top-coordinate upper bound: `|spv| ≤ 2√n/T + 1`. -/
lemma spv_bound_top {n : ℕ} {x : Fin n → ℝ} (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
    {th T : ℝ} (hT0 : 0 < T) (hth0 : 0 < th) (hthhalf : T / 2 ≤ th)
    (spv : Fin n → ℤ) (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1)
    (j : Fin n) : |(spv j : ℝ)| ≤ 2 * Real.sqrt (n : ℝ) / T + 1 := by
  have h1 : |(spv j : ℝ)| ≤ |(Real.sqrt (n : ℝ) / th) * x j| + 1 := by
    have h := hspv j
    have htri := abs_le_abs_add_abs_sub (a := (Real.sqrt (n : ℝ) / th) * x j) (b := (spv j : ℝ))
    -- htri : |spv j| ≤ |a| + |a − spv j|: and |a − spv| = |spv − a| ≤ 1
    have hd : |(Real.sqrt (n : ℝ) / th) * x j - (spv j : ℝ)| = |(spv j : ℝ) - (Real.sqrt (n : ℝ) / th) * x j| := by
      rw [abs_sub_comm]
    have hb : |(spv j : ℝ) - (Real.sqrt (n : ℝ) / th) * x j| ≤ 1 := by simpa [hd] using h
    linarith
  have h2 : |(Real.sqrt (n : ℝ) / th) * x j| ≤ Real.sqrt (n : ℝ) / th * 1 := by
    have hc : (Real.sqrt (n : ℝ) / th : ℝ) ≥ 0 := by positivity
    have hx1 : |x j| ≤ 1 := coord_abs_le_one hx j
    rw [abs_mul]
    have habs : |x j| = |x j| := rfl
    have hm : |Real.sqrt (n : ℝ) / th| * |x j| ≤ (Real.sqrt (n : ℝ) / th) * 1 := by
      have hnn : |Real.sqrt (n : ℝ) / th| = Real.sqrt (n : ℝ) / th := abs_of_nonneg hc
      rw [hnn]
      exact mul_le_mul_of_nonneg_left hx1 hc
    simpa using hm
  have h3 : Real.sqrt (n : ℝ) / th * 1 ≤ 2 * Real.sqrt (n : ℝ) / T := by
    have hnn : Real.sqrt (n : ℝ) ≥ 0 := by positivity
    have hlt := one_over_th_le_two_over_T (th := th) (T := T) hT0 hth0 hthhalf
    have hmul := mul_le_mul_of_nonneg_left hlt hnn
    -- (√n)·(1/th) ≤ √n·(2/T): rewrite to (√n/th) ≤ 2√n/T
    have hrew1 : Real.sqrt (n : ℝ) * (1 / th) = Real.sqrt (n : ℝ) / th := by ring
    have hrew2 : Real.sqrt (n : ℝ) * (2 / T) = 2 * Real.sqrt (n : ℝ) / T := by ring
    rw [hrew1, hrew2] at hmul
    linarith
  linarith


/-- small-coordinate radius lower bound: `4√n/(T·√pos) + 1 ≤ smallRad`. -/
lemma smallRad_radius_ge {n : ℕ} (T : ℝ) (pos : ℕ) (hpos0 : (0 : ℝ) < (pos : ℝ)) :
    4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) + 1 ≤ (smallRad n T pos : ℝ) := by
  have h := smallRad_real_ge (n := n) T pos
  simpa [mul_comm] using h

/-- the radius of the top coordinate covers `2√n/T + 1`. -/
lemma smallRad_top {n : ℕ} (T : ℝ) (hT0 : 0 < T) :
    (2 * Real.sqrt (n : ℝ) / T + 1 : ℝ) ≤ (smallRad n T 1 : ℝ) := by
  have hx1 : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by norm_num
  have hrew : 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt ((1 : ℕ) : ℝ)) =
      4 * Real.sqrt (n : ℝ) / T := by
    rw [hx1]
    field_simp [ne_of_gt hT0]
  have hsr0 := smallRad_real_ge (n := n) T 1
  have hsr : 4 * Real.sqrt (n : ℝ) / T + 1 ≤ (smallRad n T 1 : ℝ) := by
    rwa [← hrew]
  have h21 : (2 * Real.sqrt (n : ℝ) / T + 1 : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / T + 1 := by
    have hsqrt : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := by positivity
    have hc : 2 * Real.sqrt (n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by nlinarith
    have hd : 2 * Real.sqrt (n : ℝ) / T ≤ 4 * Real.sqrt (n : ℝ) / T :=
      div_le_div_of_nonneg_right hc (le_of_lt hT0)
    linarith
  linarith

/-- `2·2^{1/2} ≤ √8`. -/
lemma two_pow_half_mul_two_le_sqrt8 :
    (2 : ℝ) * (2 : ℝ) ^ (((0 : ℝ) + 1) / 2) ≤ Real.sqrt 8 := by
  apply nonneg_le_of_sq_le (by positivity) (by positivity)
  have hsq1 : ((2 : ℝ) ^ (((0 : ℝ) + 1) / 2)) ^ 2 = 2 := by
    have he : (((0 : ℝ) + 1) / 2) = (1 : ℝ) / 2 := by norm_num
    rw [he]
    have hrew : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := by
      rw [← Real.sqrt_eq_rpow (2 : ℝ)]
    rw [hrew]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [mul_pow, hsq1, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

/-- `√8/(√δ·T) + 1 ≤ largeRad`. -/
lemma largeRad_ge_sqrt8 {δ T : ℝ} (hδ0 : 0 < δ) (hT0 : 0 < T) :
    (Real.sqrt 8 / (Real.sqrt δ * T) + 1 : ℝ) ≤ (largeRad δ T : ℝ) := by
  have hsqrtδ : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hy0 : (0 : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) := by positivity
  have hceil : Real.sqrt 8 / (Real.sqrt δ * T) ≤ (⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ : ℝ) :=
    Nat.le_ceil _
  unfold largeRad
  have hcast : (↑(⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ + 1 : ℕ) : ℝ) =
      (⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rw [hcast]
  linarith

/-- square-root of the ratio `δ·n/pos`. -/
lemma sqrt_δn_div_pos {δ : ℝ} {n pos : ℕ} (hδ0 : 0 ≤ δ) (hpos0 : (0 : ℝ) < (pos : ℝ)) :
    Real.sqrt (δ * (n : ℝ) / (pos : ℝ)) = Real.sqrt δ * Real.sqrt (n : ℝ) / Real.sqrt (pos : ℝ) := by
  have hδn0 : (0 : ℝ) ≤ δ * (n : ℝ) := mul_nonneg hδ0 (by positivity)
  rw [Real.sqrt_div hδn0]
  have hmul : Real.sqrt (δ * (n : ℝ)) = Real.sqrt δ * Real.sqrt (n : ℝ) := Real.sqrt_mul hδ0 _
  rw [hmul]

/-- the shell spread bound is covered by the small-coordinate radius. -/
lemma shell_spread_le_radius {δ T th : ℝ} {n pos : ℕ} (hδ0 : 0 < δ) (hT0 : 0 < T)
    (hth0 : 0 < th) (hthhalf : T / 2 ≤ th)
    {j : ℕ} (hj : 1 ≤ j) (hprev : (2 : ℝ) ^ (j - 1) ≤ δ * (n : ℝ) / (pos : ℝ))
    (hpos0 : (0 : ℝ) < (pos : ℝ)) :
    (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) ≤
      4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := by
  let A : ℝ := (2 : ℝ) ^ (((j : ℝ) + 1) / 2)
  let r : ℝ := δ * (n : ℝ) / (pos : ℝ)
  have hA0 : 0 ≤ A := by positivity
  have hsh : A ≤ 2 * Real.sqrt r := by
    exact shell_half_bound (j := j) hj (δ := δ) (n := n) (pos := pos) hδ0 hpos0 hprev
  have h1t : (1 / th : ℝ) ≤ 2 / T := one_over_th_le_two_over_T (th := th) (T := T) hT0 hth0 hthhalf
  have hsqrtδ : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hdiv : A / (Real.sqrt δ * th) ≤ A * 2 / (Real.sqrt δ * T) := by
    have hm : A * (1 / th) ≤ A * (2 / T) := mul_le_mul_of_nonneg_left h1t hA0
    have hrew1 : A * (1 / th) = A / th := by ring
    have hrew2 : A * (2 / T) = A * 2 / T := by ring
    have hm' : A / th ≤ A * 2 / T := by rwa [hrew1, hrew2] at hm
    have hmain : (1 / Real.sqrt δ) * (A / th) ≤ (1 / Real.sqrt δ) * (A * 2 / T) :=
      mul_le_mul_of_nonneg_left hm' (le_of_lt (one_div_pos.mpr hsqrtδ))
    have hrew3 : (1 / Real.sqrt δ) * (A / th) = A / (Real.sqrt δ * th) := by
      field_simp [ne_of_gt hsqrtδ, ne_of_gt hth0]
    have hrew4 : (1 / Real.sqrt δ) * (A * 2 / T) = A * 2 / (Real.sqrt δ * T) := by
      field_simp [ne_of_gt hsqrtδ, ne_of_gt hT0]
    rwa [hrew3, hrew4] at hmain
  have hsh2 : A * 2 / (Real.sqrt δ * T) ≤ 2 * Real.sqrt r * 2 / (Real.sqrt δ * T) := by
    have hm := mul_le_mul_of_nonneg_right hsh (by positivity : (0 : ℝ) ≤ 2 / (Real.sqrt δ * T))
    have hrew : A * (2 / (Real.sqrt δ * T)) = A * 2 / (Real.sqrt δ * T) := by ring
    have hrew2 : (2 * Real.sqrt r) * (2 / (Real.sqrt δ * T)) = 2 * Real.sqrt r * 2 / (Real.sqrt δ * T) := by ring
    rwa [hrew, hrew2] at hm
  have hred : 2 * Real.sqrt r * 2 / (Real.sqrt δ * T) ≤
      4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := by
    have hsqr := sqrt_δn_div_pos (δ := δ) (n := n) (pos := pos) hδ0.le hpos0
    calc
      2 * Real.sqrt r * 2 / (Real.sqrt δ * T)
          = 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := by
            rw [hsqr]
            field_simp [ne_of_gt hsqrtδ, ne_of_gt hT0,
              ne_of_gt (Real.sqrt_pos.2 hpos0)] <;> ring
      _ ≤ 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := le_rfl
  exact le_trans hdiv (le_trans hsh2 hred)

/-- the `j=0` spread bound is covered by the large-coordinate radius. -/
lemma spread_j0_le_largeRad {δ T th : ℝ} (hδ0 : 0 < δ) (hT0 : 0 < T)
    (hth0 : 0 < th) (hthhalf : T / 2 ≤ th) :
    (2 : ℝ) ^ (((0 : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1 ≤ (largeRad δ T : ℝ) := by
  have h1t : (1 / th : ℝ) ≤ 2 / T := one_over_th_le_two_over_T (th := th) (T := T) hT0 hth0 hthhalf
  have hsqrtδ : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  let A0 : ℝ := (2 : ℝ) ^ (((0 : ℝ) + 1) / 2)
  have hA0 : 0 ≤ A0 := by positivity
  have hb : A0 / (Real.sqrt δ * th) ≤ Real.sqrt 8 / (Real.sqrt δ * T) := by
    -- A0/(√δ·th) ≤ A0·2/(√δT) ≤ √8/(√δT)
    have hm1 : A0 * (1 / th) ≤ A0 * (2 / T) := mul_le_mul_of_nonneg_left h1t hA0
    have hrew1 : A0 * (1 / th) = A0 / th := by ring
    have hrew2 : A0 * (2 / T) = A0 * 2 / T := by ring
    have hm1' : A0 / th ≤ A0 * 2 / T := by rwa [hrew1, hrew2] at hm1
    have hmain : (1 / Real.sqrt δ) * (A0 / th) ≤ (1 / Real.sqrt δ) * (A0 * 2 / T) :=
      mul_le_mul_of_nonneg_left hm1' (le_of_lt (one_div_pos.mpr hsqrtδ))
    have hrew3 : (1 / Real.sqrt δ) * (A0 / th) = A0 / (Real.sqrt δ * th) := by
      field_simp [ne_of_gt hsqrtδ, ne_of_gt hth0]
    have hrew4 : (1 / Real.sqrt δ) * (A0 * 2 / T) = A0 * 2 / (Real.sqrt δ * T) := by
      field_simp [ne_of_gt hsqrtδ, ne_of_gt hT0]
    have hmain' : A0 / (Real.sqrt δ * th) ≤ A0 * 2 / (Real.sqrt δ * T) := by
      rwa [hrew3, hrew4] at hmain
    have hsq8 : A0 * 2 ≤ Real.sqrt 8 := by
      have h0e : (((0 : ℝ) + 1) / 2) = (1 : ℝ) / 2 := by norm_num
      have hm : (2 : ℝ) * A0 ≤ Real.sqrt 8 := two_pow_half_mul_two_le_sqrt8
      have hcomm : (2 : ℝ) * A0 = A0 * 2 := by ring
      rwa [hcomm] at hm
    have hdiv : A0 * 2 / (Real.sqrt δ * T) ≤ Real.sqrt 8 / (Real.sqrt δ * T) := by
      exact div_le_div_of_nonneg_right hsq8 (le_of_lt (mul_pos hsqrtδ hT0))
    exact le_trans hmain' hdiv
  have hlg := largeRad_ge_sqrt8 (δ := δ) (T := T) hδ0 hT0
  calc
    A0 / (Real.sqrt δ * th) + 1
        ≤ Real.sqrt 8 / (Real.sqrt δ * T) + 1 := by linarith
    _ ≤ (largeRad δ T : ℝ) := hlg


/-! ## the membership lemma and `cor: permutations` -/

/-- the reordered `spv` vector lies in the coordinate family, given the two
spread bounds. -/
lemma reordered_spv_mem_Acoord {δ ν T : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) {n : ℕ} (hn1 : 1 ≤ n) (hδn1 : (1 : ℝ) ≤ δ * (n : ℝ))
    {x : Fin n → ℝ} (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
    {th T : ℝ} (hth0 : 0 < th) (hT0 : 0 < T) (hTν : T ≤ ν / 2)
    (hthhalf : T / 2 ≤ th) (hthT : th ≤ T)
    (spv : Fin n → ℤ) (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1)
    {σ : Equiv.Perm (Fin n)}
    (hlower : ∀ i : Fin n, ((i : ℝ) + 1) ≤ δ * (n : ℝ) → ν / th - 1 < |(spv (σ i) : ℝ)|)
    (hupper : ∀ j : ℕ, (2 : ℝ) ^ j ≤ δ * (n : ℝ) → ∀ i : Fin n,
        δ * (n : ℝ) / (2 : ℝ) ^ j < ((i : ℝ) + 1) →
        |(spv (σ i) : ℝ)| ≤ (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1) :
    ∀ i : Fin n, spv (σ i) ∈ Acoord n δ ν T i := by
  intro i
  by_cases hi : smallIndex n δ (i.val)
  · have hposδn : (posOf i : ℝ) ≤ δ * (n : ℝ) := (smallIndex_pos_iff i).mp hi
    have hpos0 : (0 : ℝ) < (posOf i : ℝ) := by exact_mod_cast (posOf_pos i)
    have hk2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
    have hk1 : 1 ≤ keepMag ν T := by omega
    have hkνth : (keepMag ν T : ℝ) ≤ ν / th := by
      have hkm := keepMag_le_self (ν := ν) (T := T) hT0 hν0
      have h2 : ν / T ≤ ν / th := div_le_div_of_nonneg_left (le_of_lt hν0) hth0 hthT
      linarith
    have hlow := hlower i hi
    have hlowreal : (keepMag ν T : ℝ) - 1 < |(spv (σ i) : ℝ)| := by linarith
    have hlowint : (keepMag ν T : ℤ) ≤ |spv (σ i)| :=
      int_abs_ge_of_gt_sub_one (k := keepMag ν T) (a := spv (σ i)) hk1 hlowreal
    by_cases htop : posOf i = 1
    · have hb := spv_bound_top (n := n) hx hT0 hth0 hthhalf spv hspv (σ i)
      have hsr := smallRad_top (n := n) T hT0
      have hup : |(spv (σ i) : ℝ)| ≤ (smallRad n T (posOf i) : ℝ) := by
        rw [htop]
        exact le_trans hb hsr
      have hm2 : |spv (σ i)| ≤ (smallRad n T (posOf i) : ℤ) :=
        int_abs_le_of_real_le (R := smallRad n T (posOf i)) hup
      exact Acoord_mem_of_small hi hlowint hm2
    · have hpos2 : 2 ≤ posOf i := by
        have hne : posOf i ≠ 1 := htop
        unfold posOf at hne ⊢
        omega
      have hδ1 : δ ≤ 1 := by nlinarith [hδ12]
      rcases shell_of_pos (n := n) (pos := posOf i) (δ := δ) hδ0 hδ1 hn1 hpos2 hposδn
        with ⟨j, hj1, h2jδn, hantP, hprev⟩
      have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hant0 : δ * (n : ℝ) < (posOf i : ℝ) * (2 : ℝ) ^ j := by
        simpa [mul_comm] using (div_lt_iff₀ hpos0).mp hantP
      have hant : δ * (n : ℝ) / (2 : ℝ) ^ j < (posOf i : ℝ) :=
        (div_lt_iff₀ h2jpos).mpr hant0
      have hant' : δ * (n : ℝ) / (2 : ℝ) ^ j < ((i : ℝ) + 1) := by
        have hpi := pos_of_i_real i
        rwa [← hpi]
      have hup_spread := hupper j h2jδn i hant'
      have hcmp := shell_spread_le_radius (δ := δ) (T := T) (th := th) (n := n)
        (pos := posOf i) hδ0 hT0 hth0 hthhalf (j := j) hj1 hprev hpos0
      have hupmid : |(spv (σ i) : ℝ)| ≤
          4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (posOf i : ℝ)) + 1 := by
        linarith
      have hsr := smallRad_radius_ge (n := n) T (posOf i) hpos0
      have hup : |(spv (σ i) : ℝ)| ≤ (smallRad n T (posOf i) : ℝ) := le_trans hupmid hsr
      have hm2 : |spv (σ i)| ≤ (smallRad n T (posOf i) : ℤ) :=
        int_abs_le_of_real_le (R := smallRad n T (posOf i)) hup
      exact Acoord_mem_of_small hi hlowint hm2
  · have hposgt : δ * (n : ℝ) < (posOf i : ℝ) := by
      have hnot : ¬ (posOf i : ℝ) ≤ δ * (n : ℝ) := by
        intro hle
        exact hi ((smallIndex_pos_iff i).mpr hle)
      exact lt_of_not_ge hnot
    have hup0 : δ * (n : ℝ) / (2 : ℝ) ^ 0 < ((i : ℝ) + 1) := by
      have hpi := pos_of_i_real i
      have hrew : (2 : ℝ) ^ 0 = 1 := by norm_num
      rw [hrew] at *
      have hg : δ * (n : ℝ) / 1 < (posOf i : ℝ) := by
        have h1 : δ * (n : ℝ) < (posOf i : ℝ) * 1 := by simpa using hposgt
        exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1)).mpr h1
      rw [← hpi]
      exact hg
    have h2j0 : (2 : ℝ) ^ 0 ≤ δ * (n : ℝ) := by simpa using hδn1
    have hup_spread := hupper 0 h2j0 i hup0
    have hup_spread' : |(spv (σ i) : ℝ)| ≤
        (2 : ℝ) ^ (((0 : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1 := by
      simpa using hup_spread
    have hlg := spread_j0_le_largeRad (δ := δ) (T := T) (th := th) hδ0 hT0 hth0 hthhalf
    have hup : |(spv (σ i) : ℝ)| ≤ (largeRad δ T : ℝ) := le_trans hup_spread' hlg
    have hm2 : |spv (σ i)| ≤ (largeRad δ T : ℤ) := int_abs_le_of_real_le (R := largeRad δ T) hup
    exact Acoord_mem_of_large hi hm2

/-- **cor: permutations**: for incompressible `x` with `th ∈ [T/2, T]`, the
spread permutation places `spv` inside the coordinate family. -/
theorem cor_permutations {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) {n : ℕ} (hn2 : 2 ≤ n) (hδn1 : (1 : ℝ) ≤ δ * (n : ℝ))
    {T : ℝ} (hT0 : 0 < T) (hTν : T ≤ ν / 2) :
    ∃ CPerm : ℝ, 1 ≤ CPerm ∧ ∃ PiSet : Finset (Equiv.Perm (Fin n)),
      (PiSet.card : ℝ) ≤ CPerm ^ n ∧
      ∀ {x : Fin n → ℝ} (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
        (hinc : ¬ Commons.LinearAlgebra.Net.compressible δ ν x)
        {th : ℝ} (hth0 : 0 < th) (hthhalf : T / 2 ≤ th) (hthT : th ≤ T)
        (spv : Fin n → ℤ)
        (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1),
        ∃ σ : Equiv.Perm (Fin n), σ ∈ PiSet ∧ ∀ i : Fin n, spv (σ i) ∈ Acoord n δ ν T i := by
  classical
  rcases Commons.LinearAlgebra.Net.spread_permutations with ⟨CPerm, hC1, hfam⟩
  have hn1 : 1 ≤ n := by omega
  rcases hfam n hn2 with ⟨PiSet, hPiCard, hPiProp⟩
  refine ⟨CPerm, hC1, PiSet, hPiCard, ?_⟩
  intro x hx hinc th hth0 hthhalf hthT spv hspv
  rcases hPiProp (δ := δ) (ν := ν) hδ0 hδ12 hν0 hν1 x hx hinc hth0 spv hspv
    with ⟨σ, hσmem, hlo, hup⟩
  refine ⟨σ, hσmem, ?_⟩
  exact reordered_spv_mem_Acoord (δ := δ) (ν := ν) (T := T) hδ0 hδ12 hν0 hν1
    (hn1 := hn1) (hδn1 := hδn1) hx hth0 hT0 hTν hthhalf hthT spv hspv hlo hup

end Submission.Section5D

end
