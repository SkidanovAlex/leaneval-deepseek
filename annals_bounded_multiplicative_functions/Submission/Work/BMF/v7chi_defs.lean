import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Contour data and elementary toolbox for `chi_prime_sum_twist` (node V7)

Definitions and elementary real-analysis facts used by
`Work.BMF.chi_prime_sum_twist` and its helper lemmas (`v7chi_arith`,
`v7chi_error_bounds`, `v7chi_primitive_reduction`, `v7chi_lowHeight_box`).

The contour half-width `δ = v7chidelta c₄ c₅ (1/(20A)) N u T` and the height
`T = v7chiT x = exp((log x)^{1/2})` are those of the lead's design
("Addendum: V0 exponent"): the Vinogradov–Korobov denominator `v7chiD` uses the exponent
`6/7` and the final error is `exp(-c (log x)^{1/12})`.

Nothing here depends on any analytic input.
-/

namespace Work.BMF

open Filter
open scoped Topology

noncomputable section

/-- The contour height: `T = exp((log x)^{1/2})`. -/
def v7chiT (x : ℝ) : ℝ := Real.exp (Real.log x ^ (1 / 2 : ℝ))

/-- The top height `|u| + T + 3` of the twisted box. -/
def v7chiU (u T : ℝ) : ℝ := |u| + T + 3

/-- The Vinogradov–Korobov denominator at the top height `U`. -/
def v7chiD (N : ℕ) (u T : ℝ) : ℝ :=
  Real.log (v7chiU u T) ^ (6 / 7 : ℝ) *
    (Real.log ((N : ℝ) + 2) + Real.log (Real.log (v7chiU u T)))

/-- The half-width `δ` of the (zero-free) box. -/
def v7chidelta (c₄ c₅ ε : ℝ) (N : ℕ) (u T : ℝ) : ℝ :=
  min (min (c₄ / (2 * v7chiD N u T)) (c₅ * (N : ℝ) ^ (-ε) / 2)) (1 / 4)

/-- The uniform bound `B` for `‖L'/L‖` on the box. -/
def v7chiB (C₄ C₅ ε : ℝ) (N : ℕ) (u T : ℝ) : ℝ :=
  C₄ * Real.log ((N : ℝ) * v7chiU u T) ^ 4 +
    C₅ * ((N : ℝ) ^ ε + Real.log ((N : ℝ) + 2) ^ 2)

/-! ## Elementary facts about the contour data -/

lemma v7chiU_ge_three (u T : ℝ) (hT : 0 ≤ T) : 3 ≤ v7chiU u T := by
  simp only [v7chiU]; linarith [abs_nonneg u]

lemma v7chiT_pos (x : ℝ) : 0 < v7chiT x := Real.exp_pos _

lemma v7chiD_pos (N : ℕ) (u T : ℝ) (hT : 0 ≤ T) (hN : 1 ≤ N) : 0 < v7chiD N u T := by
  have hU3 : 3 ≤ v7chiU u T := v7chiU_ge_three u T hT
  have hU0 : 0 < v7chiU u T := by linarith
  have hUe : Real.exp 1 ≤ v7chiU u T := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hlog3 : 0 < Real.log (v7chiU u T) := Real.log_pos (by linarith)
  have hloglog : 0 ≤ Real.log (Real.log (v7chiU u T)) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le hU0]
    exact hUe
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
  exact mul_pos (Real.rpow_pos_of_pos hlog3 _) (by linarith)

lemma v7chidelta_pos {c₄ c₅ ε : ℝ} (hc₄ : 0 < c₄) (hc₅ : 0 < c₅)
    {N : ℕ} (hN : 1 ≤ N) {u T : ℝ} (hT : 0 ≤ T) : 0 < v7chidelta c₄ c₅ ε N u T := by
  have hD := v7chiD_pos N u T hT hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : 0 < c₄ / (2 * v7chiD N u T) := div_pos hc₄ (by linarith)
  have h2 : 0 < c₅ * (N : ℝ) ^ (-ε) / 2 :=
    div_pos (mul_pos hc₅ (Real.rpow_pos_of_pos (by linarith) _)) (by norm_num)
  have h3 : (0 : ℝ) < 1 / 4 := by norm_num
  simp only [v7chidelta]
  exact lt_min (lt_min h1 h2) h3

lemma v7chidelta_le_quarter (c₄ c₅ ε : ℝ) (N : ℕ) (u T : ℝ) :
    v7chidelta c₄ c₅ ε N u T ≤ 1 / 4 := by
  simp only [v7chidelta]; exact min_le_right _ _

lemma v7chidelta_le_sieg (c₄ c₅ ε : ℝ) (N : ℕ) (u T : ℝ) :
    v7chidelta c₄ c₅ ε N u T ≤ c₅ * (N : ℝ) ^ (-ε) / 2 := by
  simp only [v7chidelta]; exact le_trans (min_le_left _ _) (min_le_right _ _)

lemma v7chidelta_le_D (c₄ c₅ ε : ℝ) (N : ℕ) (u T : ℝ) :
    v7chidelta c₄ c₅ ε N u T ≤ c₄ / (2 * v7chiD N u T) := by
  simp only [v7chidelta]; exact le_trans (min_le_left _ _) (min_le_left _ _)

/-- Monotonicity of the Vinogradov–Korobov denominator in the height. -/
lemma v7chiD_mono (N : ℕ) (hN : 2 ≤ N) (u T : ℝ) (hT : 0 ≤ T) {y : ℝ} (hy3 : 3 ≤ y)
    (hyU : y ≤ v7chiU u T) :
    Real.log y ^ (6 / 7 : ℝ) * (Real.log ((N : ℝ) + 2) + Real.log (Real.log y)) ≤
      v7chiD N u T := by
  have hU3 : 3 ≤ v7chiU u T := v7chiU_ge_three u T hT
  have hy0 : (0 : ℝ) < y := by linarith
  have hU0 : (0 : ℝ) < v7chiU u T := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogU : 0 < Real.log (v7chiU u T) := Real.log_pos (by linarith)
  have hlogm : Real.log y ≤ Real.log (v7chiU u T) := Real.log_le_log hy0 hyU
  have hf1 : Real.log y ^ (6 / 7 : ℝ) ≤ Real.log (v7chiU u T) ^ (6 / 7 : ℝ) :=
    Real.rpow_le_rpow hlogy.le hlogm (by norm_num)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
  have hll : Real.log (Real.log y) ≤ Real.log (Real.log (v7chiU u T)) :=
    Real.log_le_log hlogy hlogm
  have he1 : Real.exp 1 ≤ y := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hnn : 0 ≤ Real.log ((N : ℝ) + 2) + Real.log (Real.log y) := by
    have : 0 ≤ Real.log (Real.log y) := by
      apply Real.log_nonneg
      rw [Real.le_log_iff_exp_le hy0]
      exact he1
    linarith
  calc Real.log y ^ (6 / 7 : ℝ) * (Real.log ((N : ℝ) + 2) + Real.log (Real.log y))
      ≤ Real.log (v7chiU u T) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (v7chiU u T))) :=
        mul_le_mul hf1 (by linarith) hnn (Real.rpow_nonneg hlogU.le _)
    _ = v7chiD N u T := by simp only [v7chiD, v7chiU]

/-- At any height `y ∈ [3, U]`, the Vinogradov–Korobov denominator is at most the one at `U`, so
half of the `min` entry `c₄/(2D)` is at most `c₄/M(y)`. -/
lemma v7chi_denom_le {c₄ : ℝ} (hc₄ : 0 ≤ c₄) (N : ℕ) (hN : 2 ≤ N) {u T y : ℝ} (hT : 0 ≤ T)
    (hy : 3 ≤ y) (hyU : y ≤ v7chiU u T) :
    c₄ / (2 * v7chiD N u T) ≤
      c₄ / (Real.log y ^ (6 / 7 : ℝ) * (Real.log ((N : ℝ) + 2) + Real.log (Real.log y))) := by
  have hmono := v7chiD_mono N hN u T hT hy hyU
  have hDpos : 0 < v7chiD N u T := v7chiD_pos N u T hT (by omega)
  have hMpos : 0 < Real.log y ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log y)) := by
    refine mul_pos (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _) ?_
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have h5 : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
    have h6 : 0 ≤ Real.log (Real.log y) := by
      apply Real.log_nonneg
      rw [Real.le_log_iff_exp_le (by linarith)]
      have : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    linarith
  exact div_le_div_of_nonneg_left hc₄ hMpos (by linarith)

/-! ## Pointwise facts about `x' = ⌊x⌋ + 1/2` -/

lemma v7chiX_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x := by
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  linarith

lemma v7chiX_ge {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 * ((⌊x⌋₊ : ℝ) + 1 / 2) := by
  have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

lemma v7chiX_pos {x : ℝ} (hx : 0 ≤ x) : 0 < (⌊x⌋₊ : ℝ) + 1 / 2 := by
  have h1 : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  linarith

lemma v7chiX_log_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) ≤ Real.log x + 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos := v7chiX_pos (by linarith : (0 : ℝ) ≤ x)
  have h2 : (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x := v7chiX_le_two_mul (by linarith)
  calc Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) ≤ Real.log (2 * x) := Real.log_le_log hpos h2
    _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (ne_of_gt hx0)
    _ ≤ Real.log x + 1 := by linarith [Real.log_two_lt_d9]

lemma v7chiX_log_ge_one {x : ℝ} (hx : 6 ≤ x) :
    1 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) := by
  have h1 : (3 : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 / 2 := by
    have h2 : (6 : ℝ) ≤ x := hx
    have h3 : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h2)
    have : (6 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
    linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) := by
        apply Real.log_le_log (Real.exp_pos 1)
        have : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith

lemma v7chiX_floor (x : ℝ) : ⌊(⌊x⌋₊ : ℝ) + 1 / 2⌋₊ = ⌊x⌋₊ := by
  rw [Nat.floor_eq_iff (by positivity)]
  exact ⟨by linarith, by linarith⟩

lemma v7chiX_not_natCast (x : ℝ) (n : ℕ) : (n : ℝ) ≠ (⌊x⌋₊ : ℝ) + 1 / 2 := by
  intro h
  have h2 : (2 * n : ℕ) = 2 * ⌊x⌋₊ + 1 := by
    have : ((2 * n : ℕ) : ℝ) = ((2 * ⌊x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ## Eventual-arithmetic toolbox -/

/-- Eventually `log y ≤ ε y^r` (`r > 0`). -/
lemma v7chi_ev_log_le_mul_rpow {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, Real.log y ≤ ε * y ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy0 r),
    abs_of_nonneg hl0] at hy
  exact hy

/-- Eventually `C ≤ y^r` (`r > 0`). -/
lemma v7chi_ev_const_le_rpow {r C : ℝ} (hr : 0 < r) :
    ∀ᶠ y : ℝ in atTop, C ≤ y ^ r := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact le_trans hC (Real.rpow_nonneg hy r)
  · push_neg at hC
    exact (tendsto_rpow_atTop hr).eventually_ge_atTop C

/-- Eventually a constant is dominated by `exp (δ y^r)` (`δ, r > 0`). -/
lemma v7chi_ev_const_le_exp {δ r C : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    ∀ᶠ y : ℝ in atTop, C ≤ Real.exp (δ * y ^ r) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (δ * y ^ r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_const_mul_atTop_of_pos hδ).mpr (tendsto_rpow_atTop hr))
  exact h1.eventually_ge_atTop C

end

end Work.BMF
