/-
# `Submission.Work.FITop.RCPrelude` — asymptotics toolkit for the range-check chain

Building blocks for `Work.FITop.RangeCheckChain`: the generic (log)^b-vs-x^ε comparison
lemmas, the explicit bounds for the numerical parameters `Lam1, Delta1, Dcut, Y1, del1, s1,
Pcut, Mcutb, d2b` of `Submission/Work/FITop/Defs.lean`, and the sandwich `W1 ≤ s1 ≤ 2 W1`.
-/
import Mathlib
import Submission.Work.FITop.Defs

set_option autoImplicit false

namespace Work.FITop

open Filter

noncomputable section

/-! ## 0. Generic asymptotic helpers -/

lemma FI_ev_mul_rpow_log_rpow_lt {a b c C : ℝ} (hC : 0 < C) (hac : a < c) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * (Real.log x) ^ b < x ^ c := by
  have hε : 0 < c - a := sub_pos.mpr hac
  have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ b / x ^ (c - a)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop b hε).tendsto_div_nhds_zero
  have h1 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ b / x ^ (c - a) < 1 / C :=
    h0.eventually_lt_const (by positivity)
  filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with x hlt hx
  have hxca : 0 < x ^ (c - a) := Real.rpow_pos_of_pos hx _
  have h2 : (Real.log x) ^ b < (1 / C) * x ^ (c - a) := (div_lt_iff₀ hxca).mp hlt
  rw [one_div] at h2
  have h3 : C * (Real.log x) ^ b < C * (C⁻¹ * x ^ (c - a)) := mul_lt_mul_of_pos_left h2 hC
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul] at h3
  calc C * x ^ a * (Real.log x) ^ b = x ^ a * (C * (Real.log x) ^ b) := by ring
    _ < x ^ a * x ^ (c - a) := mul_lt_mul_of_pos_left h3 (Real.rpow_pos_of_pos hx a)
    _ = x ^ c := by
        rw [← Real.rpow_add hx]; congr 1; ring

lemma FI_ev_mul_rpow_log_rpow_lt_nat {a b c C : ℝ} (hC : 0 < C) (hac : a < c) :
    ∀ᶠ x : ℕ in atTop, C * (x : ℝ) ^ a * (Real.log (x : ℝ)) ^ b < (x : ℝ) ^ c :=
  tendsto_natCast_atTop_atTop.eventually (FI_ev_mul_rpow_log_rpow_lt hC hac)

lemma FI_ev_log_rpow_le {b ε C : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ b ≤ C * x ^ ε := by
  have h := FI_ev_mul_rpow_log_rpow_lt (a := (0 : ℝ)) (b := b) (c := ε) (C := 1 / C)
    (by positivity) hε
  filter_upwards [h] with x hx
  rw [Real.rpow_zero, mul_one, one_div] at hx
  have h3 : C * (C⁻¹ * (Real.log x) ^ b) < C * x ^ ε := mul_lt_mul_of_pos_left hx hC
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul] at h3
  exact h3.le

lemma FI_ev_log_rpow_le_nat {b ε C : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (Real.log (x : ℝ)) ^ b ≤ C * (x : ℝ) ^ ε :=
  tendsto_natCast_atTop_atTop.eventually (FI_ev_log_rpow_le hC hε)

lemma FI_ev_loglog_rpow_le_nat {b ε C : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (Real.log (x : ℝ))) ^ b ≤ C * (Real.log (x : ℝ)) ^ ε :=
  tendsto_natCast_atTop_atTop.eventually
    (Real.tendsto_log_atTop.eventually (FI_ev_log_rpow_le hC hε))

lemma FI_ev_rpow_ge_nat (a : ℝ) (ha : 0 < a) (C : ℝ) :
    ∀ᶠ x : ℕ in atTop, C ≤ (x : ℝ) ^ a :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop ha).eventually_ge_atTop C)

lemma FI_ev_log_ge_nat (C : ℝ) : ∀ᶠ x : ℕ in atTop, C ≤ Real.log (x : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop C)

/-! ## 1. Elementary cast facts -/

lemma FI_Lam1_nonneg (x : ℕ) : 0 ≤ Lam1 x := Real.rpow_nonneg (Nat.cast_nonneg x) _

lemma FI_ev_ge_one : ∀ᶠ x : ℕ in atTop, (1 : ℕ) ≤ x := eventually_ge_atTop 1

lemma FI_cast_one_le {x : ℕ} (hx : 1 ≤ x) : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx

lemma FI_cast_pos {x : ℕ} (hx : 1 ≤ x) : (0 : ℝ) < (x : ℝ) := by
  exact_mod_cast (by omega : 0 < x)

/-- `1 ≤ a * b * c` from `1 ≤ a`, `1 ≤ b`, `1 ≤ c`. -/
lemma FI_one_le_mul3 {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    1 ≤ a * b * c := by
  have ha0 : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  have h1 : (1 : ℝ) * 1 ≤ a * b := mul_le_mul ha hb zero_le_one ha0
  have h2 : (1 : ℝ) * 1 * 1 ≤ a * b * c :=
    mul_le_mul h1 hc zero_le_one (le_trans zero_le_one (by simpa using h1))
  simpa using h2

/-! ## 2. Bounds for `Lam1`, `Delta1` -/

lemma FI_ev_Lam1_ge_one : ∀ᶠ x : ℕ in atTop, 1 ≤ Lam1 x := by
  filter_upwards [FI_ev_ge_one] with x hx
  rw [Lam1]
  exact Real.one_le_rpow (FI_cast_one_le hx) (by norm_num)

lemma FI_Lam1_le_Delta1 (x : ℕ) : Lam1 x ≤ (Delta1 x : ℝ) := by
  rw [Delta1]; exact Nat.le_ceil _

lemma FI_ev_Delta1_le_two_Lam1 : ∀ᶠ x : ℕ in atTop, (Delta1 x : ℝ) ≤ 2 * Lam1 x := by
  filter_upwards [FI_ev_Lam1_ge_one] with x hLam
  have h0 : 0 ≤ Lam1 x := le_trans zero_le_one hLam
  have hlt := Nat.ceil_lt_add_one h0
  simp only [Delta1]
  linarith

/-! ## 3. Bounds for `Dcut` and `sqrt (Dcut)` -/

lemma FI_Dcut_upper (x : ℕ) : (Dcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := by
  rw [Dcut, Submission.Rcut]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

lemma FI_ev_Dcut_lower : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (Dcut x : ℝ) := by
  filter_upwards [FI_ev_rpow_ge_nat ((11 : ℝ) / 16) (by norm_num) 2] with x hx
  have hlt : (x : ℝ) ^ ((11 : ℝ) / 16) < (⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [Dcut, Submission.Rcut]
  linarith

lemma FI_ev_Dcut_ge_one : ∀ᶠ x : ℕ in atTop, 1 ≤ (Dcut x : ℝ) := by
  filter_upwards [FI_ev_Dcut_lower, FI_ev_rpow_ge_nat ((11 : ℝ) / 16) (by norm_num) 4]
    with x hx h4
  linarith

lemma FI_sqrt_Dcut_upper (x : ℕ) :
    Real.sqrt (Dcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 32) := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  calc Real.sqrt (Dcut x : ℝ) ≤ Real.sqrt ((x : ℝ) ^ ((11 : ℝ) / 16)) :=
        Real.sqrt_le_sqrt (FI_Dcut_upper x)
    _ = (x : ℝ) ^ ((11 : ℝ) / 32) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
        congr 1
        norm_num

lemma FI_ev_sqrt_Dcut_upper : ∀ᶠ x : ℕ in atTop,
    Real.sqrt (Dcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 32) :=
  Filter.Eventually.of_forall FI_sqrt_Dcut_upper

lemma FI_ev_sqrt_Dcut_lower : ∀ᶠ x : ℕ in atTop,
    (x : ℝ) ^ ((11 : ℝ) / 32) / 2 ≤ Real.sqrt (Dcut x : ℝ) := by
  filter_upwards [FI_ev_Dcut_lower] with x hD
  have hnn : 0 ≤ (x : ℝ) ^ ((11 : ℝ) / 32) / 2 := by positivity
  have hsq : ((x : ℝ) ^ ((11 : ℝ) / 32) / 2) ^ 2 = (x : ℝ) ^ ((11 : ℝ) / 16) / 4 := by
    rw [div_pow]
    have h3 : ((x : ℝ) ^ ((11 : ℝ) / 32)) ^ 2 = (x : ℝ) ^ ((11 : ℝ) / 16) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]
      congr 1
      norm_num
    rw [h3]
    norm_num
  rw [Real.le_sqrt hnn (Nat.cast_nonneg (Dcut x))]
  rw [hsq]
  linarith

/-! ## 4. Bounds for `Y1` and its integer parts -/

lemma FI_Y1_nonneg (x : ℕ) : 0 ≤ Y1 x :=
  mul_nonneg (inv_nonneg.mpr (FI_Lam1_nonneg x)) (Real.sqrt_nonneg _)

lemma FI_ev_Y1_upper : ∀ᶠ x : ℕ in atTop, Y1 x ≤ (x : ℝ) ^ ((267 : ℝ) / 800) := by
  filter_upwards [FI_ev_sqrt_Dcut_upper, FI_ev_ge_one] with x hD hx1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hA : (Lam1 x)⁻¹ = (x : ℝ) ^ (-((1 : ℝ) / 100)) := by
    rw [Lam1, ← Real.rpow_neg (le_of_lt hxpos) ((1 : ℝ) / 100)]
  rw [Y1, hA]
  calc (x : ℝ) ^ (-((1 : ℝ) / 100)) * Real.sqrt (Dcut x : ℝ)
      ≤ (x : ℝ) ^ (-((1 : ℝ) / 100)) * (x : ℝ) ^ ((11 : ℝ) / 32) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg (le_of_lt hxpos) _)
    _ = (x : ℝ) ^ ((267 : ℝ) / 800) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        norm_num

lemma FI_ev_Y1_lower : ∀ᶠ x : ℕ in atTop,
    (x : ℝ) ^ ((267 : ℝ) / 800) / 2 ≤ Y1 x := by
  filter_upwards [FI_ev_sqrt_Dcut_lower, FI_ev_ge_one] with x hD hx1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hA : (Lam1 x)⁻¹ = (x : ℝ) ^ (-((1 : ℝ) / 100)) := by
    rw [Lam1, ← Real.rpow_neg (le_of_lt hxpos) ((1 : ℝ) / 100)]
  rw [Y1, hA]
  have h2 : (x : ℝ) ^ (-((1 : ℝ) / 100)) * (x : ℝ) ^ ((11 : ℝ) / 32)
      = (x : ℝ) ^ ((267 : ℝ) / 800) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    norm_num
  have h1 : (x : ℝ) ^ (-((1 : ℝ) / 100)) * ((x : ℝ) ^ ((11 : ℝ) / 32) / 2)
      = (x : ℝ) ^ ((267 : ℝ) / 800) / 2 := by
    rw [← h2]; ring
  rw [← h1]
  exact mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg (le_of_lt hxpos) _)

lemma FI_ev_floor_Y1_lower : ∀ᶠ x : ℕ in atTop,
    (x : ℝ) ^ ((267 : ℝ) / 800) / 4 ≤ (⌊Y1 x⌋₊ : ℝ) := by
  filter_upwards [FI_ev_Y1_lower, FI_ev_rpow_ge_nat ((267 : ℝ) / 800) (by norm_num) 4]
    with x hY hx
  have hlt := Nat.lt_floor_add_one (Y1 x)
  have hY2 : 2 ≤ Y1 x := by linarith
  linarith

lemma FI_ev_floor_Y1_upper : ∀ᶠ x : ℕ in atTop,
    (⌊Y1 x⌋₊ : ℝ) ≤ (x : ℝ) ^ ((267 : ℝ) / 800) := by
  filter_upwards [FI_ev_Y1_upper] with x h
  exact le_trans (Nat.floor_le (FI_Y1_nonneg x)) h

lemma FI_ev_floor_eY1_upper : ∀ᶠ x : ℕ in atTop,
    (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800) := by
  filter_upwards [FI_ev_Y1_upper] with x h
  have h0 : (0 : ℝ) ≤ Real.exp 1 * Y1 x :=
    mul_nonneg (Real.exp_pos 1).le (FI_Y1_nonneg x)
  calc (⌊Real.exp 1 * Y1 x⌋₊ : ℝ) ≤ Real.exp 1 * Y1 x := Nat.floor_le h0
    _ ≤ Real.exp 1 * (x : ℝ) ^ ((267 : ℝ) / 800) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le

/-! ## 5. Bounds for `del1` -/

lemma FI_ev_del1_ge_one : ∀ᶠ x : ℕ in atTop, 1 ≤ del1 x := by
  filter_upwards [FI_ev_log_ge_nat 1] with x hx
  rw [del1]; nlinarith [hx]

/-- `y ^ 2` (natural power) as a real power. -/
lemma FI_rpow_two (y : ℝ) : y ^ 2 = y ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma FI_ev_del1_le : ∀ᶠ x : ℕ in atTop, del1 x ≤ (x : ℝ) ^ ((1 : ℝ) / 100) := by
  have h := FI_ev_log_rpow_le_nat (b := ((2 : ℕ) : ℝ)) (ε := (1 : ℝ) / 100) (C := 1)
    one_pos (by norm_num)
  filter_upwards [h] with x hx
  rw [one_mul, Real.rpow_natCast] at hx
  rw [del1]
  exact hx

/-! ## 6. The window ratio `W1` and the sandwich for `s1` -/

/-- The dyadic window ratio `√x / (8δ√D)` whose `log₂` is `J1`. -/
def W1 (x : ℕ) : ℝ := Real.sqrt (x : ℝ) / (8 * del1 x * Real.sqrt (Dcut x))

lemma FI_J1_eq (x : ℕ) : J1 x = ⌈Real.log (W1 x) / Real.log 2⌉₊ := rfl

lemma FI_sqrt_div_eq8 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / (8 * x ^ ((283 : ℝ) / 800)) = (1 / 8) * x ^ ((117 : ℝ) / 800) := by
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_inv]
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  rw [← Real.rpow_neg (le_of_lt hx) ((283 : ℝ) / 800)]
  rw [show x ^ ((1 : ℝ) / 2) * ((1 / 8) * x ^ (-((283 : ℝ) / 800)))
        = (1 / 8) * (x ^ ((1 : ℝ) / 2) * x ^ (-((283 : ℝ) / 800))) by ring]
  rw [← Real.rpow_add hx]
  congr 1
  norm_num

lemma FI_sqrt_div_eq4 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / (4 * x ^ ((11 : ℝ) / 32)) = (1 / 4) * x ^ ((5 : ℝ) / 32) := by
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_inv]
  rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
  rw [← Real.rpow_neg (le_of_lt hx) ((11 : ℝ) / 32)]
  rw [show x ^ ((1 : ℝ) / 2) * ((1 / 4) * x ^ (-((11 : ℝ) / 32)))
        = (1 / 4) * (x ^ ((1 : ℝ) / 2) * x ^ (-((11 : ℝ) / 32))) by ring]
  rw [← Real.rpow_add hx]
  congr 1
  norm_num

lemma FI_W1_nonneg (x : ℕ) : 0 ≤ W1 x := by
  rw [W1, del1]
  positivity

lemma FI_ev_W1_lower : ∀ᶠ x : ℕ in atTop,
    (1 / 8) * (x : ℝ) ^ ((117 : ℝ) / 800) ≤ W1 x := by
  filter_upwards [FI_ev_del1_le, FI_ev_sqrt_Dcut_upper, FI_ev_del1_ge_one,
    FI_ev_Dcut_ge_one, FI_ev_ge_one] with x hdel hD hdel1 hD1 hx1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hxpos
  have hdelpos : 0 < del1 x := lt_of_lt_of_le zero_lt_one hdel1
  have hDpos : 0 < Real.sqrt (Dcut x : ℝ) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hD1)
  have hdenpos : 0 < 8 * del1 x * Real.sqrt (Dcut x : ℝ) :=
    mul_pos (mul_pos (by norm_num) hdelpos) hDpos
  have hmul : del1 x * Real.sqrt (Dcut x : ℝ) ≤ (x : ℝ) ^ ((283 : ℝ) / 800) := by
    have h := mul_le_mul hdel hD (Real.sqrt_nonneg _) (Real.rpow_nonneg hx0 _)
    have hsum : ((1 : ℝ) / 100 + (11 : ℝ) / 32) = (283 : ℝ) / 800 := by norm_num
    rwa [← Real.rpow_add hxpos, hsum] at h
  have hdenle : 8 * del1 x * Real.sqrt (Dcut x : ℝ) ≤ 8 * (x : ℝ) ^ ((283 : ℝ) / 800) := by
    have := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 8)
    linarith [this]
  have hmain : Real.sqrt (x : ℝ) / (8 * (x : ℝ) ^ ((283 : ℝ) / 800)) ≤ W1 x := by
    rw [W1]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg x) hdenpos hdenle
  rw [← FI_sqrt_div_eq8 hxpos]
  exact hmain

lemma FI_ev_W1_upper : ∀ᶠ x : ℕ in atTop,
    W1 x ≤ (1 / 4) * (x : ℝ) ^ ((5 : ℝ) / 32) := by
  filter_upwards [FI_ev_del1_ge_one, FI_ev_sqrt_Dcut_lower, FI_ev_ge_one] with x hdel1 hD hx1
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  have hdelpos : 0 < del1 x := lt_of_lt_of_le zero_lt_one hdel1
  have hmul : (x : ℝ) ^ ((11 : ℝ) / 32) / 2 ≤ del1 x * Real.sqrt (Dcut x : ℝ) := by
    have h := mul_le_mul hdel1 hD (by positivity) (le_trans zero_le_one hdel1)
    simpa using h
  have hge : 4 * (x : ℝ) ^ ((11 : ℝ) / 32) ≤ 8 * del1 x * Real.sqrt (Dcut x : ℝ) := by
    have h8 := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 8)
    linarith [h8]
  have hcpos : 0 < 4 * (x : ℝ) ^ ((11 : ℝ) / 32) := by positivity
  have hmain : W1 x ≤ Real.sqrt (x : ℝ) / (4 * (x : ℝ) ^ ((11 : ℝ) / 32)) := by
    rw [W1]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg x) hcpos hge
  rw [FI_sqrt_div_eq4 hxpos] at hmain
  exact hmain

lemma FI_ev_W1_ge_one : ∀ᶠ x : ℕ in atTop, 1 ≤ W1 x := by
  filter_upwards [FI_ev_W1_lower, FI_ev_rpow_ge_nat ((117 : ℝ) / 800) (by norm_num) 8]
    with x h hx
  linarith

lemma FI_two_rpow_log_div_log (w : ℝ) (hw : 0 < w) :
    (2 : ℝ) ^ (Real.log w / Real.log 2) = w := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h : Real.log 2 * (Real.log w / Real.log 2) = Real.log w := by
    rw [mul_comm, div_mul_cancel₀ _ h2]
  rw [h, Real.exp_log hw]

lemma FI_ev_W1_le_s1 : ∀ᶠ x : ℕ in atTop, W1 x ≤ s1 x := by
  filter_upwards [FI_ev_W1_ge_one] with x hw1
  have hwpos : 0 < W1 x := lt_of_lt_of_le zero_lt_one hw1
  have ht : Real.log (W1 x) / Real.log 2 ≤ (((J1 x : ℕ)) : ℝ) := by
    rw [FI_J1_eq]; exact Nat.le_ceil _
  have hpow : (2 : ℝ) ^ (Real.log (W1 x) / Real.log 2) = W1 x :=
    FI_two_rpow_log_div_log _ hwpos
  calc W1 x = (2 : ℝ) ^ (Real.log (W1 x) / Real.log 2) := hpow.symm
    _ ≤ (2 : ℝ) ^ ((((J1 x : ℕ)) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
    _ = s1 x := by rw [s1, Real.rpow_natCast]

lemma FI_ev_s1_le_two_W1 : ∀ᶠ x : ℕ in atTop, s1 x ≤ 2 * W1 x := by
  filter_upwards [FI_ev_W1_ge_one] with x hw1
  have hwpos : 0 < W1 x := lt_of_lt_of_le zero_lt_one hw1
  have ht : 0 ≤ Real.log (W1 x) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hw1) (Real.log_pos (by norm_num)).le
  have hceil : ((((J1 x : ℕ)) : ℝ)) < Real.log (W1 x) / Real.log 2 + 1 := by
    rw [FI_J1_eq]; exact Nat.ceil_lt_add_one ht
  have hpow : (2 : ℝ) ^ (Real.log (W1 x) / Real.log 2) = W1 x :=
    FI_two_rpow_log_div_log _ hwpos
  calc s1 x = (2 : ℝ) ^ ((((J1 x : ℕ)) : ℝ)) := by
        rw [s1]; exact (Real.rpow_natCast 2 (J1 x)).symm
    _ ≤ (2 : ℝ) ^ (Real.log (W1 x) / Real.log 2 + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2 * W1 x := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hpow]; ring

/-! ## 7. Bounds for `Pcut` -/

lemma FI_Pcut_ge (x : ℕ) :
    Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) ≤ (Pcut x : ℝ) := by
  rw [Pcut]; exact Nat.le_ceil _

lemma FI_Pcut_pos (x : ℕ) : 0 < (Pcut x : ℝ) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (Real.one_le_exp (by positivity)) (FI_Pcut_ge x))

lemma FI_Pcut_le_two_exp (x : ℕ) :
    (Pcut x : ℝ) ≤ 2 * Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := by
  have hlt : (Pcut x : ℝ) < Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) + 1 := by
    rw [Pcut]; exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  have h1 : (1 : ℝ) ≤ Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) :=
    Real.one_le_exp (by positivity)
  linarith

lemma FI_log_Pcut_ge (x : ℕ) :
    (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pcut x : ℝ) := by
  have h := FI_Pcut_ge x
  have hpos : 0 < Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := Real.exp_pos _
  calc (Real.log (Real.log (x : ℝ))) ^ 2
      = Real.log (Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2)) := (Real.log_exp _).symm
    _ ≤ Real.log (Pcut x : ℝ) := Real.log_le_log hpos h

lemma FI_log_Pcut_le (x : ℕ) :
    Real.log (Pcut x : ℝ) ≤ Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2 := by
  have h := FI_Pcut_le_two_exp x
  have he : (0 : ℝ) < Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := Real.exp_pos _
  calc Real.log (Pcut x : ℝ)
      ≤ Real.log (2 * Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2)) :=
        Real.log_le_log (FI_Pcut_pos x) h
    _ = Real.log 2 + Real.log (Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2)) :=
        Real.log_mul (by norm_num) (ne_of_gt he)
    _ = Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2 := by rw [Real.log_exp]

lemma FI_ev_Pcut_le_rpow : ∀ᶠ x : ℕ in atTop, (Pcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 64) := by
  have h1 := FI_ev_loglog_rpow_le_nat (b := ((2 : ℕ) : ℝ)) (ε := (1 : ℝ)) (C := (11 : ℝ) / 128)
    (by norm_num) (by norm_num)
  filter_upwards [h1, FI_ev_log_ge_nat (128 * Real.log 2 / 11), FI_ev_ge_one]
    with x hLL hlogx hx1
  have hLL' : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ (11 : ℝ) / 128 * Real.log (x : ℝ) := by
    rw [Real.rpow_one, Real.rpow_natCast] at hLL
    exact hLL
  have hlog2 : Real.log 2 ≤ (11 : ℝ) / 128 * Real.log (x : ℝ) := by linarith
  have hsum : Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2
      ≤ (11 : ℝ) / 64 * Real.log (x : ℝ) :=
    calc Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2
        ≤ (11 : ℝ) / 128 * Real.log (x : ℝ) + (11 : ℝ) / 128 * Real.log (x : ℝ) :=
          add_le_add hlog2 hLL'
      _ = (11 : ℝ) / 64 * Real.log (x : ℝ) := by ring
  have hxpos : (0 : ℝ) < x := FI_cast_pos hx1
  calc (Pcut x : ℝ) ≤ 2 * Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := FI_Pcut_le_two_exp x
    _ = Real.exp (Real.log 2 + (Real.log (Real.log (x : ℝ))) ^ 2) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp ((11 : ℝ) / 64 * Real.log (x : ℝ)) := Real.exp_le_exp.mpr hsum
    _ = (x : ℝ) ^ ((11 : ℝ) / 64) := by
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        ring

/-! ## 8. Bounds for `Mcutb` and `d2b` -/

lemma FI_ev_Mcutb_le : ∀ᶠ x : ℕ in atTop,
    (Mcutb x : ℝ) ≤ 9 * Lam1 x * del1 x * Real.sqrt (x : ℝ) := by
  filter_upwards [FI_ev_Lam1_ge_one, FI_ev_del1_ge_one, FI_ev_ge_one] with x hA hdel hx1
  have hs : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.one_le_sqrt.mpr (FI_cast_one_le hx1)
  have hprod : (1 : ℝ) ≤ Lam1 x * del1 x * Real.sqrt (x : ℝ) := FI_one_le_mul3 hA hdel hs
  have hnn : 0 ≤ 8 * Lam1 x * del1 x * Real.sqrt (x : ℝ) := by linarith [hprod]
  have hceil : (Mcutb x : ℝ) < 8 * Lam1 x * del1 x * Real.sqrt (x : ℝ) + 1 := by
    rw [Mcutb]; exact Nat.ceil_lt_add_one hnn
  have hge : (8 : ℝ) ≤ 8 * Lam1 x * del1 x * Real.sqrt (x : ℝ) := by linarith [hprod]
  linarith

lemma FI_ev_d2b_le : ∀ᶠ x : ℕ in atTop,
    (d2b x : ℝ) ≤ 65 * (Lam1 x) ^ 2 * (del1 x) ^ 2 := by
  filter_upwards [FI_ev_Lam1_ge_one, FI_ev_del1_ge_one] with x hA hdel
  have hA2 : (1 : ℝ) ≤ (Lam1 x) ^ 2 := one_le_pow₀ hA
  have hd2 : (1 : ℝ) ≤ (del1 x) ^ 2 := one_le_pow₀ hdel
  have hprod : (1 : ℝ) ≤ (Lam1 x) ^ 2 * (del1 x) ^ 2 :=
    le_of_eq_of_le (by ring) (mul_le_mul hA2 hd2 zero_le_one (le_trans zero_le_one hA2))
  have hnn : 0 ≤ 64 * (Lam1 x) ^ 2 * (del1 x) ^ 2 := by linarith [hprod]
  have hceil : (d2b x : ℝ) < 64 * (Lam1 x) ^ 2 * (del1 x) ^ 2 + 1 := by
    rw [d2b]; exact Nat.ceil_lt_add_one hnn
  have hge : (64 : ℝ) ≤ 64 * (Lam1 x) ^ 2 * (del1 x) ^ 2 := by linarith [hprod]
  linarith

end

end Work.FITop
