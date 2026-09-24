import Mathlib
import Submission.Work.ChenPlan.H2.Defs

/-!
# The geometry of Chen's `h2` window

The sift limit `M = ⌊x^{1/10}⌋ + 1`, the window top `Y = ⌊x^{1/3}⌋ + 2`, the
Bombieri–Vinogradov level `D = √x/(log x)^B` and the associated quantities
`σ = log D / log M`, `s_q = log (D/q) / log M`, `w = log (Y-1)/log M`, together with the
elementary eventual estimates used by the assembly of `h2`: the level is eventually well above
the window, `σ → 5` from below and `w → 10/3`.
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

open Commons.NumberTheory.Chen.ChenEight

/-- The sift limit `M = ⌊x^{1/10}⌋ + 1`. -/
def siftM (x : ℕ) : ℕ := Submission.chenSiftLimitTenth x

/-- The window top `Y = ⌊x^{1/3}⌋ + 2`. -/
def winY (x : ℕ) : ℕ := Submission.chenWindowTop x

/-- The Bombieri–Vinogradov level `D = √x / (log x)^B`. -/
def lvlD (B : ℝ) (x : ℕ) : ℝ := Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B

/-- `σ = log D / log M`. -/
def sigM (B : ℝ) (x : ℕ) : ℝ := Real.log (lvlD B x) / Real.log (siftM x : ℝ)

/-- `s_q = log (D/q) / log M`, the sieve level ratio of the residue class `q`. -/
def sVal (B : ℝ) (x q : ℕ) : ℝ := Real.log (lvlD B x / (q : ℝ)) / Real.log (siftM x : ℝ)

/-- `w = log (Y-1) / log M`. -/
def wVal (x : ℕ) : ℝ := Real.log ((winY x - 1 : ℕ) : ℝ) / Real.log (siftM x : ℝ)

/-- The cell threshold `L k = D · M^{-(3/2 + k/20)}`. -/
def thrL (B : ℝ) (x k : ℕ) : ℝ :=
  lvlD B x / (siftM x : ℝ) ^ (((3 : ℝ) / 2 + (k : ℝ) / 20))

/-! ## Elementary facts about `M` and `Y` -/

lemma siftM_eq (x : ℕ) : siftM x = ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1 := rfl
lemma winY_eq (x : ℕ) : winY x = ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 2 := rfl

lemma rpow_ten_lt_siftM (x : ℕ) : (x : ℝ) ^ ((1 : ℝ) / 10) < (siftM x : ℝ) := by
  have h := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 10))
  rw [siftM_eq]
  push_cast
  exact h

lemma siftM_le_rpow_add_one (x : ℕ) :
    (siftM x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) + 1 := by
  have h := Nat.floor_le (show (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) by positivity)
  rw [siftM_eq]
  push_cast
  linarith

lemma floor_rpow_three_le (x : ℕ) :
    ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

lemma winY_sub_one_eq (x : ℕ) : (winY x - 1 : ℕ) = ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1 := by
  rw [winY_eq]; omega

/-- `log M ≥ log x / 10` for `x ≥ 1`. -/
lemma log_siftM_ge {x : ℕ} (hx : 1 ≤ x) :
    Real.log (x : ℝ) / 10 ≤ Real.log (siftM x : ℝ) := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h1 : Real.log ((x : ℝ) ^ ((1 : ℝ) / 10)) ≤ Real.log (siftM x : ℝ) :=
    Real.log_le_log (by positivity) (le_of_lt (rpow_ten_lt_siftM x))
  rw [Real.log_rpow hx0 (1 / 10 : ℝ)] at h1
  linarith

/-- `log (Y-1) ≤ log x / 3 + log 2` for `x ≥ 1`. -/
lemma log_winY_sub_one_le {x : ℕ} (hx : 0 < x) :
    Real.log (((winY x - 1 : ℕ)) : ℝ) ≤ Real.log (x : ℝ) / 3 + Real.log 2 := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have h1 : ((winY x - 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 := floor_rpow_three_le x
    rw [winY_sub_one_eq]
    push_cast
    have h3 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx1 (by norm_num : (0:ℝ) ≤ 1/3)
      rwa [Real.one_rpow] at h
    linarith
  have hpos : (0 : ℝ) < ((winY x - 1 : ℕ) : ℝ) := by
    have : 0 < winY x - 1 := by
      rw [winY_sub_one_eq]; exact Nat.succ_pos _
    exact_mod_cast this
  have h4 := Real.log_le_log hpos h1
  have h5 : Real.log (2 * (x : ℝ) ^ ((1 : ℝ) / 3))
      = Real.log 2 + Real.log (x : ℝ) / 3 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    ring
  rw [h5] at h4
  linarith

/-! ## Eventual estimates -/

/-- For `s > 0` and `C ≥ 0`, eventually `C (log x)^b ≤ x^s`. -/
lemma eventually_const_mul_log_rpow_le {s b : ℝ} (hs : 0 < s) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ x : ℕ in Filter.atTop, C * Real.log (x : ℝ) ^ b ≤ (x : ℝ) ^ s := by
  have hlit : (fun x : ℝ => Real.log x ^ b) =o[Filter.atTop] (fun x : ℝ => x ^ s) :=
    isLittleO_log_rpow_rpow_atTop b hs
  have hcpos : (0 : ℝ) < 1 / (C + 1) := by positivity
  have h := (Asymptotics.isLittleO_iff.mp hlit) hcpos
  have hnat : ∀ᶠ x : ℕ in Filter.atTop,
      ‖Real.log (x : ℝ) ^ b‖ ≤ (1 / (C + 1)) * ‖(x : ℝ) ^ s‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hnat, Filter.eventually_ge_atTop 1] with x hx hx1
  have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1') b),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _)] at hx
  have hxnn : (0 : ℝ) ≤ (x : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hCc : C * (1 / (C + 1)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one (by linarith)).mpr (by linarith)
  calc C * Real.log (x : ℝ) ^ b
      ≤ C * ((1 / (C + 1)) * (x : ℝ) ^ s) := mul_le_mul_of_nonneg_left hx hC
    _ = (C * (1 / (C + 1))) * (x : ℝ) ^ s := by ring
    _ ≤ 1 * (x : ℝ) ^ s := mul_le_mul_of_nonneg_right hCc hxnn
    _ = (x : ℝ) ^ s := by ring

/-- `log x → ∞`. -/
lemma eventually_log_ge (c : ℝ) : ∀ᶠ x : ℕ in Filter.atTop, c ≤ Real.log (x : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop c)

/-- `M → ∞`. -/
lemma eventually_siftM_ge (N : ℕ) : ∀ᶠ x : ℕ in Filter.atTop, N ≤ siftM x := by
  filter_upwards [eventually_const_mul_log_rpow_le (s := (1:ℝ)/10) (b := 0) (by norm_num)
      (C := (N : ℝ) + 1) (by positivity), Filter.eventually_ge_atTop 1] with x hx hx1
  have hx' : (N : ℝ) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by simpa using hx
  have hx'' : ((N + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by push_cast; exact hx'
  have hN : N + 1 ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ := Nat.le_floor hx''
  rw [siftM_eq]
  omega

/-- `log M → ∞`. -/
lemma eventually_log_siftM_ge {c : ℝ} (hc : 1 ≤ c) :
    ∀ᶠ x : ℕ in Filter.atTop, c ≤ Real.log (siftM x : ℝ) := by
  filter_upwards [eventually_log_ge (10 * c), Filter.eventually_ge_atTop 1] with x hx hx1
  have h := log_siftM_ge (x := x) hx1
  linarith

/-- `log log x / log x → 0`. -/
lemma tendsto_loglog_div_log :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      Filter.atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h1.comp h2

/-- Eventually `M ≤ Y - 1`. -/
lemma eventually_siftM_le_winY : ∀ᶠ x : ℕ in Filter.atTop, siftM x ≤ winY x - 1 := by
  have hlt : ∀ᶠ x : ℕ in Filter.atTop, (siftM x : ℝ) ≤ ((winY x - 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_const_mul_log_rpow_le (s := (7:ℝ)/30) (b := 0) (by norm_num)
        (C := 4) (by norm_num), Filter.eventually_ge_atTop 1] with x hx hx1
    have hx' : (4:ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 30) := by simpa using hx
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1' (by norm_num : (0:ℝ) ≤ 1/10)
      rwa [Real.one_rpow] at h
    have hsplit : (x : ℝ) ^ ((1 : ℝ) / 3)
        = (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 30) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hA : (0:ℝ) < (x : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hx0 _
    have hAB : (x : ℝ) ^ ((1 : ℝ) / 10) * 4
        ≤ (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_left hx' hA.le
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 10) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [hsplit]
      calc (x : ℝ) ^ ((1 : ℝ) / 10) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 10) * 4 := by linarith [h1]
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 10) * (x : ℝ) ^ ((7 : ℝ) / 30) := hAB
    have h3 : ((winY x - 1 : ℕ) : ℝ) = ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) + 1 := by
      rw [winY_sub_one_eq]; push_cast; ring
    have h5 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) + 1 :=
      le_of_lt (Nat.lt_floor_add_one _)
    rw [h3]
    linarith [siftM_le_rpow_add_one x, h2, h5]
  filter_upwards [hlt] with x hx
  exact_mod_cast hx

/-- **`5 - ε ≤ σ` eventually.**  (The window-main-term estimate only improves as `σ` grows, and
`σ = 5 - O(log log x / log x) → 5` from below.) -/
lemma eventually_sigM_ge (B : ℝ) (hB : 0 < B) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ x : ℕ in Filter.atTop, 5 - ε ≤ sigM B x := by
  have hratio : ∀ᶠ x : ℕ in Filter.atTop,
      B * Real.log (Real.log (x : ℝ)) ≤ (ε / 20) * Real.log (x : ℝ) := by
    have hmem : ∀ᶠ y : ℝ in nhds (0:ℝ), y < ε / (20 * B) :=
      gt_mem_nhds (show (0:ℝ) < ε / (20 * B) by positivity)
    filter_upwards [tendsto_loglog_div_log.eventually hmem,
      eventually_log_ge (Real.exp (Real.exp 1))] with x hx hl2
    have hlogpos : 0 < Real.log (x : ℝ) := by
      have h1 : (1:ℝ) < Real.log (x : ℝ) := by
        have h2 : (1:ℝ) < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
        linarith
      linarith
    rw [div_lt_iff₀ hlogpos] at hx
    have h20B : (0:ℝ) < 20 * B := by positivity
    calc B * Real.log (Real.log (x : ℝ))
        ≤ B * (ε / (20 * B) * Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_of_lt hx) hB.le
      _ = (ε / 20) * Real.log (x : ℝ) := by field_simp
  filter_upwards [hratio, eventually_log_ge (max 1 (20 * (5 - ε) * Real.log 2 / ε)),
    eventually_log_ge (Real.exp 1), Filter.eventually_ge_atTop 1] with x hx hL hl1 hx1
  have hlogpos : 0 < Real.log (x : ℝ) := by
    have := Real.exp_pos 1
    linarith
  have hLge : 20 * (5 - ε) * Real.log 2 / ε ≤ Real.log (x : ℝ) := le_trans (le_max_right _ _) hL
  have h5log2 : (5 - ε) * Real.log 2 ≤ (ε / 20) * Real.log (x : ℝ) := by
    rw [div_le_iff₀ hε] at hLge
    nlinarith [hLge]
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  -- `log M ≤ log x / 10 + log 2`
  have hMeq : (siftM x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10) := by
    have h := siftM_le_rpow_add_one x
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
      have h0 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h0 (by norm_num : (0:ℝ) ≤ 1/10)
      rwa [Real.one_rpow] at h
    linarith
  have hlogM : Real.log (siftM x : ℝ) ≤ Real.log (x : ℝ) / 10 + Real.log 2 := by
    have hpos : 0 < (siftM x : ℝ) := by
      have : 0 < siftM x := by rw [siftM_eq]; omega
      exact_mod_cast this
    have h := Real.log_le_log hpos hMeq
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h
    linarith
  have hM1 : 0 < Real.log (siftM x : ℝ) := by
    have h := log_siftM_ge (x := x) hx1
    linarith
  have hDlog : Real.log (lvlD B x) = Real.log (x : ℝ) / 2 - B * Real.log (Real.log (x : ℝ)) := by
    rw [lvlD, Real.log_div (by positivity) (ne_of_gt (Real.rpow_pos_of_pos hlogpos B)),
      Real.log_sqrt hx0.le, Real.log_rpow hlogpos B]
  rw [sigM, hDlog]
  refine (le_div_iff₀ hM1).mpr ?_
  have hkey : (5 - ε) * (Real.log (x : ℝ) / 10 + Real.log 2)
      ≤ Real.log (x : ℝ) / 2 - B * Real.log (Real.log (x : ℝ)) := by
    nlinarith [hx, h5log2, hlogpos]
  have h5e : 0 ≤ 5 - ε := by linarith
  have h3 : (5 - ε) * Real.log (siftM x : ℝ)
      ≤ (5 - ε) * (Real.log (x : ℝ) / 10 + Real.log 2) :=
    mul_le_mul_of_nonneg_left hlogM h5e
  linarith [hkey, h3]

/-- **`w ≤ 10/3 + δ` eventually**, where `w = log (Y-1)/log M`. -/
lemma eventually_wVal_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in Filter.atTop, wVal x ≤ 10 / 3 + δ := by
  filter_upwards [eventually_log_ge (10 * Real.log 2 / δ), Filter.eventually_ge_atTop 2]
    with x hx hx2
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h1x : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos h1x
  have hx1le : 1 ≤ x := by omega
  have hM1 : 0 < Real.log (siftM x : ℝ) := by
    have h := log_siftM_ge (x := x) hx1le
    linarith
  have htenlog2 : 10 * Real.log 2 ≤ δ * Real.log (x : ℝ) := by
    rw [div_le_iff₀ hδ] at hx
    linarith
  have hdt : δ * Real.log (x : ℝ) / 10 ≥ Real.log 2 := by linarith
  rw [wVal, div_le_iff₀ hM1]
  have hnum := log_winY_sub_one_le (x := x) (by omega)
  have hstep : (10 / 3 + δ) * (Real.log (x : ℝ) / 10) ≤ (10 / 3 + δ) * Real.log (siftM x : ℝ) :=
    mul_le_mul_of_nonneg_left (log_siftM_ge (x := x) hx1le) (by linarith)
  have halg : (10 / 3 + δ) * (Real.log (x : ℝ) / 10) ≥ Real.log (x : ℝ) / 3 + Real.log 2 := by
    have h1 : δ * Real.log (x : ℝ) / 10 ≥ Real.log 2 := hdt
    nlinarith [hlogpos]
  linarith

/-- **The level is eventually well above the window.** -/
lemma eventually_lvlD_div_winY_ge (B : ℝ) (hB : 0 < B) (D₀ : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, D₀ ≤ lvlD B x / (winY x : ℝ) := by
  filter_upwards [eventually_const_mul_log_rpow_le (s := (1:ℝ)/6) (b := B) (by norm_num)
      (C := 3 * max D₀ 0 + 3) (by positivity), Filter.eventually_ge_atTop 2]
    with x hx hx1
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h1x : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos h1x
  have hlogB : 0 < Real.log (x : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos B
  have hYpos : 0 < (winY x : ℝ) := by
    rw [winY_eq]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊]
  have hYle : (winY x : ℝ) ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h2 := floor_rpow_three_le x
    have h3 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      have hx1' : (1 : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast (show 1 ≤ x by omega)
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1' (by norm_num : (0:ℝ) ≤ 1/3)
      rwa [Real.one_rpow] at h
    rw [winY_eq]
    push_cast
    linarith
  have hx13 : 0 < (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx0 _
  have hx16 : 0 < (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hx0 _
  -- `max D₀ 0 · (log x)^B ≤ x^{1/6}/3`
  have hM₀ : max D₀ 0 * Real.log (x : ℝ) ^ B ≤ (x : ℝ) ^ ((1 : ℝ) / 6) / 3 := by
    have h6 : 3 * max D₀ 0 ≤ 3 * max D₀ 0 + 3 := by norm_num
    have h7 : 3 * max D₀ 0 * Real.log (x : ℝ) ^ B
        ≤ (3 * max D₀ 0 + 3) * Real.log (x : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right h6 hlogB.le
    have h8 : (3 * max D₀ 0 + 3) * Real.log (x : ℝ) ^ B ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := hx
    linarith
  have hkey : D₀ * Real.log (x : ℝ) ^ B * (winY x : ℝ)
      ≤ (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h1 : D₀ * Real.log (x : ℝ) ^ B ≤ max D₀ 0 * Real.log (x : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB.le
    calc D₀ * Real.log (x : ℝ) ^ B * (winY x : ℝ)
        ≤ max D₀ 0 * Real.log (x : ℝ) ^ B * (3 * (x : ℝ) ^ ((1 : ℝ) / 3)) := by
          calc D₀ * Real.log (x : ℝ) ^ B * (winY x : ℝ)
              ≤ max D₀ 0 * Real.log (x : ℝ) ^ B * (winY x : ℝ) :=
                mul_le_mul_of_nonneg_right h1 hYpos.le
            _ ≤ max D₀ 0 * Real.log (x : ℝ) ^ B * (3 * (x : ℝ) ^ ((1 : ℝ) / 3)) :=
                mul_le_mul_of_nonneg_left hYle (by positivity)
      _ ≤ ((x : ℝ) ^ ((1 : ℝ) / 6) / 3) * (3 * (x : ℝ) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_right hM₀ (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 3) := by ring
  have hsplitsqrt : Real.sqrt (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  rw [lvlD, div_div]
  rw [le_div_iff₀ (by positivity : 0 < Real.log (x : ℝ) ^ B * (winY x : ℝ))]
  rw [hsplitsqrt]
  have hprod : D₀ * (Real.log (x : ℝ) ^ B * (winY x : ℝ))
      = D₀ * Real.log (x : ℝ) ^ B * (winY x : ℝ) := by ring
  rw [hprod]
  calc D₀ * Real.log (x : ℝ) ^ B * (winY x : ℝ)
      ≤ (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 3) := hkey
    _ = (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6) := by ring

/-- The level is at most `√x`. -/
lemma lvlD_le_sqrt (B : ℝ) (hB : 0 ≤ B) {x : ℕ} (hx : 8 ≤ x) :
    lvlD B x ≤ Real.sqrt (x : ℝ) := by
  rw [lvlD]
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (1:ℝ) ≤ Real.log (x:ℝ) := by
    have hx2 : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 8) hx2
    have h8 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h8] at h
    nlinarith [Real.log_two_gt_d9, hlog2, h]
  have hle : (1:ℝ) ≤ (Real.log (x:ℝ)) ^ B := Real.one_le_rpow hlog hB
  have hlogpos : 0 < Real.log (x:ℝ) := by linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hlogpos B)]
  nlinarith [Real.sqrt_nonneg (x:ℝ)]

/-- The level tends to infinity. -/
lemma eventually_lvlD_ge (B : ℝ) (hB : 0 < B) (A : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, A ≤ lvlD B x := by
  filter_upwards [eventually_lvlD_div_winY_ge B hB A, eventually_siftM_le_winY,
    eventually_siftM_ge 1] with x hx hle hM
  have hY1 : 1 ≤ winY x - 1 := le_trans hM hle
  have hY2 : 2 ≤ winY x := by omega
  have hYpos : 0 < (winY x : ℝ) := by exact_mod_cast (by omega : 0 < winY x)
  have hYge1 : (1 : ℝ) ≤ (winY x : ℝ) := by exact_mod_cast (by omega : 1 ≤ winY x)
  have h1 : lvlD B x / (winY x : ℝ) * (winY x : ℝ) = lvlD B x :=
    div_mul_cancel₀ _ (ne_of_gt hYpos)
  have h2 : A * (winY x : ℝ) ≤ lvlD B x := by
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hx hYpos.le
  rcases le_total 0 A with hA | hA
  · nlinarith [h2, hYge1, hA]
  · have hlvlD : 0 ≤ lvlD B x := by
      rw [lvlD]; positivity
    linarith

end

end Work.ChenPlan.H2
