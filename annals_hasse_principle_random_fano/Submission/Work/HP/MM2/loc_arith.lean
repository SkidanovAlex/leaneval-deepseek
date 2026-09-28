import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.w_arith

/-!
# `loc_arith` — the elementary eventual arithmetic behind the local estimate

Standing notation: `N = NN d n`, `L = log B`, `W = bigW (wOf B)`, `ℓ = log A`, with
`wOf B = L / log L` and `W` the primorial-type product of `Defs.lean`.

The file proves `Work.HP.MM2.loc_arith`: for `2 ≤ d ≤ n` there is `B₀` such that for every
`B ≥ B₀` and every `A` with `B^{5/6} ≤ A ≤ B²`, the nine inequalities of the statement hold.
Everything rests on two asymptotic ingredients,

* `bigW_le_pow` (`W ≤ B^ε` eventually for every `ε > 0`), and
* `log` is sub-polynomial,

packaged below as `la_pow_log_le_rpow`, `la_const_pow_log_mul_bigW_pow_le` and
`la_const_loglog_pow_le_log_pow`.
-/

namespace Work.HP.MM2

open Filter

/-- `(log B)^m ≤ B^e` eventually, for every fixed `m` and `e > 0`. -/
lemma la_pow_log_le_rpow (m : ℕ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ B in Filter.atTop, (Real.log B)^m ≤ B^e := by
  have h := isLittleO_log_rpow_rpow_atTop (m:ℝ) he
  rw [Asymptotics.isLittleO_iff] at h
  filter_upwards [h zero_lt_one, Filter.eventually_ge_atTop (1:ℝ)] with B hB hB1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) e)] at hB
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hB1) (m:ℝ))] at hB
  rw [Real.rpow_natCast] at hB
  simpa using hB

/-- `C · (log B)^m · W^k ≤ B^e` eventually, for every fixed `C`, `m`, `k > 0` and `e > 0`.
Here `W = bigW (wOf B)`, which is sub-polynomial by `bigW_le_pow`. -/
lemma la_const_pow_log_mul_bigW_pow_le (C : ℝ) (m k : ℕ) (hk : 0 < k) {e : ℝ}
    (he : 0 < e) :
    ∀ᶠ B in Filter.atTop, C * (Real.log B)^m * ((bigW (wOf B) : ℕ) : ℝ)^k ≤ B^e := by
  have hkn : ((k:ℝ)) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hδ : (0:ℝ) < e / (2 * (k:ℝ)) := by
    apply div_pos he; positivity
  obtain ⟨B₀, hB₀⟩ := bigW_le_pow (e / (2 * (k:ℝ))) hδ
  have hW : ∀ᶠ B in Filter.atTop, ((bigW (wOf B) : ℕ) : ℝ) ≤ B^(e/(2*(k:ℝ))) :=
    Filter.eventually_atTop.mpr ⟨B₀, hB₀⟩
  have h1 : ∀ᶠ B in Filter.atTop, C * (Real.log B)^m ≤ B^(e/2) := by
    have he4 : (0:ℝ) < e/4 := by linarith
    have hC : ∀ᶠ B in Filter.atTop, C ≤ B^(e/4) :=
      (tendsto_rpow_atTop he4).eventually_ge_atTop C
    have hlog : ∀ᶠ B in Filter.atTop, (Real.log B)^m ≤ B^(e/4) := by
      have h := isLittleO_log_rpow_rpow_atTop (m:ℝ) he4
      rw [Asymptotics.isLittleO_iff] at h
      filter_upwards [h zero_lt_one, Filter.eventually_ge_atTop (1:ℝ)] with B hB hB1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) (e/4))] at hB
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hB1) (m:ℝ))] at hB
      rw [Real.rpow_natCast] at hB
      simpa using hB
    filter_upwards [hC, hlog, Filter.eventually_ge_atTop (1:ℝ)] with B hc hl hB1
    have hlp : 0 ≤ (Real.log B)^m := pow_nonneg (Real.log_nonneg hB1) m
    have hbp : 0 ≤ B^(e/4) := Real.rpow_nonneg (by linarith) _
    calc C * (Real.log B)^m ≤ B^(e/4) * B^(e/4) := mul_le_mul hc hl hlp hbp
      _ = B^(e/2) := by rw [← Real.rpow_add (by linarith)]; ring_nf
  filter_upwards [hW, h1, Filter.eventually_ge_atTop (1:ℝ)] with B hWB h1B hB1
  have hBpos : (0:ℝ) < B := by linarith
  have heq : (B^(e/(2*(k:ℝ))))^k = B^(e/2) := by
    rw [← Real.rpow_natCast (B^(e/(2*(k:ℝ)))) k, ← Real.rpow_mul (le_of_lt hBpos)]
    congr 1
    field_simp
  have hWk : ((bigW (wOf B) : ℕ) : ℝ)^k ≤ B^(e/2) :=
    le_trans (pow_le_pow_left₀ (by positivity) hWB k) (le_of_eq heq)
  have hbk : 0 ≤ ((bigW (wOf B) : ℕ) : ℝ)^k := by positivity
  have hbp : 0 ≤ B^(e/2) := Real.rpow_nonneg (by linarith) _
  calc C * (Real.log B)^m * ((bigW (wOf B) : ℕ) : ℝ)^k
      ≤ B^(e/2) * B^(e/2) := mul_le_mul h1B hWk hbk hbp
    _ = B^e := by rw [← Real.rpow_add hBpos]; ring_nf

/-- `C · (log log B)^m ≤ (log B)^q` eventually, for fixed `C`, `m` and `q ≥ 1`. -/
lemma la_const_loglog_pow_le_log_pow (C : ℝ) (m q : ℕ) (hq : 0 < q) :
    ∀ᶠ B in Filter.atTop, C * (Real.log (Real.log B))^m ≤ (Real.log B)^q := by
  rcases lt_trichotomy C 0 with hC | hC | hC
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with B hB1
    have hB1' : 1 ≤ B := le_trans (Real.one_le_exp (zero_le_one)) hB1
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1'
    have hnn : 0 ≤ (Real.log B)^q := pow_nonneg hlogB0 q
    have hlogB1 : 1 ≤ Real.log B := by
      have := Real.log_le_log (Real.exp_pos 1) hB1
      rwa [Real.log_exp] at this
    have hm : 0 ≤ (Real.log (Real.log B))^m := pow_nonneg (Real.log_nonneg hlogB1) m
    have h1 : C * (Real.log (Real.log B))^m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hC) hm
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with B hB1
    rw [hC, zero_mul]
    exact pow_nonneg (Real.log_nonneg hB1) q
  · have h : (fun B : ℝ => (Real.log (Real.log B))^(m:ℝ)) =o[Filter.atTop]
        (fun B => (Real.log B)^(q:ℝ)) :=
      (isLittleO_log_rpow_rpow_atTop (m:ℝ) (by exact_mod_cast hq)).comp_tendsto
        Real.tendsto_log_atTop
    rw [Asymptotics.isLittleO_iff] at h
    filter_upwards [h (by positivity : 0 < C⁻¹), Filter.eventually_ge_atTop (Real.exp 1)]
      with B hB hB1
    have hB1' : 1 ≤ B := le_trans (Real.one_le_exp (zero_le_one)) hB1
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1'
    have hlogB1 : 1 ≤ Real.log B := by
      have := Real.log_le_log (Real.exp_pos 1) hB1
      rwa [Real.log_exp] at this
    have hloglog0 : 0 ≤ Real.log (Real.log B) := Real.log_nonneg hlogB1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hloglog0 (m:ℝ)),
        Real.norm_of_nonneg (Real.rpow_nonneg hlogB0 (q:ℝ)),
        Real.rpow_natCast, Real.rpow_natCast] at hB
    have := mul_le_mul_of_nonneg_left hB hC.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC), one_mul] at this

theorem loc_arith (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) (K : ℝ) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → ∀ A : ℝ, B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      1 ≤ A ∧ 1 ≤ Real.log A ∧ 1 ≤ Work.HP.wOf B ∧
      1 ≤ A / (Work.HP.bigW (Work.HP.wOf B) : ℝ) ∧ 1 ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) ∧
      (Work.HP.bigW (Work.HP.wOf B) : ℝ) ≤ A ∧
      K * (Real.log B) ^ 4 * (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ (Work.HP.NN d n + 4) / A
        ≤ 1 / Real.log A ∧
      K * (Real.log B) ^ 4 * (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ (Work.HP.NN d n + 4) /
        A ^ (Work.HP.NN d n - 2) ≤ 1 / Real.log A ∧
      K * Real.log A ≤
        (min (A / (Work.HP.bigW (Work.HP.wOf B) : ℝ)) (Work.HP.wOf B)) ^ (Work.HP.NN d n - 3) := by
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hN3 : 3 ≤ NN d n - 3 := by omega
  have hN2pos : 0 < NN d n - 2 := by omega
  have hNk : 0 < NN d n + 4 := by omega
  have hN4ge : (10:ℝ) ≤ ((NN d n + 4 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 10 ≤ NN d n + 4)
  have hN4pos : (0:ℝ) < ((NN d n + 4 : ℕ) : ℝ) := by linarith
  -- the exponent `δ` for `W ≤ B^δ`
  set δ : ℝ := 5 / (24 * ((NN d n + 4 : ℕ) : ℝ)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ_le512 : δ ≤ 5/12 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ_le56 : δ ≤ 5/6 := by linarith
  -- eventual inputs
  have hWle : ∀ᶠ B in Filter.atTop, ((bigW (wOf B) : ℕ) : ℝ) ≤ B^δ := by
    obtain ⟨B₀, hB₀⟩ := bigW_le_pow δ hδpos
    exact Filter.eventually_atTop.mpr ⟨B₀, hB₀⟩
  have hW7 : ∀ᶠ B in Filter.atTop,
      (2 * |K|) * (Real.log B)^5 * ((bigW (wOf B) : ℕ) : ℝ)^(NN d n + 4)
        ≤ B^((5:ℝ)/6) :=
    la_const_pow_log_mul_bigW_pow_le (2*|K|) 5 (NN d n + 4) hNk (by norm_num)
  have hm8pos : (0:ℝ) < ((5:ℝ)/6) * ((NN d n - 2 : ℕ) : ℝ) := by
    have h1 : (0:ℝ) < ((NN d n - 2 : ℕ) : ℝ) := by exact_mod_cast hN2pos
    positivity
  have hW8 : ∀ᶠ B in Filter.atTop,
      (2 * |K|) * (Real.log B)^5 * ((bigW (wOf B) : ℕ) : ℝ)^(NN d n + 4)
        ≤ B^(((5:ℝ)/6) * ((NN d n - 2 : ℕ) : ℝ)) :=
    la_const_pow_log_mul_bigW_pow_le (2*|K|) 5 (NN d n + 4) hNk hm8pos
  have hlogle : ∀ᶠ B in Filter.atTop, Real.log B ≤ B^((5:ℝ)/12) := by
    simpa [pow_one] using la_pow_log_le_rpow 1 (show (0:ℝ) < 5/12 by norm_num)
  have hloglogbound : ∀ᶠ B in Filter.atTop,
      (2 * |K|) * (Real.log (Real.log B))^3 ≤ (Real.log B)^2 :=
    la_const_loglog_pow_le_log_pow (2*|K|) 3 2 (by norm_num)
  have hBge1 : ∀ᶠ B in Filter.atTop, (1:ℝ) ≤ B := Filter.eventually_ge_atTop 1
  have hlogBge2 : ∀ᶠ B in Filter.atTop, (2:ℝ) ≤ Real.log B :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have hloglog_ge1 : ∀ᶠ B in Filter.atTop, (1:ℝ) ≤ Real.log (Real.log B) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have hw1ev : ∀ᶠ B in Filter.atTop, (1:ℝ) ≤ wOf B :=
    tendsto_wOf_atTop.eventually_ge_atTop 1
  -- main eventual statement
  have hev : ∀ᶠ B in Filter.atTop, ∀ A : ℝ, B^((5:ℝ)/6) ≤ A → A ≤ B^2 →
      1 ≤ A ∧ 1 ≤ Real.log A ∧ 1 ≤ wOf B ∧
      1 ≤ A / (bigW (wOf B) : ℝ) ∧ 1 ≤ (bigW (wOf B) : ℝ) ∧
      (bigW (wOf B) : ℝ) ≤ A ∧
      K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) / A ≤ 1 / Real.log A ∧
      K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) / A^(NN d n - 2)
        ≤ 1 / Real.log A ∧
      K * Real.log A ≤ (min (A / (bigW (wOf B) : ℝ)) (wOf B))^(NN d n - 3) := by
    filter_upwards [hBge1, hlogBge2, hloglog_ge1, hw1ev, hWle, hW7, hW8, hlogle, hloglogbound]
      with B hBge1 hlogBge2 hloglog_ge1 hw1 hWle hW7 hW8 hlogle hloglogbound
    intro A hA1 hA2
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBge1
    have hLpos : 0 < Real.log B := by linarith
    have hWge1 : (1:ℝ) ≤ (bigW (wOf B) : ℝ) := by
      exact_mod_cast one_le_bigW (wOf B)
    have hWpos : 0 < (bigW (wOf B) : ℝ) := lt_of_lt_of_le zero_lt_one hWge1
    -- item 1
    have hA_ge1 : 1 ≤ A := le_trans (Real.one_le_rpow hBge1 (by norm_num)) hA1
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge1
    -- log A
    have hlogA_ge1 : 1 ≤ Real.log A := by
      have h1 : Real.log (B ^ ((5:ℝ)/6)) ≤ Real.log A :=
        Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hA1
      rw [Real.log_rpow hBpos] at h1
      nlinarith [h1, hlogBge2]
    have hlogA_nonneg : 0 ≤ Real.log A := le_of_lt (lt_of_lt_of_le zero_lt_one hlogA_ge1)
    have hlogA_le : Real.log A ≤ 2 * Real.log B := by
      have h1 : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hApos hA2
      rw [Real.log_pow] at h1
      simpa using h1
    -- wOf ≤ log B and wOf ≤ B^{5/12}
    have hloglogpos : 0 < Real.log (Real.log B) := lt_of_lt_of_le zero_lt_one hloglog_ge1
    have hw_le_logB : wOf B ≤ Real.log B := by
      rw [wOf, div_le_iff₀ hloglogpos]
      exact le_mul_of_one_le_right hLpos.le hloglog_ge1
    have hw_le : wOf B ≤ B^((5:ℝ)/12) := le_trans hw_le_logB hlogle
    -- item 4 and the min
    have h5_12δ : (5:ℝ)/12 + δ ≤ 5/6 := by linarith
    have hAW : wOf B ≤ A / (bigW (wOf B) : ℝ) := by
      rw [le_div_iff₀ hWpos]
      calc wOf B * (bigW (wOf B) : ℝ)
          ≤ B^((5:ℝ)/12) * B^δ :=
            mul_le_mul hw_le hWle hWpos.le (Real.rpow_nonneg hBpos.le _)
        _ = B^((5:ℝ)/12 + δ) := (Real.rpow_add hBpos _ _).symm
        _ ≤ B^((5:ℝ)/6) := Real.rpow_le_rpow_of_exponent_le hBge1 h5_12δ
        _ ≤ A := hA1
    -- item 6
    have h6 : (bigW (wOf B) : ℝ) ≤ A := by
      have h1 : B^δ ≤ B^((5:ℝ)/6) := Real.rpow_le_rpow_of_exponent_le hBge1 hδ_le56
      exact le_trans (le_trans hWle h1) hA1
    -- cross-multiplied key bound
    have hKW_le : K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4)
        ≤ |K| * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hLpos.le 4))
        (pow_nonneg hWpos.le (NN d n + 4))
    have hstep : K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * Real.log A
        ≤ |K| * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * (2 * Real.log B) :=
      mul_le_mul hKW_le hlogA_le hlogA_nonneg (by positivity)
    -- item 7
    have h7 : K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) / A
        ≤ 1 / Real.log A := by
      rw [div_le_div_iff₀ hApos (lt_of_lt_of_le zero_lt_one hlogA_ge1)]
      calc K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * Real.log A
          ≤ |K| * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * (2 * Real.log B) := hstep
        _ = 2 * |K| * (Real.log B)^5 * (bigW (wOf B) : ℝ)^(NN d n + 4) := by ring
        _ ≤ B^((5:ℝ)/6) := hW7
        _ ≤ A := hA1
        _ = 1 * A := by ring
    -- item 8
    have h8 : K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) / A^(NN d n - 2)
        ≤ 1 / Real.log A := by
      rw [div_le_div_iff₀ (pow_pos hApos _) (lt_of_lt_of_le zero_lt_one hlogA_ge1)]
      have heq : (B^((5:ℝ)/6))^(NN d n - 2)
          = B^(((5:ℝ)/6) * ((NN d n - 2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast (B^((5:ℝ)/6)) (NN d n - 2),
            ← Real.rpow_mul hBpos.le (5/6) ((NN d n - 2 : ℕ) : ℝ)]
      have hApow : B^(((5:ℝ)/6) * ((NN d n - 2 : ℕ) : ℝ)) ≤ A^(NN d n - 2) := by
        rw [← heq]
        exact pow_le_pow_left₀ (Real.rpow_nonneg hBpos.le _) hA1 _
      calc K * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * Real.log A
          ≤ |K| * (Real.log B)^4 * (bigW (wOf B) : ℝ)^(NN d n + 4) * (2 * Real.log B) := hstep
        _ = 2 * |K| * (Real.log B)^5 * (bigW (wOf B) : ℝ)^(NN d n + 4) := by ring
        _ ≤ B^(((5:ℝ)/6) * ((NN d n - 2 : ℕ) : ℝ)) := hW8
        _ ≤ A^(NN d n - 2) := hApow
        _ = 1 * A^(NN d n - 2) := by ring
    -- item 9
    have hstep9 : 2 * |K| * Real.log B ≤ (wOf B)^3 := by
      rw [wOf, div_pow, le_div_iff₀ (by positivity : 0 < (Real.log (Real.log B))^3)]
      calc 2 * |K| * Real.log B * (Real.log (Real.log B))^3
          = (2 * |K| * (Real.log (Real.log B))^3) * Real.log B := by ring
        _ ≤ (Real.log B)^2 * Real.log B :=
            mul_le_mul_of_nonneg_right hloglogbound hLpos.le
        _ = (Real.log B)^3 := by ring
    have hw3 : 2 * |K| * Real.log B ≤ (wOf B)^(NN d n - 3) :=
      le_trans hstep9 (pow_le_pow_right₀ hw1 hN3)
    have h9item : K * Real.log A
        ≤ (min (A / (bigW (wOf B) : ℝ)) (wOf B))^(NN d n - 3) := by
      rw [min_eq_right hAW]
      calc K * Real.log A ≤ |K| * Real.log A :=
            mul_le_mul_of_nonneg_right (le_abs_self K) hlogA_nonneg
        _ ≤ |K| * (2 * Real.log B) := mul_le_mul_of_nonneg_left hlogA_le (abs_nonneg K)
        _ = 2 * |K| * Real.log B := by ring
        _ ≤ (wOf B)^(NN d n - 3) := hw3
    exact ⟨hA_ge1, hlogA_ge1, hw1, le_trans hw1 hAW, hWge1, h6, h7, h8, h9item⟩
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨B₀, fun B hB A hA1 hA2 => hB₀ B hB A hA1 hA2⟩

end Work.HP.MM2
