import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.w_arith
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.MDEstimates.pairS0_arith

namespace Work.HP.MM2

open Filter

/-- `C · (log B)^p ≤ B^ε` eventually, for every fixed `C`, `p` and `ε > 0`. -/
lemma eventually_const_mul_log_pow_le_rpow (C : ℝ) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℝ in Filter.atTop, C * Real.log B ^ p ≤ B ^ ε := by
  have h := isLittleO_log_rpow_rpow_atTop (p : ℝ) hε
  rw [Asymptotics.isLittleO_iff] at h
  have hc : (0:ℝ) < 1 / (|C| + 1) := by positivity
  filter_upwards [h hc, eventually_ge_atTop (1:ℝ)] with B hB hB1
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hlog_nn : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hnorm1 : ‖Real.log B ^ (p:ℝ)‖ = Real.log B ^ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog_nn _), Real.rpow_natCast]
  have hnorm2 : ‖B ^ ε‖ = B ^ ε := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hBpos.le ε)]
  rw [hnorm1, hnorm2] at hB
  calc C * Real.log B ^ p ≤ |C| * Real.log B ^ p :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hlog_nn p)
    _ ≤ |C| * ((1/(|C|+1)) * B^ε) := mul_le_mul_of_nonneg_left hB (abs_nonneg C)
    _ = (|C|/(|C|+1)) * B^ε := by ring
    _ ≤ 1 * B^ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hBpos.le ε)
        rw [div_le_one (by positivity)]; linarith [abs_nonneg C]
    _ = B^ε := one_mul _

/-- `C · log B ≤ (wOf B)^3` eventually, for every fixed `C`. -/
lemma eventually_const_mul_log_le_wOf_cube (C : ℝ) :
    ∀ᶠ B : ℝ in Filter.atTop, C * Real.log B ≤ (wOf B) ^ 3 := by
  have hlog : ∀ᶠ u : ℝ in Filter.atTop, C * Real.log u ^ 3 ≤ u ^ (((2 : ℕ) : ℝ)) :=
    eventually_const_mul_log_pow_le_rpow C 3 (by norm_num)
  have hlognat : ∀ᶠ u : ℝ in Filter.atTop, C * Real.log u ^ 3 ≤ u ^ 2 := by
    filter_upwards [hlog] with u hu
    rwa [Real.rpow_natCast] at hu
  have hcomp : ∀ᶠ B : ℝ in Filter.atTop, C * Real.log (Real.log B) ^ 3 ≤ (Real.log B)^2 :=
    Real.tendsto_log_atTop.eventually hlognat
  filter_upwards [hcomp, Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)]
    with B h1 h2
  have hlogB : 0 < Real.log B := lt_of_lt_of_le (Real.exp_pos 1) h2
  have hll : 0 < Real.log (Real.log B) := by
    have h3 := Real.log_le_log (Real.exp_pos 1) h2
    rw [Real.log_exp] at h3
    linarith
  have hcube : (wOf B)^3 = (Real.log B)^3 / (Real.log (Real.log B))^3 := by
    rw [wOf, div_pow]
  rw [hcube]
  rw [le_div_iff₀ (by positivity)]
  have hmul : (C * Real.log (Real.log B)^3) * Real.log B ≤ (Real.log B)^2 * Real.log B :=
    mul_le_mul_of_nonneg_right h1 hlogB.le
  have h2' : (Real.log B)^2 * Real.log B = (Real.log B)^3 := by ring
  rw [h2'] at hmul
  nlinarith [hmul]

/-- **Arithmetic core.** `5 (N-2)/24 > d/(n+1-d)` for `2 ≤ d ≤ n`, `(d,n) ≠ (2,2)`,
where `N = NN d n = C(n+d,d)`.  Uses `NN_eq_choose` and the Vandermonde lower bound
`choose_lower`: `N ≥ n d + C(n,2) C(d,2)`. -/
theorem mix_key_arith_local (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    0 < 5 * ((NN d n : ℝ) - 2) / 24 - (d : ℝ) / ((n : ℝ) + 1 - d) := by
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    have hd2 : d = 2 := by omega
    exact h22 (by simp [hd2, hn2])
  set N0 : ℝ := (NN d n : ℝ) with hNdef
  set m : ℝ := (n : ℝ) + 1 - d with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hm1 : (1:ℝ) ≤ m := by
    rw [hmdef]
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hlow : (n:ℝ) * (d:ℝ) + ((n.choose 2 : ℕ):ℝ) * ((d.choose 2 : ℕ):ℝ) ≤ N0 := by
    rw [hNdef, Work.HP.MDEstimates.NN_eq_choose]
    exact Work.HP.MDEstimates.choose_lower d n hd
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
  have hcn3 : (3:ℝ) ≤ ((n.choose 2 : ℕ):ℝ) := by
    have h : (3:ℕ) ≤ n.choose 2 := by
      have hh := Nat.choose_le_choose 2 hn3
      norm_num at hh
      exact hh
    exact_mod_cast h
  have hkey5 : (24:ℝ) * (d:ℝ) < 5 * (N0 - 2) * m := by
    by_cases hd3 : 3 ≤ d
    · -- d ≥ 3
      have hcd3 : (3:ℝ) ≤ ((d.choose 2 : ℕ):ℝ) := by
        have h : (3:ℕ) ≤ d.choose 2 := by
          have hh := Nat.choose_le_choose 2 hd3
          norm_num at hh
          exact hh
        exact_mod_cast h
      have hdd : (d:ℝ) * (d:ℝ) ≤ (n:ℝ) * (d:ℝ) := by
        have hnd : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
        nlinarith [hnd, hdR]
      have h9 : (9:ℝ) ≤ ((n.choose 2 : ℕ):ℝ) * ((d.choose 2 : ℕ):ℝ) := by
        nlinarith [hcn3, hcd3]
      have hN : (d:ℝ)^2 + 9 ≤ N0 := by
        have hst : (d:ℝ)^2 + 9 ≤ (n:ℝ)*(d:ℝ) + ((n.choose 2 : ℕ):ℝ)*((d.choose 2 : ℕ):ℝ) := by
          nlinarith [hdd, h9]
        linarith [hst, hlow]
      have hquad : (24:ℝ) * (d:ℝ) < 5 * ((d:ℝ)^2 + 7) := by
        nlinarith [sq_nonneg (5*(d:ℝ) - 12)]
      have hdm : (d:ℝ)^2 + 7 ≤ N0 - 2 := by linarith [hN]
      have hA : 5 * ((d:ℝ)^2 + 7) ≤ 5 * (N0 - 2) := by linarith [hdm]
      have hnn5 : (0:ℝ) ≤ 5 * (N0 - 2) := by linarith [hA, sq_nonneg (d:ℝ)]
      have hB : 5 * (N0 - 2) * 1 ≤ 5 * (N0 - 2) * m :=
        mul_le_mul_of_nonneg_left hm1 hnn5
      have hC : 5 * ((d:ℝ)^2 + 7) ≤ 5 * (N0 - 2) * m := by
        refine le_trans hA ?_
        simpa using hB
      linarith [hquad, hC]
    · -- d = 2
      have hd2 : d = 2 := by omega
      have hm2 : (2:ℝ) ≤ m := by rw [hmdef, hd2]; push_cast; linarith [hnR]
      have hN9 : (9:ℝ) ≤ N0 := by
        have hst : (9:ℝ) ≤ (n:ℝ) * (d:ℝ) + ((n.choose 2 : ℕ):ℝ) * ((d.choose 2 : ℕ):ℝ) := by
          rw [hd2]
          norm_num
          nlinarith [hcn3, hnR]
        linarith [hst, hlow]
      have hN7 : (7:ℝ) ≤ N0 - 2 := by linarith [hN9]
      have h70 : (70:ℝ) ≤ 5 * (N0 - 2) * m := by
        have h1 : 5 * (7:ℝ) ≤ 5 * (N0 - 2) := by linarith [hN7]
        have h2 : 5 * (7:ℝ) * 2 ≤ 5 * (N0 - 2) * 2 :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
        have h3 : 5 * (N0 - 2) * 2 ≤ 5 * (N0 - 2) * m :=
          mul_le_mul_of_nonneg_left hm2 (by linarith [hN7])
        norm_num at h2
        linarith [h2, h3]
      have h24 : (24:ℝ) * (d:ℝ) < 70 := by rw [hd2]; norm_num
      linarith [h70, h24]
  have hfin : (d:ℝ) / m < 5 * (N0 - 2) / 24 := by
    rw [div_lt_iff₀ hmpos, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0:ℝ) < 24)]
    linarith [hkey5]
  exact sub_pos.mpr hfin

theorem mix_arith (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) (K : ℝ) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → ∀ A : ℝ, B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x : Fin (n + 1) → ℤ, Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
      1 ≤ A ∧ 1 ≤ Real.log A ∧ 1 ≤ Work.HP.wOf B ∧
      1 ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) ∧
      (Work.HP.bigW (Work.HP.wOf B) : ℝ) ≤ A ∧
      K * Real.log B * Real.log A ≤ A ^ ((1 : ℝ) / 4) ∧
      K * (Real.log A) ^ 4 * (Work.HP.bigW (Work.HP.wOf B) : ℝ) *
          Work.HP.eNorm (Work.HP.veronese d n x) /
          A ^ (((Work.HP.NN d n - 2 : ℕ) : ℝ) / 4) ≤ 1 ∧
      K * (Real.log A) ^ 2 / A ^ (((Work.HP.NN d n - 3 : ℕ) : ℝ) / 4) ≤ 1 ∧
      K * Real.log A ≤ (Work.HP.wOf B) ^ (Work.HP.NN d n - 3) := by
  obtain ⟨c₁, c₂, hc₁pos, hc₂pos, hbnd⟩ := eNorm_veronese_bounds d n (by omega : 1 ≤ d)
  set N : ℕ := NN d n with hNdef
  have hN6 : 6 ≤ N := by rw [hNdef]; exact six_le_NN d n hd hdn
  have hN3le : 3 ≤ N - 3 := by omega
  set m : ℝ := (n : ℝ) + 1 - d with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  set f : ℝ := 5 * ((N : ℝ) - 2) / 24 - (d : ℝ) / m with hfdef
  have hfpos : 0 < f := by
    rw [hfdef]
    have hkey := mix_key_arith_local d n hd hdn h22
    rwa [← hNdef, ← hmdef] at hkey
  set e7 : ℝ := (((N - 2 : ℕ)) : ℝ) / 4 with he7def
  set e8 : ℝ := (((N - 3 : ℕ)) : ℝ) / 4 with he8def
  have he7pos : 0 < e7 := by
    rw [he7def]
    have : (0:ℝ) < ((N - 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 2 by omega)
    positivity
  have he8pos : 0 < e8 := by
    rw [he8def]
    have : (0:ℝ) < ((N - 3 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 3 by omega)
    positivity
  have hδ8pos : 0 < (5:ℝ)/6 * e8 := by positivity
  have hN2cast : (((N - 2 : ℕ)) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
  have hfe7 : (5:ℝ)/6 * e7 = f + (d:ℝ)/m := by
    rw [he7def, hN2cast, hfdef]; ring
  -- eventual inputs
  have hW56 : ∀ᶠ B : ℝ in Filter.atTop, (bigW (wOf B) : ℝ) ≤ B ^ ((5:ℝ)/6) := by
    obtain ⟨B₀, hB₀⟩ := bigW_le_pow ((5:ℝ)/6) (by norm_num)
    exact Filter.eventually_atTop.mpr ⟨B₀, hB₀⟩
  have hWf2 : ∀ᶠ B : ℝ in Filter.atTop, (bigW (wOf B) : ℝ) ≤ B ^ (f/2) := by
    obtain ⟨B₀, hB₀⟩ := bigW_le_pow (f/2) (by linarith)
    exact Filter.eventually_atTop.mpr ⟨B₀, hB₀⟩
  have hev : ∀ᶠ B : ℝ in Filter.atTop,
      (1:ℝ) ≤ B ∧ (2:ℝ) ≤ Real.log B ∧ (1:ℝ) ≤ Real.log (Real.log B) ∧
      1 ≤ wOf B ∧
      (bigW (wOf B) : ℝ) ≤ B ^ ((5:ℝ)/6) ∧
      (bigW (wOf B) : ℝ) ≤ B ^ (f/2) ∧
      2 * |K| * (Real.log B)^2 ≤ B ^ ((5:ℝ)/24) ∧
      |K| * c₂ * 16 * (Real.log B)^4 ≤ B ^ (f/2) ∧
      |K| * 4 * (Real.log B)^2 ≤ B ^ ((5:ℝ)/6 * e8) ∧
      2 * |K| * Real.log B ≤ (wOf B)^3 := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
      tendsto_wOf_atTop.eventually_ge_atTop 1, hW56, hWf2,
      eventually_const_mul_log_pow_le_rpow (2 * |K|) 2 (ε := (5:ℝ)/24) (by norm_num),
      eventually_const_mul_log_pow_le_rpow (|K| * c₂ * 16) 4 (ε := f/2) (by linarith),
      eventually_const_mul_log_pow_le_rpow (|K| * 4) 2 (ε := (5:ℝ)/6*e8) hδ8pos,
      eventually_const_mul_log_le_wOf_cube (2 * |K|)]
      with B h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨B₀, fun B hB => ?_⟩
  intro A hA1 hA2 x hx
  obtain ⟨hBge1, hlogBge2, hloglogB1, hw1, hW56', hWf2', hK6, hK7, hK8, hK9⟩ := hB₀ B hB
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBge1
  have hLpos : 0 < Real.log B := by linarith
  have hLnn : 0 ≤ Real.log B := le_of_lt hLpos
  have hWge1 : (1:ℝ) ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
  have hWpos : 0 < (bigW (wOf B) : ℝ) := lt_of_lt_of_le zero_lt_one hWge1
  -- item 1
  have hAge1 : 1 ≤ A := le_trans (Real.one_le_rpow hBge1 (by norm_num)) hA1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAge1
  -- item 2
  have hlogA_ge1 : 1 ≤ Real.log A := by
    have h1 : Real.log (B ^ ((5:ℝ)/6)) ≤ Real.log A :=
      Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hA1
    rw [Real.log_rpow hBpos] at h1
    nlinarith [h1, hlogBge2]
  have hlogAnn : 0 ≤ Real.log A := le_of_lt (lt_of_lt_of_le zero_lt_one hlogA_ge1)
  have hlogA_le : Real.log A ≤ 2 * Real.log B := by
    have h1 : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hApos hA2
    rw [Real.log_pow] at h1
    norm_num at h1
    linarith
  -- item 6
  have hitem6 : K * Real.log B * Real.log A ≤ A ^ ((1:ℝ)/4) := by
    have hA14 : B ^ ((5:ℝ)/24) ≤ A ^ ((1:ℝ)/4) := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le ((5:ℝ)/6)) hA1
        (by norm_num : (0:ℝ) ≤ 1/4)
      rwa [← Real.rpow_mul hBpos.le ((5:ℝ)/6) ((1:ℝ)/4),
        show (5:ℝ)/6 * ((1:ℝ)/4) = (5:ℝ)/24 by norm_num] at h1
    have hstep1 : K * Real.log B * Real.log A ≤ |K| * Real.log B * Real.log A := by
      have h1 : K * Real.log B ≤ |K| * Real.log B :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hLnn
      exact mul_le_mul_of_nonneg_right h1 hlogAnn
    calc K * Real.log B * Real.log A ≤ |K| * Real.log B * Real.log A := hstep1
      _ ≤ |K| * Real.log B * (2 * Real.log B) :=
          mul_le_mul_of_nonneg_left hlogA_le (by positivity)
      _ = 2 * |K| * (Real.log B)^2 := by ring
      _ ≤ B ^ ((5:ℝ)/24) := hK6
      _ ≤ A ^ ((1:ℝ)/4) := hA14
  -- exponent bound on the Veronese image
  have hxpow : (eNorm x)^d ≤ B ^ ((d:ℝ)/m) := by
    have h1 : (eNorm x)^d ≤ (B ^ (1/m))^d :=
      pow_le_pow_left₀ (eNorm_toR_nonneg x) hx d
    have h2 : (B ^ (1/m))^d = B ^ ((d:ℝ)/m) := by
      rw [← Real.rpow_natCast (B ^ (1/m)) d, ← Real.rpow_mul hBpos.le]
      congr 1
      ring
    rw [h2] at h1; exact h1
  have hEpow : eNorm (veronese d n x) ≤ c₂ * B ^ ((d:ℝ)/m) :=
    le_trans (hbnd x).2 (mul_le_mul_of_nonneg_left hxpow hc₂pos.le)
  -- item 7
  have hitem7 : K * (Real.log A)^4 * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) / A ^ e7 ≤ 1 := by
    have hAe7pos : 0 < A ^ e7 := Real.rpow_pos_of_pos hApos e7
    have hlogA4 : (Real.log A)^4 ≤ 16 * (Real.log B)^4 := by
      have h := pow_le_pow_left₀ hlogAnn hlogA_le 4
      calc (Real.log A)^4 ≤ (2 * Real.log B)^4 := h
        _ = 16 * (Real.log B)^4 := by ring
    have hAe7 : B ^ ((5:ℝ)/6 * e7) ≤ A ^ e7 := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le ((5:ℝ)/6)) hA1 he7pos.le
      rwa [← Real.rpow_mul hBpos.le ((5:ℝ)/6) e7] at h1
    rw [div_le_one hAe7pos]
    have hEnn : 0 ≤ eNorm (veronese d n x) := eNorm_toR_nonneg _
    calc K * (Real.log A)^4 * (bigW (wOf B) : ℝ) * eNorm (veronese d n x)
        ≤ |K| * (Real.log A)^4 * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) := by
          have h1 : K * (Real.log A)^4 ≤ |K| * (Real.log A)^4 :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hlogAnn 4)
          have h2 : K * (Real.log A)^4 * (bigW (wOf B) : ℝ)
              ≤ |K| * (Real.log A)^4 * (bigW (wOf B) : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hWpos.le
          exact mul_le_mul_of_nonneg_right h2 hEnn
      _ ≤ (|K| * (16 * (Real.log B)^4) * B ^ (f/2)) * (c₂ * B ^ ((d:ℝ)/m)) := by
          have hAB : |K| * (Real.log A)^4 ≤ |K| * (16 * (Real.log B)^4) :=
            mul_le_mul_of_nonneg_left hlogA4 (abs_nonneg K)
          have h3 : |K| * (Real.log A)^4 * (bigW (wOf B) : ℝ)
              ≤ (|K| * (16 * (Real.log B)^4)) * B ^ (f/2) :=
            mul_le_mul hAB hWf2' hWpos.le (by positivity)
          exact mul_le_mul h3 hEpow hEnn (by positivity)
      _ = (|K| * c₂ * 16 * (Real.log B)^4) * (B ^ (f/2) * B ^ ((d:ℝ)/m)) := by ring
      _ ≤ A ^ e7 := by
          rw [← Real.rpow_add hBpos]
          have h7a : (|K| * c₂ * 16 * (Real.log B)^4) * B ^ (f/2 + (d:ℝ)/m)
              ≤ B ^ (f/2) * B ^ (f/2 + (d:ℝ)/m) :=
            mul_le_mul_of_nonneg_right hK7 (Real.rpow_nonneg hBpos.le _)
          have h7b : B ^ (f/2) * B ^ (f/2 + (d:ℝ)/m) = B ^ (f + (d:ℝ)/m) := by
            rw [← Real.rpow_add hBpos]; congr 1; ring
          have h7c : B ^ (f + (d:ℝ)/m) = B ^ ((5:ℝ)/6 * e7) := by rw [hfe7]
          exact h7a.trans (h7b.le.trans (h7c.le.trans hAe7))
  -- item 8
  have hitem8 : K * (Real.log A)^2 / A ^ e8 ≤ 1 := by
    have hAe8pos : 0 < A ^ e8 := Real.rpow_pos_of_pos hApos e8
    have hsq : (Real.log A)^2 ≤ 4 * (Real.log B)^2 := by
      have h := pow_le_pow_left₀ hlogAnn hlogA_le 2
      calc (Real.log A)^2 ≤ (2 * Real.log B)^2 := h
        _ = 4 * (Real.log B)^2 := by ring
    have hAe8 : B ^ ((5:ℝ)/6 * e8) ≤ A ^ e8 := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le ((5:ℝ)/6)) hA1 he8pos.le
      rwa [← Real.rpow_mul hBpos.le ((5:ℝ)/6) e8] at h1
    rw [div_le_one hAe8pos]
    calc K * (Real.log A)^2 ≤ |K| * (Real.log A)^2 :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
      _ ≤ |K| * (4 * (Real.log B)^2) := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
      _ = |K| * 4 * (Real.log B)^2 := by ring
      _ ≤ B ^ ((5:ℝ)/6 * e8) := hK8
      _ ≤ A ^ e8 := hAe8
  -- item 9
  have hitem9 : K * Real.log A ≤ (wOf B) ^ (N - 3) := by
    calc K * Real.log A ≤ |K| * Real.log A :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hlogAnn
      _ ≤ |K| * (2 * Real.log B) := mul_le_mul_of_nonneg_left hlogA_le (abs_nonneg K)
      _ = 2 * |K| * Real.log B := by ring
      _ ≤ (wOf B)^3 := hK9
      _ ≤ (wOf B)^(N - 3) := pow_le_pow_right₀ hw1 hN3le
  exact ⟨hAge1, hlogA_ge1, hw1, hWge1, le_trans hW56' hA1, hitem6, hitem7, hitem8, hitem9⟩

end Work.HP.MM2
