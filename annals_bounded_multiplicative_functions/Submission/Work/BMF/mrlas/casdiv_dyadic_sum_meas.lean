import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.mrlas.casdiv_dyadic_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BMF.mrlas

open MeasureTheory Set intervalIntegral
open scoped BigOperators

/-- `1 / 2^k = (1/2)^k`. -/
lemma one_div_two_pow (k : ℕ) : (1 : ℝ) / (2 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
  rw [eq_comm, div_pow, one_pow]

/-- `(1/2)^n ≤ (1/2)^m` for `m ≤ n`. -/
lemma half_pow_le {m n : ℕ} (h : m ≤ n) : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m := by
  rw [← one_div_two_pow n, ← one_div_two_pow m]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) h

/-- The geometric sum `∑_{k<n} 1/2^{k+1} = 1 - 2^{-n} ≤ 1`. -/
lemma sum_one_div_two_pow (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / (2 : ℝ) ^ (k + 1)) = 1 - (1 / 2 : ℝ) ^ n := by
  rw [Finset.sum_congr rfl (fun k _ => one_div_two_pow (k + 1))]
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- The geometric sum `∑_{k<n} 2^{k+1} = 2^{n+1} - 2`. -/
lemma sum_two_pow_succ (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℝ) ^ (k + 1)) = (2 : ℝ) ^ (n + 1) - 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ']
      ring

/-- Assembling the three summand groups. -/
lemma casdiv_group (C a1 b1 d1 a2 b2 d2 s : ℝ) :
    C * (a1 + b1 / s + d1) + C * (a2 + b2 / s + d2)
      = C * ((a1 + a2) + (b1 + b2) / s + (d1 + d2)) := by
  ring

/-- The final arithmetic step: for `C₁, C₂, C₃ > 0` and `I, X ≥ 0`,
`1 + C₁(4C₂I + (2C₃+1)X + 2) ≤ (4C₁C₂ + C₁(2C₃+1) + 2C₁ + 2)(I + X + 1)`. -/
lemma casdiv_arith (C₁ C₂ C₃ I X : ℝ) (h₁ : 0 < C₁) (h₂ : 0 < C₂) (h₃ : 0 < C₃)
    (hI : 0 ≤ I) (hX : 0 ≤ X) :
    1 + C₁ * (4 * C₂ * I + (2 * C₃ + 1) * X + 2)
      ≤ (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * (I + X + 1) := by
  have hna : 0 ≤ C₁ * (2 * C₃ + 1) := by nlinarith [h₁.le, h₃.le]
  have hnb : 0 ≤ 4 * C₁ * C₂ := by nlinarith [h₁.le, h₂.le]
  have hnc : 0 ≤ 2 * C₁ := by nlinarith [h₁.le]
  have h4a : 4 * C₁ * C₂ ≤ 4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2 := by linarith
  have h4b : C₁ * (2 * C₃ + 1) ≤ 4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2 := by linarith
  have h4c : 2 * C₁ ≤ 4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2 := by linarith
  have h4d : 1 ≤ 4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2 := by linarith
  have hMM : C₁ * (4 * C₂ * I + (2 * C₃ + 1) * X + 2)
      = 4 * C₁ * C₂ * I + C₁ * (2 * C₃ + 1) * X + 2 * C₁ := by ring
  have hNN : (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * (I + X + 1)
      = (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * I
        + (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * X
        + (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) := by ring
  rw [hMM, hNN]
  have h1 : 4 * C₁ * C₂ * I ≤ (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * I :=
    mul_le_mul_of_nonneg_right h4a hI
  have h2 : C₁ * (2 * C₃ + 1) * X ≤ (4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2) * X :=
    mul_le_mul_of_nonneg_right h4b hX
  linarith [h1, h2, h4c, h4d]

/-- **Dyadic summation of the `W`-terms.**  Let `W : ℝ → ℝ` be measurable, nonnegative on
`(0,1]` and bounded there by `c ≥ 0`, and suppose `W` satisfies the "`α`-step" property
`W b ≤ C₂ W a` whenever `0 < a ≤ b ≤ 2a ≤ 1`.  Then for `L ≥ 1` and `N` with `2^N ≤ L`, the sum
of the values of `W` at the dyadic points `1/2^{k+1}` (`k < N`), together with `W (1/L)`, is
bounded by `4 C₂` times `∫_{1/(2L)}^{1} W α / α dα`.

For `0 < b ≤ 1` the `α`-step gives `W b ≤ 2 C₂ ∫_{b/2}^{b} W α/α dα`: on `[b/2,b]` one has
`W α ≥ W b / C₂` and `1/α ≥ 1/b`.  Applying this to `b = 1/2^{k+1}` (`k < N`) and summing the
adjacent intervals `[1/2^{k+2}, 1/2^{k+1}]` gives `∫_{1/2^{N+1}}^{1/2}`, which lies inside
`[1/(2L),1]` because `2^N ≤ L`; the same bound for `b = 1/L` lands in
`[1/(2L),1/L] ⊆ [1/(2L),1]`. -/
lemma wsum_dyadic (W : ℝ → ℝ) (C₂ c L : ℝ) (N : ℕ)
    (hC₂ : 0 < C₂) (hc : 0 ≤ c) (hWmeas : Measurable W)
    (hWnn : ∀ α : ℝ, 0 < α → α ≤ 1 → 0 ≤ W α)
    (hWbd : ∀ α : ℝ, 0 < α → α ≤ 1 → W α ≤ c)
    (hstep : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 → W b ≤ C₂ * W a)
    (hL1 : 1 ≤ L) (hN : (2 : ℝ) ^ N ≤ L) :
    (∑ k ∈ Finset.range N, W (1 / (2 : ℝ) ^ (k + 1))) + W (1 / L) ≤
      4 * C₂ * (∫ α in (1 / (2 * L))..1, W α / α) := by
  -- the single-scale bound: `W b ≤ 2 C₂ ∫_{b/2}^{b} W α/α dα` for `0 < b ≤ 1`
  have hterm : ∀ b : ℝ, 0 < b → b ≤ 1 → W b ≤ 2 * C₂ * (∫ α in b / 2..b, W α / α) := by
    intro b hb0 hb1
    have hb2pos : 0 < b / 2 := by linarith
    have hle : b / 2 ≤ b := by linarith
    have hInt : IntervalIntegrable (fun α : ℝ => W α / α) volume (b / 2) b :=
      intervalIntegrable_W_div hWmeas hc hWbd hWnn hb2pos hle hb1
    have hIntc : IntervalIntegrable (fun _ : ℝ => W b / (C₂ * b)) volume (b / 2) b :=
      intervalIntegrable_const
    have hpt : ∀ α ∈ Set.Icc (b / 2) b, W b / (C₂ * b) ≤ W α / α := by
      intro α hα
      have hα0 : 0 < α := lt_of_lt_of_le hb2pos hα.1
      have hb2α : b ≤ 2 * α := by linarith [hα.1]
      have hs := hstep α b hα0 hα.2 hb2α hb1
      have hWα : 0 ≤ W α :=
        le_trans (div_nonneg (hWnn b hb0 hb1) hC₂.le)
          ((div_le_iff₀ hC₂).mpr (by rw [mul_comm]; exact hs))
      have hden : 0 < C₂ * b := by positivity
      rw [div_le_div_iff₀ hden hα0]
      calc W b * α ≤ (C₂ * W α) * α := mul_le_mul_of_nonneg_right hs hα0.le
        _ ≤ (C₂ * W α) * b := mul_le_mul_of_nonneg_left hα.2 (mul_nonneg hC₂.le hWα)
        _ = W α * (C₂ * b) := by ring
    have hmono := intervalIntegral.integral_mono_on hle hIntc hInt hpt
    have hval : (∫ α in b / 2..b, W b / (C₂ * b)) = W b / (2 * C₂) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hbne : b ≠ 0 := ne_of_gt hb0
      have hC2ne : C₂ ≠ 0 := ne_of_gt hC₂
      field_simp
      ring
    rw [hval] at hmono
    calc W b = 2 * C₂ * (W b / (2 * C₂)) := by
            rw [← mul_div_assoc, mul_div_cancel_left₀]
            exact ne_of_gt (by positivity : (0 : ℝ) < 2 * C₂)
      _ ≤ 2 * C₂ * (∫ α in b / 2..b, W α / α) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
  -- the pointwise dyadic bounds
  have hWk : ∀ k ∈ Finset.range N,
      W ((1 / 2 : ℝ) ^ (k + 1)) ≤
        2 * C₂ * (∫ α in (1 / 2 : ℝ) ^ (k + 2)..(1 / 2 : ℝ) ^ (k + 1), W α / α) := by
    intro k _
    have hbk : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpos : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have h := hterm ((1 / 2 : ℝ) ^ (k + 1)) hpos hbk
    have hdiv : (1 / 2 : ℝ) ^ (k + 1) / 2 = (1 / 2 : ℝ) ^ (k + 2) := by
      rw [div_eq_mul_inv, inv_eq_one_div, pow_succ']
      ring
    rwa [hdiv] at h
  -- telescoping of the dyadic integrals
  have htel : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, ∫ α in (1 / 2 : ℝ) ^ (k + 2)..(1 / 2 : ℝ) ^ (k + 1), W α / α)
        = ∫ α in (1 / 2 : ℝ) ^ (n + 1)..(1 / 2 : ℝ) ^ 1, W α / α := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, add_comm]
        refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
        · exact intervalIntegrable_W_div hWmeas hc hWbd hWnn (by positivity)
            (half_pow_le (by omega)) (pow_le_one₀ (by norm_num) (by norm_num))
        · exact intervalIntegrable_W_div hWmeas hc hWbd hWnn (by positivity)
            (half_pow_le (by omega)) (by norm_num)
  -- the sum of the `W`-terms
  have hsumW : (∑ k ∈ Finset.range N, W ((1 / 2 : ℝ) ^ (k + 1))) ≤
      2 * C₂ * (∫ α in (1 / 2 : ℝ) ^ (N + 1)..(1 / 2 : ℝ) ^ 1, W α / α) := by
    calc ∑ k ∈ Finset.range N, W ((1 / 2 : ℝ) ^ (k + 1))
        ≤ ∑ k ∈ Finset.range N,
            2 * C₂ * (∫ α in (1 / 2 : ℝ) ^ (k + 2)..(1 / 2 : ℝ) ^ (k + 1), W α / α) :=
          Finset.sum_le_sum hWk
      _ = 2 * C₂ * (∑ k ∈ Finset.range N,
            ∫ α in (1 / 2 : ℝ) ^ (k + 2)..(1 / 2 : ℝ) ^ (k + 1), W α / α) :=
          (Finset.mul_sum _ _ _).symm
      _ = 2 * C₂ * (∫ α in (1 / 2 : ℝ) ^ (N + 1)..(1 / 2 : ℝ) ^ 1, W α / α) := by
          rw [htel N]
  -- the term `W (1/L)`
  have hW1L : W (1 / L) ≤ 2 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α) := by
    have hpos : 0 < 1 / L := by positivity
    have hle1 : 1 / L ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < L)).mpr hL1
    have h := hterm (1 / L) hpos hle1
    have hdiv : (1 / L) / 2 = 1 / (2 * L) := by
      rw [div_div]
      ring
    rw [hdiv] at h
    have hInt : IntervalIntegrable (fun α : ℝ => W α / α) volume (1 / (2 * L)) 1 :=
      intervalIntegrable_W_div hWmeas hc hWbd hWnn (by positivity)
        (by rw [div_le_one (by positivity : (0 : ℝ) < 2 * L)]; linarith) le_rfl
    have hmono : (∫ α in 1 / (2 * L)..1 / L, W α / α) ≤
        (∫ α in 1 / (2 * L)..1, W α / α) := by
      refine intervalIntegral.integral_mono_interval le_rfl ?_ hle1 ?_ hInt
      · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L) (by linarith : (0 : ℝ) < L)]
        linarith
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t :=
          lt_trans (show (0 : ℝ) < 1 / (2 * L) by positivity) ht.1
        exact div_nonneg (hWnn t ht0 (le_trans ht.2 le_rfl)) ht0.le
    calc W (1 / L) ≤ 2 * C₂ * (∫ α in 1 / (2 * L)..1 / L, W α / α) := h
      _ ≤ 2 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  -- containment in `[1/(2L), 1]`
  have hsub1 : (∫ α in (1 / 2 : ℝ) ^ (N + 1)..(1 / 2 : ℝ) ^ 1, W α / α) ≤
      (∫ α in 1 / (2 * L)..1, W α / α) := by
    have hInt : IntervalIntegrable (fun α : ℝ => W α / α) volume (1 / (2 * L)) 1 :=
      intervalIntegrable_W_div hWmeas hc hWbd hWnn (by positivity)
        (by rw [div_le_one (by positivity : (0 : ℝ) < 2 * L)]; linarith) le_rfl
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_ hInt
    · rw [← one_div_two_pow (N + 1)]
      refine one_div_le_one_div_of_le (by positivity) ?_
      rw [pow_succ']
      linarith [hN]
    · exact half_pow_le (by omega)
    · exact pow_le_one₀ (by norm_num) (by norm_num)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t :=
        lt_trans (show (0 : ℝ) < 1 / (2 * L) by positivity) ht.1
      exact div_nonneg (hWnn t ht0 (le_trans ht.2 le_rfl)) ht0.le
  -- combine the two pieces
  have hSW : (∑ k ∈ Finset.range N, W (1 / (2 : ℝ) ^ (k + 1))) ≤
      2 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α) := by
    have h1 : (∑ k ∈ Finset.range N, W (1 / (2 : ℝ) ^ (k + 1))) =
        ∑ k ∈ Finset.range N, W ((1 / 2 : ℝ) ^ (k + 1)) :=
      Finset.sum_congr rfl (fun k _ => by rw [one_div_two_pow])
    rw [h1]
    exact le_trans hsumW (mul_le_mul_of_nonneg_left hsub1 (by positivity))
  have hdouble : 2 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α)
      + 2 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α)
      = 4 * C₂ * (∫ α in 1 / (2 * L)..1, W α / α) := by ring
  linarith [hSW, hW1L, hdouble]

/-- **Dyadic summation of the `Z`-terms (Mertens).**  Let `Z : ℝ → ℝ` satisfy the Mertens-type
bound `Z y ≤ C₃ Z x (log y / log x)` for `2 ≤ y ≤ x`, with `C₃ ≥ 0`, `Z x ≥ 0`, and let
`L = log x > 0` and `2^N ≤ L`.  Then the sum of `Z` at the dyadic scales `exp ((2:ℝ)^(k+1))`
(`k < N`), together with `Z x`, is at most `(2 C₃ + 1) Z x`. -/
lemma zsum_dyadic (Z : ℝ → ℝ) (C₃ x L : ℝ) (N : ℕ)
    (hC₃ : 0 ≤ C₃) (hL : Real.log x = L) (hLpos : 0 < L) (hx0 : 0 < x)
    (hN : (2 : ℝ) ^ N ≤ L) (hZx : 0 ≤ Z x)
    (hmer : ∀ y : ℝ, 2 ≤ y → y ≤ x → Z y ≤ C₃ * Z x * (Real.log y / Real.log x)) :
    (∑ k ∈ Finset.range N, Z (Real.exp ((2 : ℝ) ^ (k + 1)))) + Z x ≤
      (2 * C₃ + 1) * Z x := by
  have hexpx : Real.exp L = x := by rw [← hL]; exact Real.exp_log hx0
  have hterm : ∀ k ∈ Finset.range N,
      Z (Real.exp ((2 : ℝ) ^ (k + 1))) ≤ (C₃ * Z x / L) * (2 : ℝ) ^ (k + 1) := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hge : 2 ≤ Real.exp ((2 : ℝ) ^ (k + 1)) := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
          _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_of_lt (calc (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
        _ ≤ Real.exp ((2 : ℝ) ^ (k + 1)) := Real.exp_le_exp.mpr h2)
    have hlex : Real.exp ((2 : ℝ) ^ (k + 1)) ≤ x := by
      rw [← hexpx]
      apply Real.exp_le_exp.mpr
      have h2 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [hN]
    have h := hmer _ hge hlex
    rw [Real.log_exp, hL] at h
    calc Z (Real.exp ((2 : ℝ) ^ (k + 1))) ≤ C₃ * Z x * ((2 : ℝ) ^ (k + 1) / L) := h
      _ = (C₃ * Z x / L) * (2 : ℝ) ^ (k + 1) := by ring
  have hgeo : (∑ k ∈ Finset.range N, (2 : ℝ) ^ (k + 1)) ≤ 2 * L := by
    rw [sum_two_pow_succ N, pow_succ']
    linarith [hN]
  have hCZ : 0 ≤ C₃ * Z x / L := div_nonneg (mul_nonneg hC₃ hZx) hLpos.le
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have h2 : (C₃ * Z x / L) * (∑ k ∈ Finset.range N, (2 : ℝ) ^ (k + 1))
      ≤ (C₃ * Z x / L) * (2 * L) := mul_le_mul_of_nonneg_left hgeo hCZ
  have h3 : (C₃ * Z x / L) * (2 * L) = 2 * C₃ * Z x := by field_simp
  have h4 : 2 * C₃ * Z x + Z x = (2 * C₃ + 1) * Z x := by ring
  linarith [hsum, h2, h3, h4]

/-- **Dyadic summation of the per-scale bound** (Ramaré's `casdiv`, step 8), with the constant `C₄`
uniform in the data and the extra measurability/boundedness hypotheses that make the claim true.

This is the corrected form of `Work.BMF.mrlas.casdiv_dyadic_sum`: as stated there (with no
measurability hypothesis on `W` or `M`) the claim is *false*, because Lean's Bochner integral of a
function that is not a.e. strongly measurable is `0`, so a `W` built from the indicator of a
non-measurable set satisfies all the per-scale hypotheses while making the integral on the
right-hand side vanish (see `casdiv_dyadic_sum_refutation` in
`Submission/Work/BMF/mrlas/casdiv_dyadic_sum.lean`).  The intended instances are measurable and
bounded (`W = exp (Wsup …) ≤ exp (Zrcp x)`, `M = ‖Mf …‖ ≤ t`), so adding `Measurable M`,
`Measurable W` and a bound `W ≤ c` on `(0,1]` restores the statement while keeping it applicable.

Let `C₁, C₂, C₃ > 0`, `M, W, Z : ℝ → ℝ`, `3 ≤ x`, `2 ≤ T`, and suppose
* (per-scale bound) for every scale `z ∈ [e, x]`, `∫_{√z}^{z} M t/t² dt ≤ C₁ (W(1/log z) + Z z/√T + 1/log z)`;
* (α-step) `W b ≤ C₂ W a` whenever `0 < a ≤ b ≤ 2a ≤ 1`;
* (Mertens) `Z y ≤ C₃ Z x (log y/log x)` for `2 ≤ y ≤ x`;
* `Measurable M`, `Measurable W`, `M ≥ 0`, `M t ≤ t` for `t ≥ 0`, `W ≥ 0` on `(0,1]`, `W` bounded
  on `(0,1]` by some `c ≥ 0`, and `Z x ≥ 0`.

Then `∫_1^x M t/t² dt ≤ C₄ (∫_{1/(2 log x)}^1 W α/α dα + Z x/√T + 1)`. -/
theorem casdiv_dyadic_sum_meas
    (C₁ C₂ C₃ : ℝ) (h₁ : 0 < C₁) (h₂ : 0 < C₂) (h₃ : 0 < C₃) :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ (M W Z : ℝ → ℝ) (x T : ℝ), 3 ≤ x → 2 ≤ T →
      Measurable M → Measurable W →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ M t) →
      (∀ t : ℝ, 0 ≤ t → M t ≤ t) →
      (∀ α : ℝ, 0 < α → α ≤ 1 → 0 ≤ W α) →
      (∃ c : ℝ, 0 ≤ c ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → W α ≤ c) →
      0 ≤ Z x →
      (∀ z : ℝ, Real.exp 1 ≤ z → z ≤ x →
        (∫ t in Real.sqrt z..z, M t / t ^ 2) ≤
          C₁ * (W (1 / Real.log z) + Z z / Real.sqrt T + 1 / Real.log z)) →
      (∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 → W b ≤ C₂ * W a) →
      (∀ y : ℝ, 2 ≤ y → y ≤ x → Z y ≤ C₃ * Z x * (Real.log y / Real.log x)) →
      (∫ t in (1 : ℝ)..x, M t / t ^ 2) ≤
        C₄ * ((∫ α in (1 / (2 * Real.log x))..1, W α / α) + Z x / Real.sqrt T + 1) := by
  refine ⟨4 * C₁ * C₂ + C₁ * (2 * C₃ + 1) + 2 * C₁ + 2, by positivity, ?_⟩
  intro M W Z x T hx hT hMmeas hWmeas hMnn hMle hWnn hWbd hZxnn hscale hstep hZmer
  obtain ⟨c, hc, hWbdc⟩ := hWbd
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hL1 : 1 ≤ Real.log x := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    exact le_trans h3 (Real.log_le_log (by norm_num) hx)
  have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLnn : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  set N : ℕ := Nat.floor (Real.log (Real.log x) / Real.log 2) with hNdef
  have hNle : (N : ℝ) ≤ Real.log (Real.log x) / Real.log 2 :=
    Nat.floor_le (div_nonneg hlogLnn hlog2.le)
  have hNlt : Real.log (Real.log x) / Real.log 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2Nle : (2 : ℝ) ^ N ≤ Real.log x := by
    have h : (N : ℝ) * Real.log 2 ≤ Real.log (Real.log x) := (le_div_iff₀ hlog2).mp hNle
    calc (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (Real.log (Real.log x)) := Real.exp_le_exp.mpr h
      _ = Real.log x := Real.exp_log hLpos
  have h2Nhalf : Real.log x / 2 ≤ (2 : ℝ) ^ N := by
    have h1 : Real.log (Real.log x) < ((N : ℝ) + 1) * Real.log 2 :=
      (div_lt_iff₀ hlog2).mp hNlt
    have hcast : ((N : ℝ) + 1) * Real.log 2 = ((N + 1 : ℕ) : ℝ) * Real.log 2 := by
      push_cast; ring
    rw [hcast] at h1
    have hlt : Real.log x < (2 : ℝ) ^ (N + 1) :=
      calc Real.log x = Real.exp (Real.log (Real.log x)) := (Real.exp_log hLpos).symm
        _ < Real.exp (((N + 1 : ℕ) : ℝ) * Real.log 2) := Real.exp_lt_exp.mpr h1
        _ = (2 : ℝ) ^ (N + 1) := by
              rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have h2 : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := pow_succ' 2 N
    linarith
  -- integrability of the integrand
  have hint : ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun t : ℝ => M t / t ^ 2) volume a b :=
    fun a b ha hb => intervalIntegrable_M_div_sq hMmeas hMnn hMle ha hb
  -- the dyadic decomposition of the integral
  have hsum : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
          ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
        = ∫ t in Real.exp 1..Real.exp ((2 : ℝ) ^ n), M t / t ^ 2 := by
    intro n
    induction n with
    | zero => simp [pow_zero]
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        exact intervalIntegral.integral_add_adjacent_intervals
          (hint (Real.exp 1) (Real.exp ((2 : ℝ) ^ m)) (Real.exp_pos 1) (Real.exp_pos _))
          (hint (Real.exp ((2 : ℝ) ^ m)) (Real.exp ((2 : ℝ) ^ (m + 1))) (Real.exp_pos _)
            (Real.exp_pos _))
  have hsplit : (∫ t in (1 : ℝ)..x, M t / t ^ 2)
      = (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2)
        + (∑ k ∈ Finset.range N,
            ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
        + (∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2) := by
    have houter : (∫ t in (1 : ℝ)..Real.exp ((2 : ℝ) ^ N), M t / t ^ 2)
        + ∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2
        = ∫ t in (1 : ℝ)..x, M t / t ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        (hint 1 (Real.exp ((2 : ℝ) ^ N)) one_pos (Real.exp_pos _))
        (hint (Real.exp ((2 : ℝ) ^ N)) x (Real.exp_pos _) hx0)
    have hinner : (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2)
        + ∫ t in Real.exp 1..Real.exp ((2 : ℝ) ^ N), M t / t ^ 2
        = ∫ t in (1 : ℝ)..Real.exp ((2 : ℝ) ^ N), M t / t ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        (hint 1 (Real.exp 1) one_pos (Real.exp_pos 1))
        (hint (Real.exp 1) (Real.exp ((2 : ℝ) ^ N)) (Real.exp_pos 1) (Real.exp_pos _))
    rw [← houter, ← hinner, ← hsum N]
  -- the first piece `∫_1^e ≤ 1`
  have hfirst : (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2) ≤ 1 := by
    have hI1 : IntervalIntegrable (fun t : ℝ => M t / t ^ 2) volume 1 (Real.exp 1) :=
      hint 1 (Real.exp 1) one_pos (Real.exp_pos 1)
    have hI2 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 (Real.exp 1) := by
      refine intervalIntegral.intervalIntegrable_inv (f := fun t : ℝ => t) (a := 1)
        (b := Real.exp 1) ?_ continuousOn_id
      intro t ht
      rw [Set.uIcc_of_le (by linarith [Real.exp_one_gt_two] : (1 : ℝ) ≤ Real.exp 1)] at ht
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    have hmono : (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2)
        ≤ ∫ t in (1 : ℝ)..Real.exp 1, t⁻¹ := by
      refine intervalIntegral.integral_mono_on
        (by linarith [Real.exp_one_gt_two] : (1 : ℝ) ≤ Real.exp 1) hI1 hI2 ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      have h2 : (0 : ℝ) < t ^ 2 := by positivity
      calc M t / t ^ 2 ≤ t / t ^ 2 := div_le_div_of_nonneg_right (hMle t ht0.le) h2.le
        _ = t⁻¹ := by rw [div_eq_mul_inv]; field_simp
    have hval : (∫ t in (1 : ℝ)..Real.exp 1, t⁻¹) = 1 := by
      rw [integral_inv_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp]
    linarith
  -- the dyadic blocks
  have hblock : ∀ k ∈ Finset.range N,
      (∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2) ≤
        C₁ * (W (1 / (2 : ℝ) ^ (k + 1)) + Z (Real.exp ((2 : ℝ) ^ (k + 1))) / Real.sqrt T
          + 1 / (2 : ℝ) ^ (k + 1)) := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hz1 : Real.exp 1 ≤ Real.exp ((2 : ℝ) ^ (k + 1)) := by
      apply Real.exp_le_exp.mpr
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      linarith
    have hz2 : Real.exp ((2 : ℝ) ^ (k + 1)) ≤ x := by
      rw [← Real.exp_log hx0]
      apply Real.exp_le_exp.mpr
      have h2 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [h2Nle]
    have h := hscale (Real.exp ((2 : ℝ) ^ (k + 1))) hz1 hz2
    rw [sqrt_exp_two_pow k, Real.log_exp] at h
    exact h
  -- the last block
  have hlast : (∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2) ≤
      C₁ * (W (1 / Real.log x) + Z x / Real.sqrt T + 1 / Real.log x) := by
    have hxe : Real.exp 1 ≤ x := by
      rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hL1
    have h := hscale x hxe le_rfl
    have hle : (∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2)
        ≤ (∫ t in Real.sqrt x..x, M t / t ^ 2) := by
      refine intervalIntegral.integral_mono_interval ?_ ?_ le_rfl ?_ ?_
      · have hsx : Real.sqrt x = Real.exp (Real.log x / 2) := by
          rw [← Real.exp_log (Real.sqrt_pos.mpr hx0), Real.log_sqrt hx0.le]
        rw [hsx]
        exact Real.exp_le_exp.mpr h2Nhalf
      · rw [← Real.exp_log hx0]
        exact Real.exp_le_exp.mpr h2Nle
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (hMnn t (le_trans (Real.sqrt_nonneg x) ht.1.le)) (by positivity)
      · exact hint (Real.sqrt x) x (Real.sqrt_pos.mpr hx0) hx0
    exact le_trans hle h
  -- the three sums
  set SW : ℝ := ∑ k ∈ Finset.range N, W (1 / (2 : ℝ) ^ (k + 1)) with hSWdef
  set SZ : ℝ := ∑ k ∈ Finset.range N, Z (Real.exp ((2 : ℝ) ^ (k + 1))) with hSZdef
  set S1 : ℝ := ∑ k ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ (k + 1) with hS1def
  have hsumblocks : (∑ k ∈ Finset.range N,
        ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
      ≤ C₁ * (SW + SZ / Real.sqrt T + S1) := by
    rw [hSWdef, hSZdef, hS1def]
    calc (∑ k ∈ Finset.range N,
          ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
        ≤ ∑ k ∈ Finset.range N, C₁ * (W (1 / (2 : ℝ) ^ (k + 1))
            + Z (Real.exp ((2 : ℝ) ^ (k + 1))) / Real.sqrt T + 1 / (2 : ℝ) ^ (k + 1)) :=
          Finset.sum_le_sum hblock
      _ = C₁ * (∑ k ∈ Finset.range N, (W (1 / (2 : ℝ) ^ (k + 1))
            + Z (Real.exp ((2 : ℝ) ^ (k + 1))) / Real.sqrt T + 1 / (2 : ℝ) ^ (k + 1))) :=
          (Finset.mul_sum _ _ _).symm
      _ = C₁ * ((∑ k ∈ Finset.range N, W (1 / (2 : ℝ) ^ (k + 1)))
            + (∑ k ∈ Finset.range N, Z (Real.exp ((2 : ℝ) ^ (k + 1)))) / Real.sqrt T
            + (∑ k ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ (k + 1))) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
  have hS1b : S1 + 1 / Real.log x ≤ 2 := by
    rw [hS1def, sum_one_div_two_pow N]
    have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
    have h3 : (1 : ℝ) / Real.log x ≤ 1 := (div_le_one hLpos).mpr hL1
    linarith
  have hWsb : SW + W (1 / Real.log x)
      ≤ 4 * C₂ * (∫ α in (1 / (2 * Real.log x))..1, W α / α) := by
    rw [hSWdef]
    exact wsum_dyadic W C₂ c (Real.log x) N h₂ hc hWmeas hWnn hWbdc hstep hL1 h2Nle
  have hZsb : SZ + Z x ≤ (2 * C₃ + 1) * Z x := by
    rw [hSZdef]
    exact zsum_dyadic Z C₃ x (Real.log x) N h₃.le rfl hLpos hx0 h2Nle hZxnn hZmer
  have hZdiv : (SZ + Z x) / Real.sqrt T ≤ (2 * C₃ + 1) * (Z x / Real.sqrt T) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hZsb hsqrtT
  have hI_nn : 0 ≤ ∫ α in (1 / (2 * Real.log x))..1, W α / α := by
    refine intervalIntegral.integral_nonneg ?_ ?_
    · rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.log x)]
      linarith
    · intro t ht
      have ht0 : 0 < t :=
        lt_of_lt_of_le (show (0 : ℝ) < 1 / (2 * Real.log x) by positivity) ht.1
      exact div_nonneg (hWnn t ht0 ht.2) ht0.le
  have hX_nn : 0 ≤ Z x / Real.sqrt T := div_nonneg hZxnn hsqrtT
  -- the main chain of inequalities
  have hgrp := casdiv_group C₁ SW SZ S1 (W (1 / Real.log x)) (Z x) (1 / Real.log x)
    (Real.sqrt T)
  have hbrk : (SW + W (1 / Real.log x)) + (SZ + Z x) / Real.sqrt T + (S1 + 1 / Real.log x)
      ≤ 4 * C₂ * (∫ α in (1 / (2 * Real.log x))..1, W α / α)
        + (2 * C₃ + 1) * (Z x / Real.sqrt T) + 2 := by
    linarith [hWsb, hZdiv, hS1b]
  have hBC : (∑ k ∈ Finset.range N,
          ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
        + C₁ * (W (1 / Real.log x) + Z x / Real.sqrt T + 1 / Real.log x)
      ≤ C₁ * (4 * C₂ * (∫ α in (1 / (2 * Real.log x))..1, W α / α)
          + (2 * C₃ + 1) * (Z x / Real.sqrt T) + 2) := by
    refine le_trans (add_le_add hsumblocks le_rfl) ?_
    rw [hgrp]
    exact mul_le_mul_of_nonneg_left hbrk h₁.le
  have hAC : (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2)
        + (∑ k ∈ Finset.range N,
            ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
        + (∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2)
      ≤ 1 + C₁ * (4 * C₂ * (∫ α in (1 / (2 * Real.log x))..1, W α / α)
          + (2 * C₃ + 1) * (Z x / Real.sqrt T) + 2) := by
    have e1 : (∫ t in (1 : ℝ)..Real.exp 1, M t / t ^ 2)
          + (∑ k ∈ Finset.range N,
              ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
          + (∫ t in Real.exp ((2 : ℝ) ^ N)..x, M t / t ^ 2)
        ≤ 1 + ((∑ k ∈ Finset.range N,
              ∫ t in Real.exp ((2 : ℝ) ^ k)..Real.exp ((2 : ℝ) ^ (k + 1)), M t / t ^ 2)
            + C₁ * (W (1 / Real.log x) + Z x / Real.sqrt T + 1 / Real.log x)) := by
      linarith [hfirst, hlast]
    linarith [e1, hBC]
  rw [hsplit]
  refine le_trans hAC ?_
  exact casdiv_arith C₁ C₂ C₃ (∫ α in (1 / (2 * Real.log x))..1, W α / α)
    (Z x / Real.sqrt T) h₁ h₂ h₃ hI_nn hX_nn

end Work.BMF.mrlas
