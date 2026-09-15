import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.NumberTheory.Sieve

/-- For `c > 0` and `L > 0`, the function `x ↦ exp (-(c * sqrt (log x / L)))` tends to
`0` as `x → +∞`. -/
lemma tendsto_exp_neg_sqrt_log_div_atTop (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-(c * Real.sqrt (Real.log x / L))))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / L) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hL Real.tendsto_log_atTop
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x / L))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hmul : Filter.Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x / L))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc hsqrt
  have hneg : Filter.Tendsto (fun x : ℝ => -(c * Real.sqrt (Real.log x / L)))
      Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hmul
  exact Real.tendsto_exp_atBot.comp hneg

/-- For `K > 0`, the inequality `K * log x ≤ sqrt x` holds for all sufficiently large `x`. -/
lemma eventually_const_mul_log_le_sqrt (K : ℝ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in Filter.atTop, K * Real.log x ≤ Real.sqrt x := by
  have hlittle : (fun x : ℝ => Real.log x) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1/2 : ℝ)) := isLittleO_log_rpow_atTop (by norm_num)
  have hev := hlittle.def (c := 1/K) (by positivity : (0:ℝ) < 1/K)
  filter_upwards [hev, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hhalf_nn : 0 ≤ x^(1/2:ℝ) := Real.rpow_nonneg hx0 _
  have hbound : Real.log x ≤ (1/K) * x^(1/2:ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlognn, abs_of_nonneg hhalf_nn] using hx
  calc K * Real.log x ≤ K * ((1/K) * x^(1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hK)
    _ = x^(1/2:ℝ) := by field_simp
    _ = Real.sqrt x := by rw [Real.sqrt_eq_rpow]

theorem window_AP_error_eventually (ε c C : ℝ) (hε : 0 < ε) (hc : 0 < c) (hC : 0 < C) :
    ∀ W : ℕ, 1 ≤ W → ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      2 * C * ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ) *
          Real.exp (-(c * Real.sqrt
            (Real.log ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ) / Real.log ((W : ℝ) + 2))))
        + 2 * Real.sqrt ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ) *
            Real.log ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ)
      ≤ ε * (p : ℝ) / 8 := by
  intro W hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    have : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    linarith
  have hLpos : 0 < Real.log ((W : ℝ) + 2) := Real.log_pos (by linarith)
  -- target small exponential factor δ1
  set δ1 : ℝ := 1 / (96 * C * (W : ℝ)) with hδ1def
  have hδ1pos : 0 < δ1 := by
    rw [hδ1def]
    exact one_div_pos.mpr (by positivity)
  -- eventually the exponential term is below δ1
  have hev1 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((W : ℝ) + 2)))) < δ1 :=
    (tendsto_order.1 (tendsto_exp_neg_sqrt_log_div_atTop c _ hc hLpos)).2 δ1 hδ1pos
  rw [Filter.eventually_atTop] at hev1
  obtain ⟨M1, hM1⟩ := hev1
  -- eventually 96 W log x ≤ sqrt x
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, 96 * (W : ℝ) * Real.log x ≤ Real.sqrt x :=
    eventually_const_mul_log_le_sqrt (96 * (W : ℝ)) (by positivity)
  rw [Filter.eventually_atTop] at hev2
  obtain ⟨M2, hM2⟩ := hev2
  let M : ℝ := max M1 M2
  let K0 : ℝ := max 1 ((M + (W : ℝ) - 1) / 2)
  -- choose the threshold P
  have htend : Filter.Tendsto (fun p : ℕ => ((W : ℝ) * ε) * (p : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < (W:ℝ) * ε)
      tendsto_natCast_atTop_atTop
  have hevP : ∀ᶠ p : ℕ in Filter.atTop, K0 ≤ ((W : ℝ) * ε) * (p : ℝ) :=
    (Filter.tendsto_atTop.1 htend) K0
  rw [Filter.eventually_atTop] at hevP
  obtain ⟨P, hP⟩ := hevP
  refine ⟨P, fun p hp => ?_⟩
  have hK0le : K0 ≤ ((W : ℝ) * ε) * (p : ℝ) := hP p hp
  -- the key quantity X = W ⌊2 ε p⌋ + 1
  let X : ℝ := ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ)
  change 2 * C * X * Real.exp (-(c * Real.sqrt
            (Real.log X / Real.log ((W : ℝ) + 2))))
        + 2 * Real.sqrt X * Real.log X ≤ ε * (p : ℝ) / 8
  have hfloor_le : (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) ≤ 2 * ε * (p : ℝ) :=
    Nat.floor_le (by positivity)
  have hfloor_gt : 2 * ε * (p : ℝ) < (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hXeq : X = (W : ℝ) * (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) + 1 := by
    change ((W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 : ℕ) : ℝ) = (W : ℝ) * (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) + 1
    push_cast
    ring
  have hXub : X ≤ 2 * (W : ℝ) * ε * (p : ℝ) + 1 := by
    rw [hXeq]; nlinarith [hfloor_le, hWpos]
  have hXlb : 2 * (W : ℝ) * ε * (p : ℝ) - (W : ℝ) + 1 ≤ X := by
    rw [hXeq]; nlinarith [hfloor_gt, hWpos]
  have hXge1 : (1 : ℝ) ≤ X := by
    rw [hXeq]
    have hcast : (0 : ℝ) ≤ (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
    nlinarith [hcast, hWpos]
  have hWεp_ge : 1 ≤ (W : ℝ) * ε * (p : ℝ) :=
    le_trans (le_max_left 1 _) hK0le
  have hXle3 : X ≤ 3 * (W : ℝ) * ε * (p : ℝ) := by nlinarith [hXub, hWεp_ge]
  have hXM : M ≤ X := by
    have hK0ge : (M + (W : ℝ) - 1) / 2 ≤ K0 := le_max_right 1 _
    have : M ≤ 2 * (W : ℝ) * ε * (p : ℝ) - (W : ℝ) + 1 := by
      nlinarith [hK0le, hK0ge]
    linarith [hXlb, this]
  have hM1X : M1 ≤ X := le_trans (le_max_left M1 M2) hXM
  have hM2X : M2 ≤ X := le_trans (le_max_right M1 M2) hXM
  have hexp : Real.exp (-(c * Real.sqrt (Real.log X / Real.log ((W : ℝ) + 2)))) ≤ δ1 :=
    le_of_lt (hM1 X hM1X)
  have hXnn : 0 ≤ X := by linarith [hXge1]
  -- first term
  have hterm1 : 2 * C * X *
      Real.exp (-(c * Real.sqrt (Real.log X / Real.log ((W : ℝ) + 2)))) ≤ ε * (p : ℝ) / 16 := by
    calc
      2 * C * X * Real.exp (-(c * Real.sqrt (Real.log X / Real.log ((W : ℝ) + 2))))
          ≤ 2 * C * X * δ1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 2 * C * (3 * (W : ℝ) * ε * (p : ℝ)) * δ1 := by
            have h1 : 2 * C * X ≤ 2 * C * (3 * (W : ℝ) * ε * (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hXle3 (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (le_of_lt hδ1pos)
      _ = ε * (p : ℝ) / 16 := by
            rw [hδ1def]; field_simp; ring
  -- second term
  have hterm2 : 2 * Real.sqrt X * Real.log X ≤ ε * (p : ℝ) / 16 := by
    have hlogX : 96 * (W : ℝ) * Real.log X ≤ Real.sqrt X := hM2 X hM2X
    have hsq : Real.sqrt X * Real.sqrt X = X := by nlinarith [Real.sq_sqrt hXnn]
    have hstep : 2 * Real.sqrt X * Real.log X * (48 * (W : ℝ)) ≤ X := by
      have h1 : (96 * (W : ℝ) * Real.log X) * (2 * Real.sqrt X)
          ≤ Real.sqrt X * (2 * Real.sqrt X) :=
        mul_le_mul_of_nonneg_right hlogX (by positivity)
      nlinarith [h1, hsq]
    have hWpos48 : (0 : ℝ) < 48 * (W : ℝ) := by positivity
    have hmain : 2 * Real.sqrt X * Real.log X ≤ X / (48 * (W : ℝ)) := by
      rw [le_div_iff₀ hWpos48]; exact hstep
    have hXdiv : X / (48 * (W : ℝ)) ≤ 3 * (W : ℝ) * ε * (p : ℝ) / (48 * (W : ℝ)) :=
      div_le_div_of_nonneg_right hXle3 (by positivity)
    have heq : 3 * (W : ℝ) * ε * (p : ℝ) / (48 * (W : ℝ)) = ε * (p : ℝ) / 16 := by
      field_simp; ring
    linarith [hmain, hXdiv, heq.le]
  linarith [hterm1, hterm2]

end Commons.NumberTheory.Sieve