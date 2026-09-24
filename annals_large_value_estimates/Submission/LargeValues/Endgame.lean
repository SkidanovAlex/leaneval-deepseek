import Submission.LargeValues.Middle
import Submission.LargeValues.Reduction
import Submission.Commons.NumberTheory.DirichletPolynomial.trivial_value_bound
import Submission.Commons.Analysis.Metric.one_separated_points_card_le

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Assembly: Guth–Maynard Theorem 1.1 from Proposition 4.1 (`KeyProp`)

We combine
 * the classical regimes (`pointwise_bound_cases123`: absolute constant),
 * the middle regime (`middle_regime_bound`: bound `≤ C·N^{4ε}·bound` for `N ≥ N₀(ε)`),
into `theorem_1_1`, whose `o` is built by a diagonal choice of `ε(T) = 1/jT` where
`jT` is the least `k` with the threshold `N₀(1/k)` exceeding `T^{1/log log T}`.
-/

namespace Submission.LargeValues

/-- Classical mean-value bound in the middle regime, carrying an extra factor `N^{1/5}`:
when `3N^{7/10} ≤ V ≤ N^{4/5}` one has `R ≤ C·N^{1/5}·bound N V T`. -/
theorem mv_middle_regime :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (N : ℕ) (V T : ℝ) (R : ℕ) (t : Fin R → ℝ),
        N > 0 → V > 0 → 0 ≤ T →
        3 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
        (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖) →
        (R : ℝ) ≤ C * (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := by
  obtain ⟨CA, hCA, hA⟩ := Commons.NumberTheory.DirichletPolynomial.mv_large_values
  refine ⟨2 * CA, by positivity, ?_⟩
  intro b hb N V T R t hN hV hT hVlo hVhi hsep hIcc hD
  have h := hA b hb N V T R t hN hV hT hsep hIcc hD
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hz2 : V ^ (-2 : ℤ) = (V ^ 2)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hz4 : V ^ (-4 : ℤ) = (V ^ 4)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hbnd_eq : bound N V T
      = (N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4
        + T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
    unfold bound
    rw [hz2, hz4]
    ring
  have hN15 : 0 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (le_of_lt hNpos) _
  -- V^2 ≥ 9 N^{7/5}
  have hV2ge : 9 * (N : ℝ) ^ (7 / 5 : ℝ) ≤ V ^ 2 := by
    have hsq : (3 * (N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 ≤ V ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (le_of_lt hV)]
      exact hVlo
    have h3 : (3 * (N : ℝ) ^ (7 / 10 : ℝ)) ^ 2 = 9 * (N : ℝ) ^ (7 / 5 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (7 / 10 : ℝ)) 2,
        ← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    linarith [hsq, h3.le, h3.ge]
  -- V^2 ≤ N^{8/5}
  have hV2le : V ^ 2 ≤ (N : ℝ) ^ (8 / 5 : ℝ) := by
    calc V ^ 2 ≤ ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 2 := pow_le_pow_left₀ (le_of_lt hV) hVhi 2
      _ = (N : ℝ) ^ (8 / 5 : ℝ) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (4 / 5 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hNpos)]
          norm_num
  -- V^4 ≤ N^{16/5}
  have hV4le : V ^ 4 ≤ (N : ℝ) ^ (16 / 5 : ℝ) := by
    calc V ^ 4 ≤ ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 4 := pow_le_pow_left₀ (le_of_lt hV) hVhi 4
      _ = (N : ℝ) ^ (16 / 5 : ℝ) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (4 / 5 : ℝ)) 4, ← Real.rpow_mul (le_of_lt hNpos)]
          norm_num
  have hV4pos : 0 < V ^ 4 := by positivity
  have hV2pos : 0 < V ^ 2 := by positivity
  -- N^{2/5} ≤ bound
  have hF4 : (N : ℝ) ^ (2 / 5 : ℝ) ≤ bound N V T := by
    have hmain : (N : ℝ) ^ (2 / 5 : ℝ) ≤ (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 := by
      have h1 : (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 ≥ (N : ℝ) ^ (18 / 5 : ℝ) / (N : ℝ) ^ (16 / 5 : ℝ) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hNpos) _) (by positivity) hV4le
      have h2 : (N : ℝ) ^ (18 / 5 : ℝ) / (N : ℝ) ^ (16 / 5 : ℝ) = (N : ℝ) ^ (2 / 5 : ℝ) := by
        rw [← Real.rpow_sub hNpos]; norm_num
      linarith [h1, h2.le, h2.ge]
    rw [hbnd_eq]
    have h1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
    have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := by
      have hT0 : 0 ≤ T := hT
      positivity
    linarith [hmain]
  -- first term
  have hF5 : (N : ℝ) ^ 2 / V ^ 2 ≤ (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := by
    have he : (N : ℝ) ^ 2 / (9 * (N : ℝ) ^ (7 / 5 : ℝ)) = (N : ℝ) ^ (3 / 5 : ℝ) / 9 := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by simp]
      rw [show (N : ℝ) ^ (2 : ℝ) / (9 * (N : ℝ) ^ (7 / 5 : ℝ))
          = (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ (7 / 5 : ℝ) / 9 by ring]
      rw [← Real.rpow_sub hNpos]
      norm_num
    have h1 : (N : ℝ) ^ 2 / V ^ 2 ≤ (N : ℝ) ^ (3 / 5 : ℝ) / 9 := by
      have hd : (N : ℝ) ^ 2 / V ^ 2 ≤ (N : ℝ) ^ 2 / (9 * (N : ℝ) ^ (7 / 5 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hV2ge
      linarith [hd, he.le, he.ge]
    have h3 : (N : ℝ) ^ (3 / 5 : ℝ) = (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_add hNpos]; norm_num
    have hb0 : 0 ≤ bound N V T := le_trans (Real.rpow_nonneg (le_of_lt hNpos) _) hF4
    calc (N : ℝ) ^ 2 / V ^ 2 ≤ (N : ℝ) ^ (3 / 5 : ℝ) / 9 := h1
      _ = (N : ℝ) ^ (1 / 5 : ℝ) * ((N : ℝ) ^ (2 / 5 : ℝ) / 9) := by rw [h3]; ring
      _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (bound N V T / 9) := by
          apply mul_le_mul_of_nonneg_left _ hN15
          linarith
      _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := by
          apply mul_le_mul_of_nonneg_left _ hN15
          linarith
  -- second term
  have hF6 : T * (N : ℝ) / V ^ 2 ≤ (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := by
    have hV4eq : V ^ 4 = V ^ 2 * V ^ 2 := by ring
    have hA : (N : ℝ) / V ^ 2 ≤ (N : ℝ) ^ (13 / 5 : ℝ) / V ^ 4 := by
      rw [div_le_iff₀ hV2pos, div_mul_eq_mul_div, le_div_iff₀ hV4pos]
      have h13 : (N : ℝ) ^ (13 / 5 : ℝ) = (N : ℝ) * (N : ℝ) ^ (8 / 5 : ℝ) := by
        rw [show (13 / 5 : ℝ) = 1 + 8 / 5 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
      rw [h13, hV4eq]
      nlinarith [hV2le, mul_nonneg (le_of_lt hNpos) (le_of_lt hV2pos),
        mul_nonneg (le_of_lt hNpos) (mul_nonneg (le_of_lt hV2pos) (le_of_lt hV2pos))]
    have hC : (N : ℝ) ^ (13 / 5 : ℝ) = (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) := by
      rw [← Real.rpow_add hNpos]; norm_num
    have h3 : T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 ≤ bound N V T := by
      rw [hbnd_eq]
      have h1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
      have h4 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 := by positivity
      linarith
    calc T * (N : ℝ) / V ^ 2 = T * ((N : ℝ) / V ^ 2) := by ring
      _ ≤ T * ((N : ℝ) ^ (13 / 5 : ℝ) / V ^ 4) := mul_le_mul_of_nonneg_left hA hT
      _ = (N : ℝ) ^ (1 / 5 : ℝ) * (T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by rw [hC]; ring
      _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := mul_le_mul_of_nonneg_left h3 hN15
  have hsum : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))
      ≤ 2 * ((N : ℝ) ^ (1 / 5 : ℝ) * bound N V T) := by
    rw [hz2]
    have h1 : (N : ℝ) ^ 2 * (V ^ 2)⁻¹ = (N : ℝ) ^ 2 / V ^ 2 := by rw [div_eq_mul_inv]
    have h2 : T * ((N : ℝ) * (V ^ 2)⁻¹) = T * (N : ℝ) / V ^ 2 := by rw [div_eq_mul_inv]; ring
    rw [h1, h2]
    linarith [hF5, hF6]
  calc (R : ℝ) ≤ CA * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))) := h
    _ ≤ CA * (2 * ((N : ℝ) ^ (1 / 5 : ℝ) * bound N V T)) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hCA)
    _ = 2 * CA * ((N : ℝ) ^ (1 / 5 : ℝ) * bound N V T) := by ring
    _ = 2 * CA * (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := by ring


/-- `V ≤ 4x^{7/10}` ⟹ `x·V^{-2} ≤ 16·x^{12/5}·V^{-4}` (the `V ≤ c N^{7/10}` comparison
with `c = 4`). -/
theorem N_mul_V_neg_two_le_four (x V : ℝ) (hx1 : 1 ≤ x) (hV0 : 0 < V)
    (hV : V ≤ 4 * x ^ (7 / 10 : ℝ)) :
    x * V ^ (-2 : ℤ) ≤ 16 * x ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hVsq : V ^ 2 ≤ 16 * x ^ (7 / 5 : ℝ) := by
    have h1 : V ^ 2 ≤ (4 * x ^ (7 / 10 : ℝ)) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (le_of_lt hV0), abs_of_nonneg (by positivity)]
      exact hV
    have h2 : (4 * x ^ (7 / 10 : ℝ)) ^ 2 = 16 * x ^ (7 / 5 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ (7 / 10 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    linarith [h1, h2.symm.le, h2.le]
  have hmain : x * V ^ 2 ≤ 16 * x ^ (12 / 5 : ℝ) := by
    calc x * V ^ 2 ≤ x * (16 * x ^ (7 / 5 : ℝ)) := mul_le_mul_of_nonneg_left hVsq (le_of_lt hx0)
      _ = 16 * (x * x ^ (7 / 5 : ℝ)) := by ring
      _ = 16 * (x ^ (1 : ℝ) * x ^ (7 / 5 : ℝ)) := by rw [Real.rpow_one]
      _ = 16 * x ^ (12 / 5 : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
  rw [zpow_neg, zpow_neg, inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [hmain, sq_nonneg V]

/-- Trivial bound: `R ≤ 4(T+1)·bound N V T` for arbitrary large-value data. -/
theorem card_le_trivial (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (N : ℕ) (V T : ℝ) (R : ℕ)
    (t : Fin R → ℝ) (hN : N > 0) (hV : V > 0) (hT : 0 ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) (hIcc : ∀ i, t i ∈ Set.Icc 0 T)
    (hD : ∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖) :
    (R : ℝ) ≤ 4 * (T + 1) * bound N V T := by
  have hN1 : 1 ≤ N := hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (R : ℝ) ≤ T + 1 :=
    Commons.Analysis.Metric.one_separated_points_card_le T hT R t hIcc (fun i j hij => hsep i j hij)
  have hbnd0 : 0 ≤ bound N V T := by
    unfold bound
    have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
    have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
    have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
    linarith
  by_cases hV2N : V ≤ 2 * (N : ℝ)
  · have hge : (1 / 4 : ℝ) ≤ bound N V T := by
      unfold bound
      have hN2 : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) = (N : ℝ) ^ 2 / V ^ 2 := by
        rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
      rw [hN2]
      have h1 : (1 / 4 : ℝ) ≤ (N : ℝ) ^ 2 / V ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hNpos, hV, hV2N]
      have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
      have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
      linarith
    have h2 : (T + 1) ≤ 4 * (T + 1) * bound N V T := by nlinarith [hT, hge, hbnd0]
    linarith
  · push_neg at hV2N
    have hR0 : R = 0 := by
      by_contra hR
      have hRpos : 0 < R := Nat.pos_of_ne_zero hR
      have h := hD ⟨0, hRpos⟩
      have hbound := Commons.NumberTheory.DirichletPolynomial.trivial_value_bound N hN1 b hb (t ⟨0, hRpos⟩)
      linarith
    rw [hR0]
    push_cast
    positivity

/-- **Main estimate modulo `KeyProp`**: for every `ε > 0`, eventually in `T` all large-value
data satisfy `R ≤ T^ε · bound N V T`. -/
theorem main_bound_of_keyprop (hKey : KeyPropStatement) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (T : ℝ) in Filter.atTop,
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (N : ℕ) (V : ℝ) (R : ℕ) (t : Fin R → ℝ),
        N > 0 → V > 0 → 1 < T →
        (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
        (R : ℝ) ≤ T ^ ε * bound N V T := by
  intro ε hε
  obtain ⟨C1, hC1, h123⟩ := pointwise_bound_cases123
  obtain ⟨C2, hC2, hmid⟩ := middle_regime_bound hKey
  obtain ⟨C3, hC3, hC3b⟩ := mv_middle_regime
  obtain ⟨Cmv, hCmv, hMV⟩ := Commons.NumberTheory.DirichletPolynomial.mv_large_values
  set ε' : ℝ := ε / 16 with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; linarith
  set η : ℝ := ε / 3 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηε : η ≤ ε := by rw [hηdef]; linarith
  obtain ⟨N₀, hN₀⟩ := hmid ε' hε'
  have hK2pos : 0 < 2 * C3 * ((N₀ : ℝ) + 1) ^ (1 / 5 : ℝ) := by positivity
  have hP1pos : 0 < max C1 1 := lt_max_of_lt_right zero_lt_one
  filter_upwards [tendsto_rpow_atTop hη |>.eventually_ge_atTop C1,
    tendsto_rpow_atTop hη |>.eventually_ge_atTop C2,
    tendsto_rpow_atTop hη |>.eventually_ge_atTop (2 * C3 * ((N₀ : ℝ) + 1) ^ (1 / 5 : ℝ)),
    tendsto_rpow_atTop hη |>.eventually_ge_atTop (Cmv * 17),
    tendsto_rpow_atTop hη |>.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (1 : ℝ)] with T hC1T hC2T hK2T hKmvT h1T hT1
  intro b hb N V R t hN hV hT1' hsep hIcc hD
  have hbnd0 : 0 ≤ bound N V T := by
    unfold bound
    have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
    have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
    have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
    linarith
  have h1ε : 1 ≤ T := hT1
  have hε3 : T ^ η ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le h1ε hηε
  have hmono1 : C1 ≤ T ^ η := hC1T
  by_cases hcase : T ≤ (N : ℝ) ∨ V ≤ 4 * (N : ℝ) ^ (7 / 10 : ℝ) ∨ (N : ℝ) ^ (4 / 5 : ℝ) ≤ V
  · have hfin : (R : ℝ) ≤ T ^ ε * bound N V T := by
      rcases hcase with h1 | h1 | h1
      · have h := h123 b hb N V T R t hN hV hT1' hsep hIcc hD (Or.inl h1)
        calc (R : ℝ) ≤ C1 * bound N V T := h
          _ ≤ T ^ η * bound N V T := mul_le_mul_of_nonneg_right hmono1 hbnd0
          _ ≤ T ^ ε * bound N V T := mul_le_mul_of_nonneg_right hε3 hbnd0
      · have h := hMV b hb N V T R t hN hV (by linarith) hsep hIcc hD
        have hcomp := N_mul_V_neg_two_le_four (N : ℝ) V (by exact_mod_cast hN) hV h1
        have hsum : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))
            ≤ 17 * bound N V T := by
          have hN2 : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) ≤ bound N V T := by
            unfold bound
            have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
            have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
            linarith
          have hT2 : T * ((N : ℝ) * V ^ (-2 : ℤ)) ≤ 16 * bound N V T := by
            have h4 : T * ((N : ℝ) * V ^ (-2 : ℤ)) ≤ T * (16 * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) := by
              have h0 : 0 ≤ T := by linarith
              exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hcomp) h0
            have h5 : 16 * (T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) ≤ 16 * bound N V T := by
              have he : bound N V T = (N : ℝ) ^ 2 * V ^ (-2 : ℤ)
                  + (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ)
                  + T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)) := by
                unfold bound; ring
              rw [he]
              have h2 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
              have h3 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
              nlinarith [h2, h3]
            have h4' : T * ((N : ℝ) * V ^ (-2 : ℤ)) ≤ 16 * (T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) := by
              linarith [h4]
            linarith [h4', h5]
          linarith

        calc (R : ℝ) ≤ Cmv * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))) := h
          _ ≤ Cmv * (17 * bound N V T) := mul_le_mul_of_nonneg_left hsum (le_of_lt hCmv)
          _ = (Cmv * 17) * bound N V T := by ring
          _ ≤ T ^ η * bound N V T := mul_le_mul_of_nonneg_right hKmvT hbnd0
          _ ≤ T ^ ε * bound N V T := mul_le_mul_of_nonneg_right hε3 hbnd0
      · have h := h123 b hb N V T R t hN hV hT1' hsep hIcc hD (Or.inr (Or.inr h1))
        calc (R : ℝ) ≤ C1 * bound N V T := h
          _ ≤ T ^ η * bound N V T := mul_le_mul_of_nonneg_right hmono1 hbnd0
          _ ≤ T ^ ε * bound N V T := mul_le_mul_of_nonneg_right hε3 hbnd0
    exact hfin
  · push_neg at hcase
    obtain ⟨hNT, hVlo', hVhi'⟩ := hcase
    have hN6 : 6 ≤ N := by
      by_contra hc
      have hN5 : N ≤ 5 := by omega
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have h1 : 4 * (N : ℝ) ^ (7 / 10 : ℝ) < (N : ℝ) ^ (4 / 5 : ℝ) := lt_trans hVlo' hVhi'
      have hsplit : (N : ℝ) ^ (4 / 5 : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (7 / 10 : ℝ) := by
        rw [← Real.rpow_add hNpos]; norm_num
      rw [hsplit] at h1
      have h2 : 4 < (N : ℝ) ^ (1 / 10 : ℝ) := by
        have h3 : 4 * (N : ℝ) ^ (7 / 10 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (7 / 10 : ℝ) := h1
        have h9 : 0 < (N : ℝ) ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hNpos _
        exact lt_of_mul_lt_mul_right h3 (le_of_lt h9)
      have h4 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (5 : ℝ) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN5) (by norm_num)
      have h5 : (5 : ℝ) ^ (1 / 10 : ℝ) < 4 := by
        have h6 : ((5 : ℝ) ^ (1 / 10 : ℝ)) ^ 10 < (4 : ℝ) ^ 10 := by
          rw [← Real.rpow_natCast ((5 : ℝ) ^ (1 / 10 : ℝ)) 10,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
          norm_num
        exact lt_of_pow_lt_pow_left₀ 10 (by positivity) h6
      linarith
    by_cases hNle : N₀ ≤ N
    · set W : Finset ℝ := Finset.univ.image t with hW
      have hWcard : (W.card : ℝ) = (R : ℝ) := by
        rw [hW, Finset.card_image_of_injOn]
        · simp
        · intro i _ j _ hij
          by_contra hne
          have h1 : 1 ≤ |t i - t j| := hsep i j hne
          rw [hij, sub_self, abs_zero] at h1
          linarith
      have hWIcc : ∀ s ∈ W, s ∈ Set.Icc 0 T := by
        intro s hs
        rw [hW] at hs
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
        exact hIcc i
      have hWsep : ∀ s ∈ W, ∀ u ∈ W, s ≠ u → 1 ≤ |s - u| := by
        intro s hs u hu hsu
        rw [hW] at hs hu
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
        exact hsep i j (fun h => hsu (by rw [h]))
      have hWval : ∀ s ∈ W, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (s : ℂ))‖ := by
        intro s hs
        rw [hW] at hs
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
        exact hD i
      have h := hN₀ N hNle V T b W hN6 hNT (le_of_lt hVlo') (le_of_lt hVhi') hb hWIcc hWsep hWval
      rw [hWcard] at h
      have hNpow : (N : ℝ) ^ (4 * ε') ≤ T ^ (4 * ε') :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hNT) (by positivity)
      have h4ε' : 4 * ε' ≤ ε := by rw [hε'def]; linarith
      have hT4 : T ^ (4 * ε') ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le h1ε h4ε'
      calc (R : ℝ) ≤ C2 * (N : ℝ) ^ (4 * ε') * bound N V T := h
        _ ≤ C2 * T ^ (4 * ε') * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            exact mul_le_mul_of_nonneg_left hNpow (le_of_lt hC2)
        _ ≤ T ^ η * T ^ (4 * ε') * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            apply mul_le_mul_of_nonneg_right hC2T
            positivity
        _ = T ^ (η + 4 * ε') * bound N V T := by
            rw [← Real.rpow_add (by linarith : (0:ℝ) < T)]
        _ ≤ T ^ ε * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            apply Real.rpow_le_rpow_of_exponent_le h1ε
            rw [hηdef, hε'def]; linarith
    · push_neg at hNle
      have hV3 : 3 * (N : ℝ) ^ (7 / 10 : ℝ) ≤ V := by
        have h4 : (3:ℝ) * (N : ℝ) ^ (7 / 10 : ℝ) ≤ 4 * (N : ℝ) ^ (7 / 10 : ℝ) := by
          have h0 : (0:ℝ) ≤ (N : ℝ) ^ (7 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
          linarith
        linarith
      have h := hC3b b hb N V T R t hN hV (by linarith) hV3 (le_of_lt hVhi') hsep hIcc hD
      have hNle' : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (le_of_lt hNle)
      have hN15 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ ((N₀ : ℝ) + 1) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      calc (R : ℝ) ≤ C3 * (N : ℝ) ^ (1 / 5 : ℝ) * bound N V T := h
        _ ≤ C3 * ((N₀ : ℝ) + 1) ^ (1 / 5 : ℝ) * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            exact mul_le_mul_of_nonneg_left hN15 (le_of_lt hC3)
        _ ≤ (2 * C3 * ((N₀ : ℝ) + 1) ^ (1 / 5 : ℝ)) * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            nlinarith [hC3, Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N₀:ℝ)+1) (1/5:ℝ)]
        _ ≤ T ^ η * bound N V T := mul_le_mul_of_nonneg_right hK2T hbnd0
        _ ≤ T ^ ε * bound N V T := mul_le_mul_of_nonneg_right hε3 hbnd0


/-- **Guth–Maynard Theorem 1.1 from Proposition 4.1.**  The `o` is built by a diagonal choice:
`o T = 1/(kF T + 1)` where `kF T` is the largest `k ≤ ⌊log T⌋` for which all large-value data
with parameter `T` satisfy `R ≤ T^{1/(k+1)}·bound`; the diagonal is valid because for every fixed
`k` this property holds eventually in `T`. -/
theorem theorem_1_1_of_keyprop (hKey : KeyPropStatement) :
    ∃ o : ℝ → ℝ, o =o[Filter.atTop] (1 : ℝ → ℝ) ∧
      ∀ (b : ℕ → ℂ) (_hb : ∀ n, ‖b n‖ ≤ 1) (N : ℕ) (V : ℝ) (T : ℝ) (R : ℕ)
        (t : Fin R → ℝ),
      N > 0 → V > 0 → T > 1 →
      (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
      (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
      R ≤ T ^ (o T) * bound N V T := by
  classical
  have hmain := main_bound_of_keyprop hKey
  set P : ℝ → ℝ → Prop := fun T ε => ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (N : ℕ) (V : ℝ) (R : ℕ) (t : Fin R → ℝ),
        N > 0 → V > 0 → 1 < T →
        (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
        (R : ℝ) ≤ T ^ ε * bound N V T with hP
  have hPevent : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in Filter.atTop, P T ε :=
    fun ε hε => hmain ε hε
  obtain ⟨T₁₀, hT₁₀⟩ := Filter.eventually_atTop.mp (hPevent (1 / (((0 : ℕ) : ℝ) + 1)) (by positivity))
  set T₁ : ℝ := max T₁₀ 2 with hT₁def
  have hT₁spec : ∀ T : ℝ, T₁ ≤ T → P T (1 / (((0 : ℕ) : ℝ) + 1)) :=
    fun T hT => hT₁₀ T (le_trans (le_max_left _ _) hT)
  set kF : ℝ → ℕ := fun T => Nat.findGreatest (fun k => P T (1 / ((k : ℝ) + 1)))
    ⌊Real.log T⌋₊ with hkF
  set o : ℝ → ℝ := fun T => if 1 < T then
      (if T ≤ T₁ then Real.log (8 * (T + 1)) / Real.log T else 0)
        + 1 / ((kF T : ℝ) + 1) else 0 with ho
  have hkFspec : ∀ T : ℝ, T₁ ≤ T → P T (1 / ((kF T : ℝ) + 1)) := by
    intro T hT
    exact Nat.findGreatest_spec (P := fun k => P T (1 / ((k : ℝ) + 1))) (n := ⌊Real.log T⌋₊)
      (m := 0) (Nat.zero_le _) (hT₁spec T hT)
  have hkFtend : ∀ m : ℕ, ∀ᶠ T : ℝ in Filter.atTop, m ≤ kF T := by
    intro m
    filter_upwards [hPevent (1 / (((m : ℕ) : ℝ) + 1)) (by positivity),
      (Real.tendsto_log_atTop.eventually_ge_atTop (m : ℝ)),
      Filter.eventually_ge_atTop (1 : ℝ)] with T hPT hT hT1
    exact Nat.le_findGreatest (Nat.le_floor_iff (Real.log_nonneg hT1) |>.mpr hT) hPT
  refine ⟨o, ?_, ?_⟩
  · rw [show (1 : ℝ → ℝ) = (fun _ : ℝ => 1) from rfl, Asymptotics.isLittleO_one_iff ℝ,
      Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Filter.eventually_gt_atTop T₁, hkFtend (Nat.ceil (1 / ε) + 1)] with T hT hkT
    have hT₁ge2 : (2 : ℝ) ≤ T₁ := by rw [hT₁def]; exact le_max_right _ _
    have h1 : 1 < T := by linarith [le_of_lt hT]
    have h2 : ¬ T ≤ T₁ := not_le.mpr hT
    have hkFpos : 0 < (kF T : ℝ) + 1 := by positivity
    have hkey : o T = 1 / ((kF T : ℝ) + 1) := by
      rw [ho]; simp [h1, h2]
    rw [hkey, Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0:ℝ) < 1 / ((kF T : ℝ) + 1))]
    rw [div_lt_iff₀ hkFpos]
    have hle : 1 / ε ≤ (kF T : ℝ) := by
      have h1' : ((Nat.ceil (1 / ε) : ℕ) : ℝ) ≤ (kF T : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hkT)
      have h2' : 1 / ε ≤ ((Nat.ceil (1 / ε) : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    have hmul : ε * (1 / ε) ≤ ε * (kF T : ℝ) := mul_le_mul_of_nonneg_left hle hε.le
    have hone : ε * (1 / ε) = 1 := by field_simp
    rw [hone] at hmul
    linarith
  · intro b hb N V T R t hN hV hT1 hsep hIcc hD
    have hbnd0 : 0 ≤ bound N V T := by
      unfold bound
      have h1 : 0 ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by positivity
      have h2 : 0 ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by positivity
      have h3 : 0 ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by
        have : 0 ≤ T := by linarith
        positivity
      linarith
    by_cases hT : T ≤ T₁
    · -- small `T`: the trivial bound
      have htriv : (R : ℝ) ≤ 4 * (T + 1) * bound N V T :=
        card_le_trivial b hb N V T R t hN hV (by linarith) hsep hIcc hD
      have hlog : 0 < Real.log T := Real.log_pos hT1
      have hpos : (0 : ℝ) < 8 * (T + 1) := by positivity
      have hkey : T ^ (Real.log (8 * (T + 1)) / Real.log T) = 8 * (T + 1) := by
        rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < T),
          show Real.log T * (Real.log (8 * (T + 1)) / Real.log T) = Real.log (8 * (T + 1)) by
            field_simp]
        exact Real.exp_log hpos
      have heq : o T = Real.log (8 * (T + 1)) / Real.log T + 1 / ((kF T : ℝ) + 1) := by
        rw [ho]; simp [hT1, hT]
      have hexp : T ^ (o T) = 8 * (T + 1) * T ^ (1 / ((kF T : ℝ) + 1)) := by
        rw [heq, Real.rpow_add (by linarith : (0 : ℝ) < T), hkey]
      have hone : 1 ≤ T ^ (1 / ((kF T : ℝ) + 1)) :=
        Real.one_le_rpow (le_of_lt hT1) (by positivity)
      calc (R : ℝ) ≤ 4 * (T + 1) * bound N V T := htriv
        _ ≤ 8 * (T + 1) * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            nlinarith [hT1]
        _ ≤ 8 * (T + 1) * T ^ (1 / ((kF T : ℝ) + 1)) * bound N V T := by
            apply mul_le_mul_of_nonneg_right _ hbnd0
            nlinarith [hone, hpos]
        _ = T ^ (o T) * bound N V T := by rw [hexp]
    · -- large `T`: the real estimate
      have hT' : T₁ ≤ T := le_of_lt (not_le.mp hT)
      have hk := hkFspec T hT'
      have hbnd := hk b hb N V R t hN hV hT1 hsep hIcc hD
      have heq : o T = 1 / ((kF T : ℝ) + 1) := by
        rw [ho]; simp [hT1, hT]
      calc (R : ℝ) ≤ T ^ (1 / ((kF T : ℝ) + 1)) * bound N V T := hbnd
        _ = T ^ (o T) * bound N V T := by rw [heq]

end Submission.LargeValues
