import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

namespace Work.GM.Energy.EnergyCore

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Real-exponent bookkeeping helpers -/

/-- `x^a * x^b = x^(a+b)` (rewriting form). -/
private lemma rpow_mul_add {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx a b).symm

/-- `(x^a)^b = x^(a*b)` (rewriting form). -/
private lemma rpow_pow_mul {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) :
    (x ^ a) ^ b = x ^ (a * b) := (Real.rpow_mul hx a b).symm

/-- Numeric input: `3 ≤ N^{3/5}` for `N ≥ 100`. -/
private lemma three_le_rpow_three_fifths {N : ℝ} (hN : 100 ≤ N) :
    (3 : ℝ) ≤ N ^ ((3 : ℝ) / 5) := by
  have h27 : (27 : ℝ) ^ ((3 : ℝ) / 5) = (3 : ℝ) ^ ((9 : ℝ) / 5) := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ 3 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h1 : (3 : ℝ) ≤ (27 : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [h27]
    calc (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ (3 : ℝ) ^ ((9 : ℝ) / 5) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (27 : ℝ) ^ ((3 : ℝ) / 5) ≤ (100 : ℝ) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have h3 : (100 : ℝ) ^ ((3 : ℝ) / 5) ≤ N ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  linarith

/-- The case `T^{2/3} ≤ K`: the first terms of both brackets dominate, so
`√(A·B) ≤ C (cL+1)² √(sA sB) N^{4ε/5} N K³`. -/
private lemma case_big_aux (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 100 ≤ N → ∀ (T K E sA sB Λ cL A B : ℝ),
        T = (N : ℝ) ^ ((6 : ℝ) / 5) → T ^ ((2 : ℝ) / 3) ≤ K →
        1 ≤ Λ → 0 ≤ cL → Λ ≤ cL * (N : ℝ) ^ (ε / 5) →
        0 ≤ K → K ^ 2 ≤ E → E ≤ 3 * K ^ 3 → 0 ≤ sA → 0 ≤ sB → 0 ≤ A → 0 ≤ B →
        A ≤ sA * (K ^ 2 * ((N : ℝ) * Λ) + K * T
              + K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        B ≤ sB * (K ^ 4 * ((N : ℝ) * Λ) + E * T
              + E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        Real.sqrt (A * B) ≤ C * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
          * ((N : ℝ) * K ^ 3) := by
  refine ⟨4, by norm_num, ?_⟩
  intro N hN T K E sA sB Λ cL A B hT hcase hΛ1 hcL0 hΛcL hK0 hKE2 hKE3 hsA hsB hA0 hB0 hAle hBle
  have hN100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hTpos : 0 < T := by rw [hT]; exact Real.rpow_pos_of_pos hNpos _
  have hTnn : 0 ≤ T := hTpos.le
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; exact Real.one_le_rpow hN1 (by norm_num)
  have hEnn : 0 ≤ E := le_trans (pow_nonneg hK0 2) hKE2
  have hT23 : T ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [hT, ← Real.rpow_mul hNnn]; norm_num
  have hNK : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ K := by rw [← hT23]; exact hcase
  have hKpos : 0 < K := by
    have h1 : (1 : ℝ) ≤ T ^ ((2 : ℝ) / 3) := Real.one_le_rpow hT1 (by norm_num)
    linarith [h1, hcase]
  -- (b1) `T^{1/2} ≤ K^{3/4}`
  have h1a : T ^ ((1 : ℝ) / 2) ≤ K ^ ((3 : ℝ) / 4) := by
    have hhalf : T ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((3 : ℝ) / 5) := by
      rw [hT, ← Real.rpow_mul hNnn]; norm_num
    rw [hhalf]
    calc (N : ℝ) ^ ((3 : ℝ) / 5) = ((N : ℝ) ^ ((4 : ℝ) / 5)) ^ ((3 : ℝ) / 4) := by
          rw [rpow_pow_mul hNnn ((4 : ℝ) / 5) ((3 : ℝ) / 4)]; norm_num
      _ ≤ K ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow (Real.rpow_nonneg hNnn _) hNK (by norm_num)
  -- (b2) `T ≤ K * N`
  have hN95 : (N : ℝ) ^ ((9 : ℝ) / 5) = (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) := by
    conv_rhs => rhs; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNpos]; norm_num
  have h1b : T ≤ K * (N : ℝ) := by
    have h2 : T ≤ (N : ℝ) ^ ((9 : ℝ) / 5) := by
      rw [hT]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have h4 : (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ≤ K * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hNK hNnn
    linarith [hN95, h2, h4]
  -- (b3) `3 * T ≤ K * N`
  have h1c : 3 * T ≤ K * (N : ℝ) := by
    have hn1 : (3 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 5) := three_le_rpow_three_fifths hN100
    have hcomb : (N : ℝ) ^ ((3 : ℝ) / 5) * (N : ℝ) ^ ((6 : ℝ) / 5)
        = (N : ℝ) ^ ((9 : ℝ) / 5) := by
      rw [rpow_mul_add hNpos]; norm_num
    have h2 : 3 * T ≤ (N : ℝ) ^ ((9 : ℝ) / 5) := by
      have hle : (3 : ℝ) * (N : ℝ) ^ ((6 : ℝ) / 5)
          ≤ (N : ℝ) ^ ((3 : ℝ) / 5) * (N : ℝ) ^ ((6 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hn1 (Real.rpow_nonneg hNnn _)
      rw [hT]; linarith [hle, hcomb]
    have h4 : (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ≤ K * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hNK hNnn
    linarith [hN95, h2, h4]
  -- the six summands
  set P1 : ℝ := K ^ 2 * ((N : ℝ) * Λ) with hP1
  set P2 : ℝ := K * T with hP2
  set P3 : ℝ := K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) with hP3
  set Q1 : ℝ := K ^ 4 * ((N : ℝ) * Λ) with hQ1
  set Q2 : ℝ := E * T with hQ2
  set Q3 : ℝ := E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) with hQ3
  have hP1nn : 0 ≤ P1 := by rw [hP1]; positivity
  have hP2nn : 0 ≤ P2 := by rw [hP2]; positivity
  have hP3nn : 0 ≤ P3 := by rw [hP3]; positivity
  have hQ1nn : 0 ≤ Q1 := by rw [hQ1]; positivity
  have hQ2nn : 0 ≤ Q2 := by rw [hQ2]; positivity
  have hQ3nn : 0 ≤ Q3 := by rw [hQ3]; positivity
  -- `P3 ≤ P1`
  have hP3le : P3 ≤ P1 := by
    rw [hP3, hP1]
    have h1 : K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) ≤ K ^ ((5 : ℝ) / 4) * K ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left h1a (Real.rpow_nonneg hK0 _)
    have h2 : K ^ ((5 : ℝ) / 4) * K ^ ((3 : ℝ) / 4) = K ^ 2 := by
      rw [rpow_mul_add hKpos]; norm_num
    calc K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)
        ≤ K ^ ((5 : ℝ) / 4) * K ^ ((3 : ℝ) / 4) * ((N : ℝ) * Λ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K ^ 2 * ((N : ℝ) * Λ) := by rw [h2]
  -- `P2 ≤ P1`
  have hP2le : P2 ≤ P1 := by
    rw [hP2, hP1]
    have hTN' : T ≤ K * ((N : ℝ) * Λ) := by
      calc T ≤ K * (N : ℝ) := h1b
        _ ≤ K * ((N : ℝ) * Λ) := by
            apply mul_le_mul_of_nonneg_left _ hK0
            exact le_mul_of_one_le_right hNnn hΛ1
    calc K * T ≤ K * (K * ((N : ℝ) * Λ)) := mul_le_mul_of_nonneg_left hTN' hK0
      _ = K ^ 2 * ((N : ℝ) * Λ) := by ring
  -- `Q2 ≤ Q1`
  have hQ2le : Q2 ≤ Q1 := by
    rw [hQ2, hQ1]
    calc E * T ≤ 3 * K ^ 3 * T := mul_le_mul_of_nonneg_right hKE3 hTnn
      _ = K ^ 3 * (3 * T) := by ring
      _ ≤ K ^ 3 * (K * (N : ℝ)) := mul_le_mul_of_nonneg_left h1c (pow_nonneg hK0 3)
      _ = K ^ 4 * (N : ℝ) := by ring
      _ ≤ K ^ 4 * ((N : ℝ) * Λ) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 4)
          exact le_mul_of_one_le_right hNnn hΛ1
  -- `Q3 ≤ 3 * Q1`
  have hQ3le : Q3 ≤ 3 * Q1 := by
    rw [hQ3, hQ1]
    have hE4 : E ^ ((3 : ℝ) / 4) ≤ (3 * K ^ 3) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hEnn hKE3 (by norm_num)
    have hE4' : (3 * K ^ 3) ^ ((3 : ℝ) / 4) = (3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (pow_nonneg hK0 3)]
      congr 1
      rw [← Real.rpow_natCast K 3, rpow_pow_mul hK0 ((3 : ℕ) : ℝ) ((3 : ℝ) / 4)]
      norm_num
    have hc : (3 : ℝ) ^ ((3 : ℝ) / 4) ≤ (3 : ℝ) := by
      calc (3 : ℝ) ^ ((3 : ℝ) / 4) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = (3 : ℝ) := Real.rpow_one 3
    have hNK' : 0 ≤ (N : ℝ) * Λ := by positivity
    have hT4 : K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) ≤ K ^ 4 := by
      have s0 : K ^ ((9 : ℝ) / 4) * K = K ^ ((13 : ℝ) / 4) := by
        conv_lhs => rhs; rw [← Real.rpow_one K]
        rw [← Real.rpow_add hKpos]; norm_num
      have s1 : K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2)
          ≤ K ^ ((9 : ℝ) / 4) * K * K ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left h1a (by positivity)
      have s2 : K ^ ((9 : ℝ) / 4) * K * K ^ ((3 : ℝ) / 4) = K ^ 4 := by
        rw [s0, rpow_mul_add hKpos]; norm_num
      linarith [s1, s2]
    have hXY : (3 : ℝ) ^ ((3 : ℝ) / 4) * (K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2))
        ≤ (3 : ℝ) * K ^ 4 := by
      calc (3 : ℝ) ^ ((3 : ℝ) / 4) * (K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2))
          ≤ (3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ 4 :=
            mul_le_mul_of_nonneg_left hT4 (Real.rpow_nonneg (by norm_num) _)
        _ ≤ (3 : ℝ) * K ^ 4 := mul_le_mul_of_nonneg_right hc (pow_nonneg hK0 4)
    have hstep : (3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2)
          * ((N : ℝ) * Λ) ≤ 3 * (K ^ 4 * ((N : ℝ) * Λ)) := by
      calc (3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)
          = (3 : ℝ) ^ ((3 : ℝ) / 4) * (K ^ ((9 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2)) * ((N : ℝ) * Λ) := by
            ring
        _ ≤ (3 : ℝ) * K ^ 4 * ((N : ℝ) * Λ) := mul_le_mul_of_nonneg_right hXY hNK'
        _ = 3 * (K ^ 4 * ((N : ℝ) * Λ)) := by ring
    calc E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)
        ≤ ((3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4)) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) := by
          calc E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)
              = (E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2)) * ((N : ℝ) * Λ) := by ring
            _ ≤ ((3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4)) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) := by
                apply mul_le_mul_of_nonneg_right _ hNK'
                calc E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2)
                    = (E ^ ((3 : ℝ) / 4) * K) * T ^ ((1 : ℝ) / 2) := by ring
                  _ ≤ (((3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4)) * K) * T ^ ((1 : ℝ) / 2) := by
                      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hTnn _)
                      exact mul_le_mul_of_nonneg_right (le_trans hE4 (le_of_eq hE4')) hK0
                  _ = ((3 : ℝ) ^ ((3 : ℝ) / 4) * K ^ ((9 : ℝ) / 4)) * K * T ^ ((1 : ℝ) / 2) := by ring
      _ ≤ 3 * (K ^ 4 * ((N : ℝ) * Λ)) := hstep
  -- sums
  have hPle : P1 + P2 + P3 ≤ 3 * P1 := by linarith [hP2le, hP3le, hP2nn, hP3nn]
  have hQle : Q1 + Q2 + Q3 ≤ 5 * Q1 := by linarith [hQ2le, hQ3le, hQ1nn, hQ2nn, hQ3nn]
  have hA' : A ≤ 3 * sA * P1 := by
    calc A ≤ sA * (P1 + P2 + P3) := hAle
      _ ≤ sA * (3 * P1) := mul_le_mul_of_nonneg_left hPle hsA
      _ = 3 * sA * P1 := by ring
  have hB' : B ≤ 5 * sB * Q1 := by
    calc B ≤ sB * (Q1 + Q2 + Q3) := hBle
      _ ≤ sB * (5 * Q1) := mul_le_mul_of_nonneg_left hQle hsB
      _ = 5 * sB * Q1 := by ring
  have hAB : A * B ≤ 15 * sA * sB * (K ^ 6 * (N : ℝ) ^ 2 * Λ ^ 2) := by
    have hKc : K ^ 2 * K ^ 4 = K ^ 6 := by rw [← pow_add]
    have hPQ : P1 * Q1 = K ^ 6 * (N : ℝ) ^ 2 * Λ ^ 2 := by
      rw [hP1, hQ1]
      calc K ^ 2 * ((N : ℝ) * Λ) * (K ^ 4 * ((N : ℝ) * Λ))
          = K ^ 2 * K ^ 4 * (((N : ℝ) * Λ) * ((N : ℝ) * Λ)) := by ring
        _ = K ^ 6 * (N : ℝ) ^ 2 * Λ ^ 2 := by rw [hKc]; ring
    have hmul : A * B ≤ (3 * sA * P1) * (5 * sB * Q1) := mul_le_mul hA' hB' hB0 (by positivity)
    have heq : (3 * sA * P1) * (5 * sB * Q1) = 15 * sA * sB * (K ^ 6 * (N : ℝ) ^ 2 * Λ ^ 2) := by
      rw [show (3 * sA * P1) * (5 * sB * Q1) = 15 * sA * sB * (P1 * Q1) by ring, hPQ]
    linarith [hmul, heq]
  have hLam : Λ ^ 2 ≤ (cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5) := by
    have h1 : Λ ^ 2 ≤ (cL * (N : ℝ) ^ (ε / 5)) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hΛ1]) hΛcL 2
    have h2 : (cL * (N : ℝ) ^ (ε / 5)) ^ 2 = cL ^ 2 * (N : ℝ) ^ (2 * ε / 5) := by
      rw [mul_pow]
      congr 1
      rw [pow_two, (Real.rpow_add hNpos (ε / 5) (ε / 5)).symm]
      congr 1
      ring
    have h3 : cL ^ 2 ≤ (cL + 1) ^ 4 := by
      have hc1 : cL ^ 2 ≤ (cL + 1) ^ 2 := by nlinarith [sq_nonneg cL]
      calc cL ^ 2 ≤ (cL + 1) ^ 2 := hc1
        _ ≤ ((cL + 1) ^ 2) ^ 2 := by nlinarith [sq_nonneg (cL + 1)]
        _ = (cL + 1) ^ 4 := by ring
    have h4 : (N : ℝ) ^ (2 * ε / 5) ≤ (N : ℝ) ^ (8 * ε / 5) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc Λ ^ 2 ≤ cL ^ 2 * (N : ℝ) ^ (2 * ε / 5) := by rw [← h2]; exact h1
      _ ≤ (cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
  have hmain : A * B
      ≤ (4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
          * ((N : ℝ) * K ^ 3)) ^ 2 := by
    have step : 15 * sA * sB * (K ^ 6 * (N : ℝ) ^ 2 * Λ ^ 2)
        ≤ 15 * sA * sB * (K ^ 6 * (N : ℝ) ^ 2 * ((cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hLam (by positivity)
    refine le_trans hAB (le_trans step ?_)
    have hsq : Real.sqrt (sA * sB) ^ 2 = sA * sB := Real.sq_sqrt (by positivity)
    have hNsq : ((N : ℝ) ^ (4 * ε / 5)) ^ 2 = (N : ℝ) ^ (8 * ε / 5) := by
      rw [pow_two, (Real.rpow_add hNpos (4 * ε / 5) (4 * ε / 5)).symm]
      congr 1
      ring
    have hexp : (4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
          * ((N : ℝ) * K ^ 3)) ^ 2
        = 16 * (cL + 1) ^ 4 * (sA * sB) * (N : ℝ) ^ (8 * ε / 5) * ((N : ℝ) ^ 2 * K ^ 6) := by
      rw [show (4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
              * ((N : ℝ) * K ^ 3)) ^ 2
            = (4 * (cL + 1) ^ 2) ^ 2 * (Real.sqrt (sA * sB)) ^ 2
              * ((N : ℝ) ^ (4 * ε / 5)) ^ 2 * ((N : ℝ) * K ^ 3) ^ 2 by ring,
          hsq, hNsq]
      ring
    rw [hexp]
    have hX : 0 ≤ sA * sB * ((cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5)) * (K ^ 6 * (N : ℝ) ^ 2) := by
      positivity
    rw [show 15 * sA * sB * (K ^ 6 * (N : ℝ) ^ 2 * ((cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5)))
          = 15 * (sA * sB * ((cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5)) * (K ^ 6 * (N : ℝ) ^ 2)) by ring,
        show 16 * (cL + 1) ^ 4 * (sA * sB) * (N : ℝ) ^ (8 * ε / 5) * ((N : ℝ) ^ 2 * K ^ 6)
          = 16 * (sA * sB * ((cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5)) * (K ^ 6 * (N : ℝ) ^ 2)) by ring]
    linarith [hX]
  have hXnn : 0 ≤ 4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
      * ((N : ℝ) * K ^ 3) := by positivity
  calc Real.sqrt (A * B)
      ≤ Real.sqrt ((4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
          * ((N : ℝ) * K ^ 3)) ^ 2) := Real.sqrt_le_sqrt hmain
    _ = 4 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5) * ((N : ℝ) * K ^ 3) :=
        Real.sqrt_sq hXnn
/-- The case `K ≤ T^{2/3}`: the last terms of both brackets dominate, so
`√(A·B) ≤ C (cL+1)² √(sA sB) N^{4ε/5} (N T^{1/4}K^{21/8} + E^{1/2}K^{1/2}N²)`. -/
private lemma case_small_aux (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 100 ≤ N → ∀ (T K E sA sB Λ cL A B : ℝ),
        T = (N : ℝ) ^ ((6 : ℝ) / 5) → K ≤ T ^ ((2 : ℝ) / 3) →
        1 ≤ Λ → 0 ≤ cL → Λ ≤ cL * (N : ℝ) ^ (ε / 5) →
        0 ≤ K → K ^ 2 ≤ E → E ≤ 3 * K ^ 3 → 0 ≤ sA → 0 ≤ sB → 0 ≤ A → 0 ≤ B →
        A ≤ sA * (K ^ 2 * ((N : ℝ) * Λ) + K * T
              + K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        B ≤ sB * (K ^ 4 * ((N : ℝ) * Λ) + E * T
              + E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        Real.sqrt (A * B) ≤ C * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
          * ((N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
              + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
  refine ⟨8, by norm_num, ?_⟩
  intro N hN T K E sA sB Λ cL A B hT hcase hΛ1 hcL0 hΛcL hK0 hKE2 hKE3 hsA hsB hA0 hB0 hAle hBle
  have hN100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hTpos : 0 < T := by rw [hT]; exact Real.rpow_pos_of_pos hNpos _
  have hTnn : 0 ≤ T := hTpos.le
  have hEnn : 0 ≤ E := le_trans (pow_nonneg hK0 2) hKE2
  rcases eq_or_lt_of_le hK0 with hKz | hKpos
  · -- `K = 0`
    subst hKz
    have hE0 : E = 0 := by
      have h : E ≤ 0 := by
        have h3 := hKE3
        norm_num at h3
        linarith [h3]
      linarith [hEnn, h]
    subst hE0
    have hA' : A = 0 := by
      have hbr : (0:ℝ)^2 * ((N:ℝ)*Λ) + 0 * T + (0:ℝ)^((5:ℝ)/4) * T^((1:ℝ)/2) * ((N:ℝ)*Λ) = 0 := by
        rw [Real.zero_rpow (by norm_num : ((5:ℝ)/4) ≠ 0)]
        ring
      have h := hAle
      rw [hbr, mul_zero] at h
      linarith [hA0, h]
    have hB' : B = 0 := by
      have hbr2 : (0:ℝ)^4 * ((N:ℝ)*Λ) + 0 * T + (0:ℝ)^((3:ℝ)/4) * 0 * T^((1:ℝ)/2) * ((N:ℝ)*Λ) = 0 := by
        ring
      have h := hBle
      rw [hbr2, mul_zero] at h
      linarith [hB0, h]
    rw [hA', hB', mul_zero, Real.sqrt_zero,
      Real.zero_rpow (by norm_num : ((21:ℝ)/8) ≠ 0), Real.zero_rpow (by norm_num : ((1:ℝ)/2) ≠ 0)]
    norm_num
  · -- `K > 0`
    have hEpos : 0 < E := lt_of_lt_of_le (pow_pos hKpos 2) hKE2
    have hK3 : (1:ℝ)/3 ≤ K := by
      have h1 : K^2 ≤ 3*K^3 := le_trans hKE2 hKE3
      have h2 : K^2 * 1 ≤ K^2 * (3*K) := by
        calc K^2 * 1 = K^2 := by ring
          _ ≤ 3*K^3 := h1
          _ = K^2 * (3*K) := by ring
      have h3 : 1 ≤ 3*K := le_of_mul_le_mul_left h2 (pow_pos hKpos 2)
      linarith
    have hT23 : T ^ ((2:ℝ)/3) = (N:ℝ)^((4:ℝ)/5) := by
      rw [hT, ← Real.rpow_mul hNnn]; norm_num
    have hKT : K ≤ (N:ℝ)^((4:ℝ)/5) := by rw [← hT23]; exact hcase
    have hT12 : T ^ ((1:ℝ)/2) = (N:ℝ)^((3:ℝ)/5) := by
      rw [hT, ← Real.rpow_mul hNnn]; norm_num
    -- (a) `K^{3/4} ≤ T^{1/2}`
    have ha : K ^ ((3:ℝ)/4) ≤ T ^ ((1:ℝ)/2) := by
      rw [hT12]
      calc K ^ ((3:ℝ)/4) ≤ ((N:ℝ)^((4:ℝ)/5)) ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow hK0 hKT (by norm_num)
        _ = (N:ℝ)^((3:ℝ)/5) := by rw [rpow_pow_mul hNnn ((4:ℝ)/5) ((3:ℝ)/4)]; norm_num
    -- (b) `T^{1/2} ≤ K^{1/4} N Λ`
    have hKN : 1 ≤ K * (N:ℝ) := by nlinarith [hN100, hK3]
    have hKNq : 1 ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((1:ℝ)/4) := by
      have h := Real.one_le_rpow hKN (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
      rwa [Real.mul_rpow hK0 hNnn] at h
    have hb2 : (N:ℝ)^((1:ℝ)/4) ≤ (N:ℝ)^((2:ℝ)/5) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hb3 : 1 ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) * Λ := by
      have h4 : K ^ ((1:ℝ)/4) * (N:ℝ)^((1:ℝ)/4) ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) :=
        mul_le_mul_of_nonneg_left hb2 (Real.rpow_nonneg hK0 _)
      have h5 : K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) * Λ :=
        le_mul_of_one_le_right (by positivity) hΛ1
      linarith
    have hb : T ^ ((1:ℝ)/2) ≤ K ^ ((1:ℝ)/4) * (N:ℝ) * Λ := by
      have hNpow : (N:ℝ)^((2:ℝ)/5) * (N:ℝ)^((3:ℝ)/5) = (N:ℝ) := by
        rw [rpow_mul_add hNpos, show (2:ℝ)/5 + 3/5 = 1 by norm_num, Real.rpow_one]
      rw [hT12]
      calc (N:ℝ)^((3:ℝ)/5) = 1 * (N:ℝ)^((3:ℝ)/5) := by ring
        _ ≤ (K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) * Λ) * (N:ℝ)^((3:ℝ)/5) :=
            mul_le_mul_of_nonneg_right hb3 (Real.rpow_nonneg hNnn _)
        _ = K ^ ((1:ℝ)/4) * (N:ℝ) * Λ := by
            rw [show (K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) * Λ) * (N:ℝ)^((3:ℝ)/5)
                  = K ^ ((1:ℝ)/4) * ((N:ℝ)^((2:ℝ)/5) * (N:ℝ)^((3:ℝ)/5)) * Λ by ring, hNpow]
    -- (c) `3^{1/4} ≤ K^{1/4} N^{2/5}`
    have h16 : (16:ℝ) ^ ((1:ℝ)/4) = 2 := by
      rw [show (16:ℝ) = (2:ℝ)^4 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have hKN16 : 16 ≤ K * (N:ℝ) := by nlinarith [hN100, hK3]
    have hKN2 : 2 ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((1:ℝ)/4) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 16) hKN16 (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
      rw [h16, Real.mul_rpow hK0 hNnn] at h
      exact h
    have h3q : (3:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (3:ℝ) ≤ 16)
        (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
      rwa [h16] at h
    have h3K : (3:ℝ) ^ ((1:ℝ)/4) ≤ K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) :=
      le_trans h3q (le_trans hKN2 (mul_le_mul_of_nonneg_left hb2 (Real.rpow_nonneg hK0 _)))
    -- the six summands and the two terms of the conclusion
    set P1 : ℝ := K ^ 2 * ((N : ℝ) * Λ) with hP1
    set P2 : ℝ := K * T with hP2
    set P3 : ℝ := K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) with hP3
    set Q1 : ℝ := K ^ 4 * ((N : ℝ) * Λ) with hQ1
    set Q2 : ℝ := E * T with hQ2
    set Q3 : ℝ := E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ) with hQ3
    set R2 : ℝ := (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8) with hR2
    set R3 : ℝ := E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 with hR3
    have hP1nn : 0 ≤ P1 := by rw [hP1]; positivity
    have hP2nn : 0 ≤ P2 := by rw [hP2]; positivity
    have hP3nn : 0 ≤ P3 := by rw [hP3]; positivity
    have hQ1nn : 0 ≤ Q1 := by rw [hQ1]; positivity
    have hQ2nn : 0 ≤ Q2 := by rw [hQ2]; positivity
    have hQ3nn : 0 ≤ Q3 := by rw [hQ3]; positivity
    have hR2nn : 0 ≤ R2 := by rw [hR2]; positivity
    have hR3nn : 0 ≤ R3 := by rw [hR3]; positivity
    -- `P1 ≤ P3`
    have hP1le : P1 ≤ P3 := by
      rw [hP1, hP3]
      have hK2 : K ^ 2 = K ^ ((5:ℝ)/4) * K ^ ((3:ℝ)/4) := by
        rw [← Real.rpow_natCast K 2, rpow_mul_add hKpos]; norm_num
      rw [hK2]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg hK0 _)) (by positivity)
    -- `P2 ≤ P3`
    have hTsplit : T = T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2) := by
      have hh : T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2) = T ^ (1:ℝ) := by
        rw [rpow_mul_add hTpos]; norm_num
      rw [hh, Real.rpow_one]
    have hP2le : P2 ≤ P3 := by
      rw [hP2, hP3]
      have h1 : K * K ^ ((1:ℝ)/4) = K ^ ((5:ℝ)/4) := by
        conv_lhs => lhs; rw [← Real.rpow_one K]
        rw [rpow_mul_add hKpos]; norm_num
      calc K * T = K * (T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2)) := by
            conv_lhs => rhs; rw [hTsplit]
        _ = (K * T ^ ((1:ℝ)/2)) * T ^ ((1:ℝ)/2) := by ring
        _ ≤ (K * T ^ ((1:ℝ)/2)) * (K ^ ((1:ℝ)/4) * (N:ℝ) * Λ) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = K ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * ((N:ℝ)*Λ) := by
            rw [show (K * T ^ ((1:ℝ)/2)) * (K ^ ((1:ℝ)/4) * (N:ℝ) * Λ)
                  = (K * K ^ ((1:ℝ)/4)) * (T ^ ((1:ℝ)/2) * ((N:ℝ)*Λ)) by ring, h1]
            ring
    -- `Q2 ≤ Q3`
    have hE14 : E ^ ((1:ℝ)/4) ≤ (3:ℝ)^((1:ℝ)/4) * K ^ ((3:ℝ)/4) := by
      calc E ^ ((1:ℝ)/4) ≤ (3*K^3) ^ ((1:ℝ)/4) := Real.rpow_le_rpow hEnn hKE3 (by norm_num)
        _ = (3:ℝ)^((1:ℝ)/4) * K ^ ((3:ℝ)/4) := by
            rw [Real.mul_rpow (by norm_num) (pow_nonneg hK0 3)]
            congr 1
            rw [← Real.rpow_natCast K 3, rpow_pow_mul hK0 ((3:ℕ):ℝ) ((1:ℝ)/4)]
            norm_num
    have hQ2le : Q2 ≤ Q3 := by
      rw [hQ2, hQ3]
      have hkey : E ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/2) ≤ K * (N:ℝ) * Λ := by
        calc E ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/2)
            ≤ ((3:ℝ)^((1:ℝ)/4) * K ^ ((3:ℝ)/4)) * T ^ ((1:ℝ)/2) :=
              mul_le_mul_of_nonneg_right hE14 (Real.rpow_nonneg hTnn _)
          _ = (3:ℝ)^((1:ℝ)/4) * (K ^ ((3:ℝ)/4) * T ^ ((1:ℝ)/2)) := by ring
          _ ≤ (K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5)) * (K ^ ((3:ℝ)/4) * T ^ ((1:ℝ)/2)) :=
              mul_le_mul_of_nonneg_right h3K (by positivity)
          _ = K * (N:ℝ) := by
              have hK1' : K ^ ((1:ℝ)/4) * K ^ ((3:ℝ)/4) = K := by
                rw [rpow_mul_add hKpos, show (1:ℝ)/4 + 3/4 = 1 by norm_num, Real.rpow_one]
              have hN1' : (N:ℝ)^((2:ℝ)/5) * T ^ ((1:ℝ)/2) = (N:ℝ) := by
                rw [hT12, rpow_mul_add hNpos, show (2:ℝ)/5 + 3/5 = 1 by norm_num, Real.rpow_one]
              calc K ^ ((1:ℝ)/4) * (N:ℝ)^((2:ℝ)/5) * (K ^ ((3:ℝ)/4) * T ^ ((1:ℝ)/2))
                  = (K ^ ((1:ℝ)/4) * K ^ ((3:ℝ)/4)) * ((N:ℝ)^((2:ℝ)/5) * T ^ ((1:ℝ)/2)) := by ring
                _ = K * (N:ℝ) := by rw [hK1', hN1']
          _ ≤ K * (N:ℝ) * Λ := le_mul_of_one_le_right (by positivity) hΛ1
      have hEsplit : E = E ^ ((3:ℝ)/4) * E ^ ((1:ℝ)/4) := by
        conv_lhs => rw [← Real.rpow_one E]
        rw [rpow_mul_add hEpos]; norm_num
      have hE3 : E * T = E ^ ((3:ℝ)/4) * (E ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2)) := by
        conv_lhs => lhs; rw [hEsplit]
        conv_lhs => rhs; rw [hTsplit]
        ring
      calc E * T = E ^ ((3:ℝ)/4) * (E ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2)) := hE3
        _ ≤ E ^ ((3:ℝ)/4) * ((K * (N:ℝ) * Λ) * T ^ ((1:ℝ)/2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hTnn _)) (Real.rpow_nonneg hEnn _)
        _ = E ^ ((3:ℝ)/4) * K * T ^ ((1:ℝ)/2) * ((N:ℝ) * Λ) := by ring
    -- sums
    have hPle : P1 + P2 + P3 ≤ 3 * P3 := by linarith [hP1le, hP2le, hP1nn, hP2nn]
    have hQle : Q1 + Q2 + Q3 ≤ Q1 + 2 * Q3 := by linarith [hQ2le, hQ3nn]
    have hA' : A ≤ 3 * sA * P3 := by
      calc A ≤ sA * (P1 + P2 + P3) := hAle
        _ ≤ sA * (3 * P3) := mul_le_mul_of_nonneg_left hPle hsA
        _ = 3 * sA * P3 := by ring
    have hB' : B ≤ sB * (Q1 + 2 * Q3) := by
      calc B ≤ sB * (Q1 + Q2 + Q3) := hBle
        _ ≤ sB * (Q1 + 2 * Q3) := mul_le_mul_of_nonneg_left hQle hsB
    -- the Λ bound
    have hlam2 : Λ ^ 2 ≤ cL ^ 2 * (N : ℝ) ^ (2 * ε / 5) := by
      have h1 : Λ ^ 2 ≤ (cL * (N : ℝ) ^ (ε / 5)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [hΛ1]) hΛcL 2
      have h2 : (cL * (N : ℝ) ^ (ε / 5)) ^ 2 = cL ^ 2 * (N : ℝ) ^ (2 * ε / 5) := by
        rw [mul_pow]
        congr 1
        rw [pow_two, (Real.rpow_add hNpos (ε / 5) (ε / 5)).symm]
        congr 1
        ring
      rw [← h2]; exact h1
    have hcL4 : cL ^ 2 ≤ (cL + 1) ^ 4 := by
      have hc1 : cL ^ 2 ≤ (cL + 1) ^ 2 := by nlinarith [sq_nonneg cL]
      calc cL ^ 2 ≤ (cL + 1) ^ 2 := hc1
        _ ≤ ((cL + 1) ^ 2) ^ 2 := by nlinarith [sq_nonneg (cL + 1)]
        _ = (cL + 1) ^ 4 := by ring
    have hNe : (N : ℝ) ^ (2 * ε / 5) ≤ (N : ℝ) ^ (8 * ε / 5) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hLam : Λ ^ 2 ≤ (cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5) :=
      calc Λ ^ 2 ≤ cL ^ 2 * (N : ℝ) ^ (2 * ε / 5) := hlam2
        _ ≤ (cL + 1) ^ 4 * (N : ℝ) ^ (8 * ε / 5) :=
            mul_le_mul hcL4 hNe (by positivity) (by positivity)
    -- `P3 * Q1 ≤ Λ² (R2 * R2)`
    have hTquarter : T ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4) = T ^ ((1:ℝ)/2) := by
      rw [rpow_mul_add hTpos]; norm_num
    have hKquarter : K ^ ((21:ℝ)/8) * K ^ ((21:ℝ)/8) = K ^ ((21:ℝ)/4) := by
      rw [rpow_mul_add hKpos]; norm_num
    have hP3Q1 : P3 * Q1 ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2 * R2) := by
      have hKq : K ^ ((5:ℝ)/4) * K^4 = K ^ ((21:ℝ)/4) := by
        rw [← Real.rpow_natCast K 4, rpow_mul_add hKpos]; norm_num
      have hprod : P3 * Q1 = Λ^2 * (R2 * R2) := by
        rw [hP3, hQ1, hR2]
        rw [show K ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * ((N:ℝ)*Λ) * (K^4 * ((N:ℝ)*Λ))
              = (K ^ ((5:ℝ)/4) * K^4) * (T ^ ((1:ℝ)/2) * (((N:ℝ)*Λ) * ((N:ℝ)*Λ))) by ring,
            hKq, ← hTquarter, ← hKquarter]
        ring
      calc P3 * Q1 = Λ^2 * (R2 * R2) := hprod
        _ ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2 * R2) :=
            mul_le_mul_of_nonneg_right hLam (by positivity)
    -- `P3 * Q3 ≤ (cL+1)⁴N^{8ε/5} (R3 * R3)`
    have hP3Q3 : P3 * Q3 ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3 * R3) := by
      have hEhalf : E ^ ((1:ℝ)/2) * E ^ ((1:ℝ)/2) = E := by
        rw [rpow_mul_add hEpos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
      have hKhalf : K ^ ((1:ℝ)/2) * K ^ ((1:ℝ)/2) = K := by
        rw [rpow_mul_add hKpos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
      have hR3sq : R3 * R3 = E * K * (N:ℝ)^4 := by
        rw [hR3,
          show E ^ ((1:ℝ)/2) * K ^ ((1:ℝ)/2) * (N:ℝ)^2 * (E ^ ((1:ℝ)/2) * K ^ ((1:ℝ)/2) * (N:ℝ)^2)
              = (E ^ ((1:ℝ)/2) * E ^ ((1:ℝ)/2)) * (K ^ ((1:ℝ)/2) * K ^ ((1:ℝ)/2))
                * ((N:ℝ)^2 * (N:ℝ)^2) by ring,
          hEhalf, hKhalf]
        ring
      have hkey2 : K ^ ((5:ℝ)/4) * T * Λ^2
          ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (E ^ ((1:ℝ)/4) * (N:ℝ)^2) := by
        have h1 : K ^ ((3:ℝ)/4) * T ≤ (N:ℝ)^((9:ℝ)/5) := by
          calc K ^ ((3:ℝ)/4) * T ≤ (N:ℝ)^((3:ℝ)/5) * (N:ℝ)^((6:ℝ)/5) :=
                mul_le_mul (by rw [← hT12]; exact ha) (le_of_eq hT) (by positivity) (by positivity)
            _ = (N:ℝ)^((9:ℝ)/5) := by rw [rpow_mul_add hNpos]; norm_num
        have h2 : K ^ ((5:ℝ)/4) * T * Λ^2 ≤ K ^ ((1:ℝ)/2) * (N:ℝ)^((9:ℝ)/5) * Λ^2 := by
          have hK5 : K ^ ((5:ℝ)/4) = K ^ ((1:ℝ)/2) * K ^ ((3:ℝ)/4) := by
            rw [rpow_mul_add hKpos]; norm_num
          calc K ^ ((5:ℝ)/4) * T * Λ^2 = (K ^ ((1:ℝ)/2) * K ^ ((3:ℝ)/4)) * T * Λ^2 := by rw [hK5]
            _ = K ^ ((1:ℝ)/2) * (K ^ ((3:ℝ)/4) * T) * Λ^2 := by ring
            _ ≤ K ^ ((1:ℝ)/2) * (N:ℝ)^((9:ℝ)/5) * Λ^2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg Λ)
                exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK0 _)
        have h4 : K ^ ((1:ℝ)/2) ≤ E ^ ((1:ℝ)/4) := by
          have h := Real.rpow_le_rpow (pow_nonneg hK0 2) hKE2 (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
          have hpow : (K ^ 2 : ℝ) ^ ((1:ℝ)/4) = K ^ ((1:ℝ)/2) := by
            rw [← Real.rpow_natCast K 2, rpow_pow_mul hK0 (((2:ℕ)):ℝ) ((1:ℝ)/4)]
            norm_num
          rwa [hpow] at h
        have h6 : (N:ℝ)^((9:ℝ)/5) * Λ^2 ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (N:ℝ)^2 := by
          have hNexp : (N:ℝ)^((9:ℝ)/5 + 2*ε/5) ≤ (N:ℝ)^(2 + 8*ε/5) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
          calc (N:ℝ)^((9:ℝ)/5) * Λ^2 ≤ (N:ℝ)^((9:ℝ)/5) * (cL^2 * (N:ℝ)^(2*ε/5)) :=
                mul_le_mul_of_nonneg_left hlam2 (Real.rpow_nonneg hNnn _)
            _ = cL^2 * ((N:ℝ)^((9:ℝ)/5) * (N:ℝ)^(2*ε/5)) := by ring
            _ = cL^2 * (N:ℝ)^((9:ℝ)/5 + 2*ε/5) := by rw [rpow_mul_add hNpos]
            _ ≤ (cL+1)^4 * (N:ℝ)^(2 + 8*ε/5) := mul_le_mul hcL4 hNexp (by positivity) (by positivity)
            _ = ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (N:ℝ)^2 := by
                rw [show (N:ℝ)^((2:ℝ) + 8*ε/5) = (N:ℝ)^(8*ε/5) * (N:ℝ)^2 from by
                      rw [show (2:ℝ) + 8*ε/5 = 8*ε/5 + 2 by ring, Real.rpow_add hNpos,
                        Real.rpow_two]]
                ring
        calc K ^ ((5:ℝ)/4) * T * Λ^2 ≤ K ^ ((1:ℝ)/2) * (N:ℝ)^((9:ℝ)/5) * Λ^2 := h2
          _ = K ^ ((1:ℝ)/2) * ((N:ℝ)^((9:ℝ)/5) * Λ^2) := by ring
          _ ≤ E ^ ((1:ℝ)/4) * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (N:ℝ)^2) :=
              mul_le_mul h4 h6 (by positivity) (Real.rpow_nonneg hEnn _)
          _ = ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (E ^ ((1:ℝ)/4) * (N:ℝ)^2) := by ring
      have hTsq : T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2) = T := by
        rw [rpow_mul_add hTpos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
      have hE34 : E ^ ((1:ℝ)/4) * E ^ ((3:ℝ)/4) = E := by
        rw [rpow_mul_add hEpos, show (1:ℝ)/4 + 3/4 = 1 by norm_num, Real.rpow_one]
      calc P3 * Q3 = (K ^ ((5:ℝ)/4) * T * Λ^2) * (K * (E ^ ((3:ℝ)/4) * (N:ℝ)^2)) := by
            rw [hP3, hQ3]
            conv_rhs => rw [← hTsq]
            ring
        _ ≤ (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (E ^ ((1:ℝ)/4) * (N:ℝ)^2))
              * (K * (E ^ ((3:ℝ)/4) * (N:ℝ)^2)) :=
            mul_le_mul_of_nonneg_right hkey2 (by positivity)
        _ = ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3 * R3) := by
            rw [hR3sq]
            calc ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (E ^ ((1:ℝ)/4) * (N:ℝ)^2)
                  * (K * (E ^ ((3:ℝ)/4) * (N:ℝ)^2))
                = ((cL+1)^4 * (N:ℝ)^(8*ε/5))
                  * ((E ^ ((1:ℝ)/4) * E ^ ((3:ℝ)/4)) * K * ((N:ℝ)^2 * (N:ℝ)^2)) := by ring
              _ = ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (E * K * (N:ℝ)^4) := by rw [hE34]; ring
    -- assemble
    have hRsum : R2 * R2 + R3 * R3 ≤ (R2 + R3) * (R2 + R3) := by nlinarith [hR2nn, hR3nn]
    set Y : ℝ := 8 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5) * (R2 + R3) with hYdef
    have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
    have hYsq : Y * Y = 64 * (cL+1)^4 * (sA*sB) * (N:ℝ)^(8*ε/5) * ((R2+R3)*(R2+R3)) := by
      have hsq : Real.sqrt (sA * sB) * Real.sqrt (sA * sB) = sA * sB := by
        rw [← pow_two, Real.sq_sqrt (by positivity)]
      have hNsq : (N:ℝ)^(4*ε/5) * (N:ℝ)^(4*ε/5) = (N:ℝ)^(8*ε/5) := by
        rw [rpow_mul_add hNpos]; congr 1; ring
      rw [hYdef,
        show (8 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5) * (R2 + R3))
              * (8 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5) * (R2 + R3))
            = (8 * 8) * ((cL + 1) ^ 2 * (cL + 1) ^ 2) * (Real.sqrt (sA*sB) * Real.sqrt (sA*sB))
              * ((N:ℝ)^(4*ε/5) * (N:ℝ)^(4*ε/5)) * ((R2+R3)*(R2+R3)) by ring,
        hsq, hNsq]
      ring
    have hmain : A * B ≤ Y * Y := by
      have step1 : A * B ≤ 3 * sA * sB * (P3 * Q1 + 2 * (P3 * Q3)) := by
        have h1 : A * B ≤ (3 * sA * P3) * (sB * (Q1 + 2*Q3)) :=
          mul_le_mul hA' hB' (by positivity) (by positivity)
        calc A * B ≤ (3 * sA * P3) * (sB * (Q1 + 2*Q3)) := h1
          _ = 3 * sA * sB * (P3 * Q1 + 2 * (P3 * Q3)) := by ring
      have step2 : 3 * sA * sB * (P3 * Q1 + 2 * (P3 * Q3))
          ≤ 3 * sA * sB * ((((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2))
              + 2 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3*R3))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hP3Q1 (mul_le_mul_of_nonneg_left hP3Q3 (by norm_num : (0:ℝ) ≤ 2))
      have hq : R2 * R2 + 2 * (R3 * R3) ≤ 2 * ((R2 + R3) * (R2 + R3)) := by
        nlinarith [hR2nn, hR3nn]
      have hJJ : 0 ≤ (cL+1)^4 * (N:ℝ)^(8*ε/5) := by positivity
      have step3 : 3 * sA * sB * ((((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2))
              + 2 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3*R3)))
          ≤ 6 * sA * sB * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3)) := by
        have h2 : (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2))
              + 2 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3*R3))
            ≤ 2 * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3)) := by
          calc ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2)
                + 2 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3*R3))
              = ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2 + 2*(R3*R3)) := by ring
            _ ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (2*((R2+R3)*(R2+R3))) :=
                mul_le_mul_of_nonneg_left hq hJJ
            _ = 2 * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3)) := by ring
        calc 3 * sA * sB * ((((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R2*R2))
              + 2 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (R3*R3)))
            ≤ 3 * sA * sB * (2 * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 6 * sA * sB * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3)) := by ring
      have step4 : 6 * sA * sB * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3)) ≤ Y * Y := by
        rw [hYsq]
        have hK : 0 ≤ ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (sA*sB) * ((R2+R3)*(R2+R3)) := by positivity
        rw [show 6 * sA * sB * ((cL+1)^4 * (N:ℝ)^(8*ε/5)) * ((R2+R3)*(R2+R3))
              = 6 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (sA*sB) * ((R2+R3)*(R2+R3))) by ring,
            show 64 * (cL + 1) ^ 4 * (sA * sB) * (N:ℝ)^(8*ε/5) * ((R2+R3)*(R2+R3))
              = 64 * (((cL+1)^4 * (N:ℝ)^(8*ε/5)) * (sA*sB) * ((R2+R3)*(R2+R3))) by ring]
        linarith [hK]
      linarith [step1, step2, step3, step4]
    calc Real.sqrt (A * B) ≤ Real.sqrt (Y * Y) := Real.sqrt_le_sqrt hmain
      _ = Y := Real.sqrt_mul_self hYnn

/-- Final real-variable simplification of GM Lemma 11.9: given
`A ⪅ sA (|W|²NΛ + |W|T + |W|^{5/4}T^{1/2}NΛ)` and
`B ⪅ sB (|W|⁴NΛ + E T + E^{3/4}|W|T^{1/2}NΛ)` with `T = M N = N^{6/5}`, `E(W) ≥ |W|²`,
`E(W) ≤ 3|W|³` and `Λ ≤ cL N^{ε/5}`, the product `√(AB)` is bounded by
`C (cL+1)² √(sA sB) N^{4ε/5} (N|W|³ + N T^{1/4}|W|^{21/8} + E^{1/2}|W|^{1/2}N²)`. -/
theorem assembly_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 100 ≤ N → ∀ (T K E sA sB Λ cL A B : ℝ),
        T = Submission.LargeValues.M N →
        1 ≤ T → T ^ ((1 : ℝ) / 2) ≤ (N : ℝ) → T ^ ((3 : ℝ) / 2) ≤ (N : ℝ) ^ 2 →
        1 ≤ Λ → 0 ≤ cL → Λ ≤ cL * (N : ℝ) ^ (ε / 5) →
        0 ≤ K → K ^ 2 ≤ E → E ≤ 3 * K ^ 3 →
        0 ≤ sA → 0 ≤ sB → 0 ≤ A → 0 ≤ B →
        A ≤ sA * (K ^ 2 * ((N : ℝ) * Λ) + K * T
              + K ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        B ≤ sB * (K ^ 4 * ((N : ℝ) * Λ) + E * T
              + E ^ ((3 : ℝ) / 4) * K * T ^ ((1 : ℝ) / 2) * ((N : ℝ) * Λ)) →
        Real.sqrt (A * B) ≤ C * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5) *
          ((N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
            + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
  obtain ⟨C1, hC1pos, hC1⟩ := case_big_aux ε hε
  obtain ⟨C2, hC2pos, hC2⟩ := case_small_aux ε hε
  refine ⟨max C1 C2, lt_max_of_lt_left hC1pos, ?_⟩
  intro N hN T K E sA sB Λ cL A B hTdef hT1 hThalf hT32 hΛ1 hcL0 hΛcL
    hK0 hKE2 hKE3 hsA hsB hA0 hB0 hAle hBle
  have hT : T = (N : ℝ) ^ ((6 : ℝ) / 5) := by rw [hTdef, Submission.LargeValues.M]
  have hEnn : 0 ≤ E := le_trans (pow_nonneg hK0 2) hKE2
  have hsum1 : (N : ℝ) * K ^ 3
      ≤ (N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
        + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 := by
    have h1 : 0 ≤ (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8) := by positivity
    have h2 : 0 ≤ E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 := by positivity
    linarith
  have hsum2 : (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
        + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2
      ≤ (N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
        + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 := by
    have h1 : 0 ≤ (N : ℝ) * K ^ 3 := by positivity
    linarith
  by_cases hcase : T ^ ((2 : ℝ) / 3) ≤ K
  · have h := hC1 N hN T K E sA sB Λ cL A B hT hcase hΛ1 hcL0 hΛcL
      hK0 hKE2 hKE3 hsA hsB hA0 hB0 hAle hBle
    calc Real.sqrt (A * B)
        ≤ C1 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * K ^ 3) := h
      _ ≤ max C1 C2 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * K ^ 3) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C1 C2 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
              + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
          gcongr
  · have hcase' : K ≤ T ^ ((2 : ℝ) / 3) := le_of_lt (not_le.mp hcase)
    have h := hC2 N hN T K E sA sB Λ cL A B hT hcase' hΛ1 hcL0 hΛcL
      hK0 hKE2 hKE3 hsA hsB hA0 hB0 hAle hBle
    calc Real.sqrt (A * B)
        ≤ C2 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
              + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := h
      _ ≤ max C1 C2 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
              + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
          gcongr
          exact le_max_right _ _
      _ ≤ max C1 C2 * (cL + 1) ^ 2 * Real.sqrt (sA * sB) * (N : ℝ) ^ (4 * ε / 5)
            * ((N : ℝ) * K ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * K ^ ((21 : ℝ) / 8)
              + E ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
          gcongr

end Work.GM.Energy.EnergyCore
