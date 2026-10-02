import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorAux

namespace Work.LinnikAreas.BGTZ

set_option maxHeartbeats 4000000

/-! ## Elementary estimates for the BGTZ size conditions (5.5), (5.6)

These are the explicit real-analysis inputs of `RepulsionSizes`: the growth of `(log q)^4` and of
`(log q)^28 * 2^48` against `q^{1/100}`, the Landau--Siegel lower bound for `1 - β₁` turned into an
upper bound for `(1-β₁)^{-1}`, and the comparison `log (2 + A²q³) ≤ 4 log q`. -/

lemma repulsionSizesLogLeThreeRpowThird {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 3 * x ^ (1 / 3 : ℝ) := by
  have h := Real.log_le_rpow_div (show (0:ℝ) ≤ x by linarith) (show (0:ℝ) < 1/3 by norm_num)
  have h2 : x ^ (1/3:ℝ) / (1/3:ℝ) = 3 * x ^ (1/3:ℝ) := by ring
  linarith [h, h2]

lemma repulsionSizesHundredLeRpowQuarter {L : ℝ} (hL : 100000000 ≤ L) : (100:ℝ) ≤ L ^ (1/4:ℝ) := by
  have h : ((100000000:ℝ)) ^ (1/4:ℝ) ≤ L ^ (1/4:ℝ) :=
    Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  have h2 : ((100000000:ℝ)) ^ (1/4:ℝ) = 100 := by
    have h : (100000000:ℝ) = (100:ℝ)^4 := by norm_num
    rw [h, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (show (0:ℝ) ≤ 100 by norm_num)]
    norm_num
  linarith [h, h2]

lemma repulsionSizesThreeQuartersLe {L : ℝ} (hL : 0 < L) (h100 : (100:ℝ) ≤ L ^ (1/4:ℝ)) :
    L ^ (3/4:ℝ) ≤ L / 100 := by
  have hsplit : L ^ (1/4:ℝ) * L ^ (3/4:ℝ) = L := by
    rw [← Real.rpow_add hL]; norm_num
  have h34nn : (0:ℝ) ≤ L ^ (3/4:ℝ) := Real.rpow_nonneg hL.le _
  linarith only [hsplit, mul_le_mul_of_nonneg_right h100 h34nn]

lemma repulsionSizesLogPow4LeRpow {X : ℝ} (hX : Real.exp 100000000 ≤ X) :
    (Real.log X)^4 ≤ X^(1/100:ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL : (100000000:ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : 0 < Real.log X := by linarith
  have hLe1 : (1:ℝ) ≤ Real.log X := by linarith
  have hlogL : Real.log (Real.log X) ≤ 3 * (Real.log X)^(1/3:ℝ) :=
    repulsionSizesLogLeThreeRpowThird hLe1
  have hL23 : (1200:ℝ) ≤ (Real.log X)^((2:ℝ)/3) := by
    have h1200 : ((1200:ℝ)) = ((1200:ℝ)^3)^(1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0:ℝ) ≤ 1200 by norm_num)]
      norm_num
    have h1200L2 : (1200:ℝ)^3 ≤ (Real.log X)^2 := by
      have h1 : ((100000000:ℝ))^2 ≤ (Real.log X)^2 :=
        pow_le_pow_left₀ (by norm_num) hL 2
      exact le_trans (by norm_num) h1
    have h2 : ((1200:ℝ)^3)^(1/3:ℝ) ≤ (((Real.log X)^2))^(1/3:ℝ) :=
      Real.rpow_le_rpow (by positivity) h1200L2 (by norm_num)
    have h3 : (((Real.log X)^2))^(1/3:ℝ) = (Real.log X)^((2:ℝ)/3) := by
      have hcast : ((Real.log X)^2) = (Real.log X)^(2:ℝ) := (Real.rpow_natCast _ 2).symm
      rw [hcast, ← Real.rpow_mul (show (0:ℝ) ≤ Real.log X by linarith)]
      norm_num
    linarith [h1200, h2, h3]
  have hkey : 4 * Real.log (Real.log X) ≤ (1/100) * Real.log X := by
    have hsplit : (Real.log X)^(1/3:ℝ) * (Real.log X)^((2:ℝ)/3) = Real.log X := by
      rw [← Real.rpow_add hLpos]; norm_num
    have h13 : (0:ℝ) ≤ (Real.log X)^(1/3:ℝ) := Real.rpow_nonneg hLpos.le _
    linarith only [hlogL, hsplit, mul_le_mul_of_nonneg_left hL23 h13]
  rw [Real.rpow_def_of_pos hXpos]
  apply (Real.log_le_iff_le_exp (show (0:ℝ) < (Real.log X)^4 by positivity)).mp
  rw [Real.log_pow]
  linarith [hkey]

lemma repulsionSizesLogPow28Le {X : ℝ} (hX : Real.exp 100000000 ≤ X) :
    (Real.log X)^28 * (2:ℝ)^48 ≤ X^(1/100:ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL : (100000000:ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : 0 < Real.log X := by linarith
  have hLe1 : (1:ℝ) ≤ Real.log X := by linarith
  have hlogL : Real.log (Real.log X) ≤ 3 * (Real.log X)^(1/3:ℝ) :=
    repulsionSizesLogLeThreeRpowThird hLe1
  have hL23 : (16800:ℝ) ≤ (Real.log X)^((2:ℝ)/3) := by
    have h1 : ((16800:ℝ)) = ((16800:ℝ)^3)^(1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0:ℝ) ≤ 16800 by norm_num)]
      norm_num
    have h2 : (16800:ℝ)^3 ≤ (Real.log X)^2 := by
      have h3 : ((100000000:ℝ))^2 ≤ (Real.log X)^2 :=
        pow_le_pow_left₀ (by norm_num) hL 2
      exact le_trans (by norm_num) h3
    have h4 : ((16800:ℝ)^3)^(1/3:ℝ) ≤ (((Real.log X)^2))^(1/3:ℝ) :=
      Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h5 : (((Real.log X)^2))^(1/3:ℝ) = (Real.log X)^((2:ℝ)/3) := by
      have hcast : ((Real.log X)^2) = (Real.log X)^(2:ℝ) := (Real.rpow_natCast _ 2).symm
      rw [hcast, ← Real.rpow_mul (show (0:ℝ) ≤ Real.log X by linarith)]
      norm_num
    linarith [h1, h4, h5]
  have hkey : 28 * Real.log (Real.log X) ≤ (1/200) * Real.log X := by
    have hsplit : (Real.log X)^(1/3:ℝ) * (Real.log X)^((2:ℝ)/3) = Real.log X := by
      rw [← Real.rpow_add hLpos]; norm_num
    have h13 : (0:ℝ) ≤ (Real.log X)^(1/3:ℝ) := Real.rpow_nonneg hLpos.le _
    linarith only [hlogL, hsplit, mul_le_mul_of_nonneg_left hL23 h13]
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  rw [Real.rpow_def_of_pos hXpos]
  apply (Real.log_le_iff_le_exp
    (show (0:ℝ) < (Real.log X)^28 * (2:ℝ)^48 by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  linarith [hkey, hlog2, hL]

lemma repulsionSizesSiegelInv {B δ q : ℝ} (hB : 1 ≤ B) (hq : 1 < q)
    (h : B / (q ^ (1/100:ℝ) * (Real.log q)^2) < δ) :
    0 < δ ∧ δ⁻¹ ≤ q ^ (1/100:ℝ) * (Real.log q)^2 := by
  have hq0 : (0:ℝ) < q := by linarith
  have hdenpos : 0 < q ^ (1/100:ℝ) * (Real.log q)^2 := by
    have h1 : 0 < Real.log q := Real.log_pos hq
    positivity
  have hfpos : 0 < B / (q ^ (1/100:ℝ) * (Real.log q)^2) := div_pos (by linarith) hdenpos
  have hδpos : 0 < δ := lt_trans hfpos h
  refine ⟨hδpos, ?_⟩
  have h1 : δ⁻¹ ≤ (B / (q ^ (1/100:ℝ) * (Real.log q)^2))⁻¹ := by
    simpa using one_div_le_one_div_of_le hfpos h.le
  have h2 : (B / (q ^ (1/100:ℝ) * (Real.log q)^2))⁻¹
      = (q ^ (1/100:ℝ) * (Real.log q)^2) / B := by rw [inv_div]
  have h3 : (q ^ (1/100:ℝ) * (Real.log q)^2) / B ≤ q ^ (1/100:ℝ) * (Real.log q)^2 := by
    rw [div_eq_mul_inv]
    calc (q ^ (1/100:ℝ) * (Real.log q)^2) * B⁻¹
        ≤ (q ^ (1/100:ℝ) * (Real.log q)^2) * 1 :=
          mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hB) (le_of_lt hdenpos)
      _ = q ^ (1/100:ℝ) * (Real.log q)^2 := mul_one _
  linarith [h1, h2, h3]

lemma repulsionSizesLogTwoAddQ3Le {A q : ℝ} (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hAq : A ≤ q^(1/1000:ℝ)) :
    Real.log (2 + A^2 * q^3) ≤ 4 * Real.log q := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hA0 : (0:ℝ) < A := by linarith
  have hAq' : A^2 ≤ q^(1/500:ℝ) := by
    have h1 : A^2 ≤ (q^(1/1000:ℝ))^2 := pow_le_pow_left₀ hA0.le hAq 2
    have h2 : (q^(1/1000:ℝ))^2 = q^(1/500:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; norm_num
    linarith [h1, h2]
  have hA2q : A^2 ≤ q^(1/2:ℝ) :=
    le_trans hAq' (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))
  have h1 : A^2 * q^3 ≤ q^(7/2:ℝ) := by
    have h2 : A^2 * q^3 ≤ q^(1/2:ℝ) * q^3 :=
      mul_le_mul_of_nonneg_right hA2q (by positivity)
    have h3 : q^(1/2:ℝ) * q^3 = q^(7/2:ℝ) := by
      rw [← Real.rpow_natCast q 3, ← Real.rpow_add hq0]; norm_num
    linarith [h2, h3]
  have h2 : (2:ℝ) ≤ q^(1/2:ℝ) := by
    have h6 : ((2:ℝ)^2) ≤ q := by nlinarith [hq]
    have h7 := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ (2:ℝ)^2) h6
      (by norm_num : (0:ℝ) ≤ 1/2)
    have h8 : (((2:ℝ)^2))^(1/2:ℝ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    linarith [h7, h8]
  have h3 : (2:ℝ) ≤ q^(7/2:ℝ) :=
    le_trans h2 (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))
  have h4 : (2:ℝ) + A^2 * q^3 ≤ q^4 := by
    have h8 : q^(1/2:ℝ) + q^(7/2:ℝ) ≤ q^(1/2:ℝ) * q^(7/2:ℝ) := by nlinarith [h2, h3]
    have h9 : q^(1/2:ℝ) * q^(7/2:ℝ) = q^4 := by
      rw [← Real.rpow_add hq0]; norm_num
    linarith [h1, h8, h9]
  calc Real.log (2 + A^2 * q^3) ≤ Real.log (q^4) := Real.log_le_log (by positivity) h4
    _ = 4 * Real.log q := by rw [Real.log_pow]; norm_num

/-- `Cd*A²*exp(2 L^{3/4})*(1-β₁)^{-2} ≤ q^{53/1000}`. -/
lemma repulsionSizesRBound {q Cd A β₁ : ℝ} (hq : 0 < q) (hδ : 0 < 1 - β₁)
    (hCd_le : Cd ≤ q^(1/1000:ℝ)) (hA2_le : A^2 ≤ q^(1/500:ℝ))
    (hexp2 : Real.exp (2 * (Real.log q)^(3/4:ℝ)) ≤ q^(1/50:ℝ))
    (hδ2 : (1-β₁)^(-2:ℝ) ≤ q^(1/50:ℝ) * (Real.log q)^4)
    (hL4 : (Real.log q)^4 ≤ q^(1/100:ℝ)) :
    Cd * A^2 * Real.exp (2 * (Real.log q)^(3/4:ℝ)) * (1-β₁)^(-2:ℝ) ≤ q^(53/1000:ℝ) := by
  have hstep : Cd * A^2 * Real.exp (2 * (Real.log q)^(3/4:ℝ)) * (1-β₁)^(-2:ℝ)
      ≤ q^(1/1000:ℝ) * q^(1/500:ℝ) * q^(1/50:ℝ) * (q^(1/50:ℝ) * (Real.log q)^4) := by
    gcongr <;> positivity
  calc Cd * A^2 * Real.exp (2 * (Real.log q)^(3/4:ℝ)) * (1-β₁)^(-2:ℝ)
      ≤ q^(1/1000:ℝ) * q^(1/500:ℝ) * q^(1/50:ℝ) * (q^(1/50:ℝ) * (Real.log q)^4) := hstep
    _ = (q^(1/1000:ℝ) * q^(1/500:ℝ) * q^(1/50:ℝ) * q^(1/50:ℝ)) * (Real.log q)^4 := by ring
    _ = q^(43/1000:ℝ) * (Real.log q)^4 := by
        rw [show q^(1/1000:ℝ) * q^(1/500:ℝ) * q^(1/50:ℝ) * q^(1/50:ℝ) = q^(43/1000:ℝ) from by
          rw [← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq]; norm_num]
    _ ≤ q^(43/1000:ℝ) * q^(1/100:ℝ) := mul_le_mul_of_nonneg_left hL4 (Real.rpow_nonneg hq.le _)
    _ = q^(53/1000:ℝ) := by rw [← Real.rpow_add hq]; norm_num

/-- `(log(2+A²q³))^24 * (1-β₁)^{-2} ≤ q^{3/100}`. -/
lemma repulsionSizesD24Bound {q A β₁ : ℝ} (hq : 0 < q) (hLp : 0 < Real.log q) (hδ : 0 < 1 - β₁)
    (hlog2A : Real.log (2 + A^2*q^3) ≤ 4 * Real.log q)
    (hmul28 : (Real.log q)^28 * (2:ℝ)^48 ≤ q^(1/100:ℝ))
    (hδ2 : (1-β₁)^(-2:ℝ) ≤ q^(1/50:ℝ) * (Real.log q)^4) :
    (Real.log (2 + A^2*q^3))^24 * (1-β₁)^(-2:ℝ) ≤ q^(3/100:ℝ) := by
  have h24 : (Real.log (2 + A^2*q^3))^24 ≤ (4 * Real.log q)^24 :=
    pow_le_pow_left₀ (Real.log_nonneg (by nlinarith [sq_nonneg A, pow_nonneg hq.le 3])) hlog2A 24
  calc (Real.log (2 + A^2*q^3))^24 * (1-β₁)^(-2:ℝ)
      ≤ (4 * Real.log q)^24 * (q^(1/50:ℝ) * (Real.log q)^4) :=
        mul_le_mul h24 hδ2 (by positivity) (by positivity)
    _ = (4:ℝ)^24 * (Real.log q)^28 * q^(1/50:ℝ) := by rw [mul_pow]; ring_nf
    _ ≤ q^(1/100:ℝ) * q^(1/50:ℝ) := by
        have h28 : (4:ℝ)^24 * (Real.log q)^28 ≤ q^(1/100:ℝ) := by
          rw [show (4:ℝ)^24 = (2:ℝ)^48 by norm_num, mul_comm]
          exact hmul28
        exact mul_le_mul_of_nonneg_right h28 (Real.rpow_nonneg hq.le _)
    _ = q^(3/100:ℝ) := by rw [← Real.rpow_add hq]; norm_num

/-- `Cd*A⁸*exp(8 L^{3/4})*(log(2+A²q³))^24*(1-β₁)^{-2} ≤ q^{119/1000}`. -/
lemma repulsionSizesNBound {q Cd A β₁ : ℝ} (hq : 0 < q) (hδ : 0 < 1 - β₁)
    (hCd_le : Cd ≤ q^(1/1000:ℝ)) (hA8_le : A^8 ≤ q^(1/125:ℝ))
    (hexp8 : Real.exp (8 * (Real.log q)^(3/4:ℝ)) ≤ q^(2/25:ℝ))
    (hd24 : (Real.log (2 + A^2*q^3))^24 * (1-β₁)^(-2:ℝ) ≤ q^(3/100:ℝ)) :
    Cd * A^8 * Real.exp (8 * (Real.log q)^(3/4:ℝ)) * (Real.log (2 + A^2*q^3))^24
        * (1-β₁)^(-2:ℝ) ≤ q^(119/1000:ℝ) := by
  have hstep : Cd * A^8 * Real.exp (8*(Real.log q)^(3/4:ℝ))
      ≤ q^(1/1000:ℝ) * q^(1/125:ℝ) * q^(2/25:ℝ) := by
    gcongr <;> positivity
  calc Cd * A^8 * Real.exp (8*(Real.log q)^(3/4:ℝ)) * (Real.log (2 + A^2*q^3))^24
        * (1-β₁)^(-2:ℝ)
      = (Cd * A^8 * Real.exp (8*(Real.log q)^(3/4:ℝ)))
          * ((Real.log (2 + A^2*q^3))^24 * (1-β₁)^(-2:ℝ)) := by ring
    _ ≤ (q^(1/1000:ℝ) * q^(1/125:ℝ) * q^(2/25:ℝ)) * q^(3/100:ℝ) :=
        mul_le_mul hstep hd24 (by positivity) (by positivity)
    _ = q^(119/1000:ℝ) := by
        rw [← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq]; norm_num


/-- **The size conditions of the BGTZ assembly** (sifting level `R` of (5.5), detection length `N`
of (5.6)): for `log q ≥ 10^8` and constants whose logarithms are dominated by `log q`, there are
integers `R, N` satisfying Proposition 5.1's two size hypotheses, the sieve-level condition
`log (2eR) ≤ log (2 + A²q³)`, `N ≥ 2`, `1 ≤ N(1-β₁)`, and the crucial upper bound
`log N ≤ log q · U` for `U = 11/5 + (11/10)log(5+|γ|)/log q`.

This is the (only) place where the counting of `(1-β₁)^{-2}` (via the Landau--Siegel bound
`B/(q^{1/100}(log q)²) < 1-β₁`) and of `q^{c·log q}` enters; the exponents match by
`8θ + 2ε ≤ 11/5` and `4θ ≤ 11/10` with `θ = 1/4 + 1/100`, `ε = 1/100`, and `T ≤ 5 + |γ|`. -/
theorem RepulsionSizes {q : ℕ} [NeZero q] {A B Cd cZ T β₁ γ : ℝ}
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hCd : 0 < Cd) (hcZ : 0 < cZ) (hT : 4 ≤ T)
    (hγT : |γ| ≤ T) (hTγ : T ≤ 5 + |γ|) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log q) < β₁)
    (hSiegel : B / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log q) ^ 2) < 1 - β₁)
    (hlogq : 100000000 ≤ Real.log q)
    (hlogA : Real.log A ≤ Real.log q / 1000) (hlogB : Real.log B ≤ Real.log q / 1000)
    (hlogCd : Real.log Cd ≤ Real.log q / 1000) :
    ∃ R N : ℕ, 200 ≤ R ∧ 2 ≤ N ∧ 1 ≤ (N : ℝ) * (1 - β₁) ∧
      Cd * A ^ 2 * (q : ℝ) ^ (2 * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) ∧
      Real.log (2 * Real.exp 1 * (R : ℝ)) ≤ Real.log (2 + A ^ 2 * (q : ℝ) ^ 3) ∧
      Cd * A ^ 8 * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ (8 * (1 / 4 + 1 / 100))
          * T ^ (4 * (1 / 4 + 1 / 100)) * (1 - β₁) ^ (-2 : ℝ) ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.log (q : ℝ)
          * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
  have h22 : (2:ℕ) * (1/4 + 1/100) = 0 := by norm_num
  have h88 : (8:ℕ) * (1/4 + 1/100) = 0 := by norm_num
  have h44 : (4:ℕ) * (1/4 + 1/100) = 0 := by norm_num
  simp only [h22, h88, h44, pow_zero, mul_one]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  have hx1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  have hXe : Real.exp 100000000 ≤ (q:ℝ) := (Real.le_log_iff_exp_le hxpos).mp hlogq
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA2ge1 : (1:ℝ) ≤ A^2 := by nlinarith [hA1]
  have hqcont : (1:ℝ) < (q:ℝ) := by
    have h1 : (1:ℝ) < Real.exp 100000000 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith [h1, hXe]
  have hsiege : 0 < 1 - β₁ ∧ (1-β₁)⁻¹ ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 :=
    repulsionSizesSiegelInv hB1 hqcont hSiegel
  have hδpos : 0 < 1 - β₁ := hsiege.1
  have hδinv : (1-β₁)⁻¹ ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 := hsiege.2
  have hδ2 : (1-β₁)^(-2:ℝ) ≤ (q:ℝ)^(1/50:ℝ) * (Real.log (q:ℝ))^4 := by
    have hsq : (1-β₁)^(-2:ℝ) = ((1-β₁)⁻¹)^2 := by
      have h1 : (-2:ℝ) = (-1) + (-1) := by norm_num
      rw [h1, Real.rpow_add hδpos, Real.rpow_neg_one]
      ring
    rw [hsq]
    have h1 : ((1-β₁)⁻¹)^2 ≤ ((q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2)^2 :=
      (by simpa only [pow_two] using mul_self_le_mul_self (inv_pos.mpr hδpos).le hδinv)
    have h2 : ((q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2)^2
        = (q:ℝ)^(1/50:ℝ) * (Real.log (q:ℝ))^4 := by
      have ha : ((q:ℝ)^(1/100:ℝ))^2 = (q:ℝ)^(1/50:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
      have hb : ((Real.log (q:ℝ))^2)^2 = (Real.log (q:ℝ))^4 := by
        rw [← pow_mul]
      rw [mul_pow, ha, hb]
    linarith [h1, h2]
  have hCd_le : Cd ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [show Cd = Real.exp (Real.log Cd) from (Real.exp_log hCd).symm, Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have hdiv : Real.log (q:ℝ) / 1000 = Real.log (q:ℝ) * (1/1000) := by ring
    linarith [hlogCd, hdiv]
  have hA_le : A ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [show A = Real.exp (Real.log A) from (Real.exp_log hA0).symm, Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have hdiv : Real.log (q:ℝ) / 1000 = Real.log (q:ℝ) * (1/1000) := by ring
    linarith [hlogA, hdiv]
  have hA2_le : A^2 ≤ (q:ℝ)^(1/500:ℝ) := by
    have h1 : A^2 ≤ ((q:ℝ)^(1/1000:ℝ))^2 := pow_le_pow_left₀ hA0.le hA_le 2
    have h2 : ((q:ℝ)^(1/1000:ℝ))^2 = (q:ℝ)^(1/500:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [h1, h2]
  have hA8_le : A^8 ≤ (q:ℝ)^(1/125:ℝ) := by
    have h1 : A^8 ≤ ((q:ℝ)^(1/1000:ℝ))^8 := pow_le_pow_left₀ hA0.le hA_le 8
    have h2 : ((q:ℝ)^(1/1000:ℝ))^8 = (q:ℝ)^(1/125:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [h1, h2]
  have hq4 : (4:ℝ) ≤ (q:ℝ) := by
    have h1 : (4:ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3:ℝ); linarith
    have h2 : Real.exp 3 ≤ Real.exp 100000000 := Real.exp_le_exp.mpr (by norm_num)
    linarith [h1, h2, hXe]
  have hlog2A : Real.log (2 + A^2 * (q:ℝ)^3) ≤ 4 * Real.log (q:ℝ) :=
    repulsionSizesLogTwoAddQ3Le hA1 hq4 hA_le
  have h100 : (100:ℝ) ≤ (Real.log (q:ℝ)) ^ (1/4:ℝ) := repulsionSizesHundredLeRpowQuarter hlogq
  have h34 : (Real.log (q:ℝ)) ^ (3/4:ℝ) ≤ Real.log (q:ℝ) / 100 :=
    repulsionSizesThreeQuartersLe hLpos h100
  have hexp2 : Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ)) ≤ (q:ℝ)^(1/50:ℝ) := by
    have h1 : 2 * (Real.log (q:ℝ))^(3/4:ℝ) ≤ Real.log (q:ℝ) * (1/50) := by
      have h2 : Real.log (q:ℝ) / 100 = Real.log (q:ℝ) * (1/100) := by ring
      linarith only [h34, h2]
    calc Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ))
        ≤ Real.exp (Real.log (q:ℝ) * (1/50)) := Real.exp_le_exp.mpr h1
      _ = (q:ℝ)^(1/50:ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hexp8 : Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ)) ≤ (q:ℝ)^(2/25:ℝ) := by
    have h1 : 8 * (Real.log (q:ℝ))^(3/4:ℝ) ≤ Real.log (q:ℝ) * (2/25) := by
      have h2 : 8 * (Real.log (q:ℝ) / 100) = Real.log (q:ℝ) * (2/25) := by ring
      linarith only [h34, h2]
    calc Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
        ≤ Real.exp (Real.log (q:ℝ) * (2/25)) := Real.exp_le_exp.mpr h1
      _ = (q:ℝ)^(2/25:ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hL4 : (Real.log (q:ℝ))^4 ≤ (q:ℝ)^(1/100:ℝ) := repulsionSizesLogPow4LeRpow hXe
  have hmul28 : (Real.log (q:ℝ))^28 * (2:ℝ)^48 ≤ (q:ℝ)^(1/100:ℝ) :=
    repulsionSizesLogPow28Le hXe
  have hd24 : (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (1-β₁)^(-2:ℝ) ≤ (q:ℝ)^(3/100:ℝ) :=
    repulsionSizesD24Bound hxpos hLpos hδpos hlog2A hmul28 hδ2
  set LR : ℝ := Cd * A^2 * Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ)) * (1-β₁)^(-2:ℝ) with hLRdef
  set LN : ℝ := Cd * A^8 * Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
      * (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (1-β₁)^(-2:ℝ) with hLNdef
  have hLR : LR ≤ (q:ℝ)^(53/1000:ℝ) := by
    rw [hLRdef]; exact repulsionSizesRBound hxpos hδpos hCd_le hA2_le hexp2 hδ2 hL4
  have hLN : LN ≤ (q:ℝ)^(119/1000:ℝ) := by
    rw [hLNdef]; exact repulsionSizesNBound hxpos hδpos hCd_le hA8_le hexp8 hd24
  have hq11 : (11:ℝ) ≤ (q:ℝ) := by
    have h1 : (11:ℝ) ≤ Real.exp 10 := by have := Real.add_one_le_exp (10:ℝ); linarith
    have h2 : Real.exp 10 ≤ Real.exp 100000000 := Real.exp_le_exp.mpr (by norm_num)
    linarith [h1, h2, hXe]
  have hq202 : (202:ℝ) ≤ (q:ℝ) := by
    have h1 : (202:ℝ) ≤ Real.exp 201 := by have := Real.add_one_le_exp (201:ℝ); linarith
    have h2 : Real.exp 201 ≤ Real.exp 100000000 := Real.exp_le_exp.mpr (by norm_num)
    linarith [h1, h2, hXe]
  have hq053 : (q:ℝ)^(53/1000:ℝ) ≤ (q:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (53/1000:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hexp4e : 4 * Real.exp 1 ≤ (q:ℝ)^2 := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith only [hq11, h1]
  have hsum2 : 202 + (q:ℝ)^(53/1000:ℝ) ≤ 2 * (q:ℝ) := by linarith [hq202, hq053]
  have hRlt : ((⌈max 200 LR⌉₊ : ℕ) : ℝ) < max 200 LR + 1 :=
    Nat.ceil_lt_add_one (le_trans (by norm_num : (0:ℝ) ≤ 200) (le_max_left 200 LR))
  have hLRnn : (0:ℝ) ≤ LR := by rw [hLRdef]; positivity
  have hLNnn : (0:ℝ) ≤ LN := by rw [hLNdef]; positivity
  have hRmax : max 200 LR ≤ 201 + (q:ℝ)^(53/1000:ℝ) := by
    have h1 : max 200 LR ≤ 200 + LR := max_le (by linarith) (by linarith)
    have h2 : (0:ℝ) ≤ (q:ℝ)^(53/1000:ℝ) := Real.rpow_nonneg hxpos.le _
    linarith [h1, hLR, h2]
  have hbound5 : 2 * Real.exp 1 * ((⌈max 200 LR⌉₊ : ℕ) : ℝ) ≤ 2 + A^2 * (q:ℝ)^3 := by
    have h2 : 2 * Real.exp 1 * ((⌈max 200 LR⌉₊ : ℕ) : ℝ)
        < 2 * Real.exp 1 * (202 + (q:ℝ)^(53/1000:ℝ)) := by
      have he : (0:ℝ) < 2 * Real.exp 1 := by positivity
      have hlt : ((⌈max 200 LR⌉₊ : ℕ) : ℝ) < 202 + (q:ℝ)^(53/1000:ℝ) := by
        linarith [hRlt, hRmax]
      exact mul_lt_mul_of_pos_left hlt he
    have h3 : 2 * Real.exp 1 * (202 + (q:ℝ)^(53/1000:ℝ)) ≤ 2 + A^2 * (q:ℝ)^3 := by
      have he1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
      have h4 : 2 * Real.exp 1 * (202 + (q:ℝ)^(53/1000:ℝ)) ≤ 4 * Real.exp 1 * (q:ℝ) := by
        have h := mul_le_mul_of_nonneg_left hsum2 (by positivity : (0:ℝ) ≤ 2 * Real.exp 1)
        linarith only [h]
      have h5 : 4 * Real.exp 1 * (q:ℝ) ≤ (q:ℝ)^3 := by
        calc 4 * Real.exp 1 * (q:ℝ) ≤ (q:ℝ)^2 * (q:ℝ) := mul_le_mul_of_nonneg_right hexp4e hxpos.le
          _ = (q:ℝ)^3 := by ring
      have h6 : (q:ℝ)^3 ≤ A^2 * (q:ℝ)^3 :=
        le_mul_of_one_le_left (pow_nonneg hxpos.le 3) hA2ge1
      linarith [h4, h5, h6]
    exact le_trans (le_of_lt h2) h3
  -- N upper bound
  have hδinv_le : (1-β₁)⁻¹ ≤ (q:ℝ)^(119/1000:ℝ) := by
    have hLs : (Real.log (q:ℝ))^2 ≤ (Real.log (q:ℝ))^4 := by
      have hL1 : (1:ℝ) ≤ Real.log (q:ℝ) := by linarith
      have h2 : (Real.log (q:ℝ))^2 * 1 ≤ (Real.log (q:ℝ))^2 * (Real.log (q:ℝ))^2 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hLpos.le 2)
        exact one_le_pow₀ hL1
      have h3 : (Real.log (q:ℝ))^2 * (Real.log (q:ℝ))^2 = (Real.log (q:ℝ))^4 := by ring
      linarith [h2, h3]
    have h1 : (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^4 :=
      mul_le_mul_of_nonneg_left hLs (Real.rpow_nonneg hxpos.le _)
    have h2 : (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^4 ≤ (q:ℝ)^(1/100:ℝ) * (q:ℝ)^(1/100:ℝ) :=
      mul_le_mul_of_nonneg_left hL4 (Real.rpow_nonneg hxpos.le _)
    have h3 : (q:ℝ)^(1/100:ℝ) * (q:ℝ)^(1/100:ℝ) = (q:ℝ)^(1/50:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h4 : (q:ℝ)^(1/50:ℝ) ≤ (q:ℝ)^(119/1000:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith [hδinv, h1, h2, h3, h4]
  have hq3th : (3:ℝ) ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [Real.rpow_def_of_pos hxpos]
    have h1 : (3:ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2:ℝ); linarith
    have h2 : Real.exp 2 ≤ Real.exp (Real.log (q:ℝ) * (1/1000)) := by
      apply Real.exp_le_exp.mpr; linarith only [hlogq]
    linarith [h1, h2]
  have hNlt : ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) < max (max 2 LN) ((1-β₁)⁻¹) + 1 :=
    Nat.ceil_lt_add_one (le_trans (le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_left 2 LN))
      (le_max_left _ _))
  have hmaxle : max (max 2 LN) ((1-β₁)⁻¹) ≤ LN + (1-β₁)⁻¹ + 2 := by
    have hdnn : (0:ℝ) ≤ (1-β₁)⁻¹ := inv_nonneg.mpr hδpos.le
    refine max_le (max_le ?_ ?_) ?_
    · linarith
    · linarith
    · linarith
  have hNub : ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) ≤ (q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ) := by
    have e1 : (3:ℝ) ≤ (q:ℝ)^(119/1000:ℝ) :=
      le_trans hq3th (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
    have hsum : LN + (1-β₁)⁻¹ + 3 ≤ 3 * (q:ℝ)^(119/1000:ℝ) := by linarith [hLN, hδinv_le, e1]
    have h3q : 3 * (q:ℝ)^(119/1000:ℝ) ≤ (q:ℝ)^(1/1000:ℝ) * (q:ℝ)^(119/1000:ℝ) :=
      mul_le_mul_of_nonneg_right hq3th (Real.rpow_nonneg hxpos.le _)
    have h12 : (q:ℝ)^(1/1000:ℝ) * (q:ℝ)^(119/1000:ℝ) = (q:ℝ)^(12/100:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h12' : (q:ℝ)^(12/100:ℝ) ≤ (q:ℝ)^(11/5:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h5g1 : (1:ℝ) ≤ 5 + |γ| := by have := abs_nonneg γ; linarith
    have h5 : (1:ℝ) ≤ (5+|γ|)^(11/10:ℝ) := Real.one_le_rpow h5g1 (by norm_num)
    have hfin : (q:ℝ)^(12/100:ℝ) * 1 ≤ (q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ) :=
      mul_le_mul h12' h5 (by norm_num) (Real.rpow_nonneg hxpos.le _)
    have hstrict : ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ)
        < (q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ) := by
      calc ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ)
          < max (max 2 LN) ((1-β₁)⁻¹) + 1 := hNlt
        _ ≤ LN + (1-β₁)⁻¹ + 3 := by linarith [hmaxle]
        _ ≤ 3 * (q:ℝ)^(119/1000:ℝ) := hsum
        _ ≤ (q:ℝ)^(1/1000:ℝ) * (q:ℝ)^(119/1000:ℝ) := h3q
        _ = (q:ℝ)^(12/100:ℝ) := h12
        _ = (q:ℝ)^(12/100:ℝ) * 1 := by ring
        _ ≤ (q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ) := hfin
    exact le_of_lt hstrict
  refine ⟨⌈max 200 LR⌉₊, ⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (200:ℝ) ≤ max 200 LR := le_max_left _ _
    have h3 : (200:ℝ) ≤ ((⌈max 200 LR⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h3
  · have h1 : (2:ℝ) ≤ max (max 2 LN) ((1-β₁)⁻¹) := le_trans (le_max_left _ _) (le_max_left _ _)
    have h3 : (2:ℝ) ≤ ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h3
  · have hNge : (1-β₁)⁻¹ ≤ ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) :=
      le_trans (le_max_right _ _) (Nat.le_ceil _)
    have hmul := mul_le_mul_of_nonneg_right hNge hδpos.le
    have hone : (1-β₁)⁻¹ * (1-β₁) = 1 := inv_mul_cancel₀ hδpos.ne'
    linarith [hmul, hone]
  · exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  · exact Real.log_le_log (by positivity) hbound5
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_ceil _)
  · have hlogN : Real.log (((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ))
        ≤ Real.log ((q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ)) := Real.log_le_log (by positivity) hNub
    have hval : Real.log ((q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ))
        = Real.log (q:ℝ) * (11/5 + (11/10) * (Real.log (5+|γ|) / Real.log (q:ℝ))) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hxpos,
        Real.log_rpow (by linarith : (0:ℝ) < 5 + |γ|)]
      field_simp
    linarith [hlogN, hval]


end Work.LinnikAreas.BGTZ
