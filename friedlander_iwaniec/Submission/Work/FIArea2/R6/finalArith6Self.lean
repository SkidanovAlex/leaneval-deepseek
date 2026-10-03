import Mathlib

namespace Work.FIArea2.R6

/-- Pure ring identity combining the three bracket terms over a common power factor.
Stated with all-`variable` arguments so that `ring` never tries to expand a concrete
large power such as `(log K + 2)^262144`. -/
private lemma arith_combine (p u Cd M a b : ℝ) :
    p * u ^ 2 * (Cd * M) + 80 * u * (Cd * a * M) + Cd * b * M
      = Cd * M * (p * u ^ 2 + 80 * u * a + b) := by
  ring

/-- Pure ring identity for the very last rearrangement (again all variables). -/
private lemma reorder6 (p u Cd P4 L : ℝ) :
    65536 * 65536 * (Cd * (P4 * L) * ((p + 656) * u ^ 2))
      = (65536 * 65536 * (p + 656) * P4) * (Cd * u ^ 2 * L) := by
  ring

/-- `K₀·X ≤ (K₀+1)·X` for `X ≥ 0`. -/
private lemma le_succ_mul (K0 Cd u L : ℝ) (hX : 0 ≤ Cd * u ^ 2 * L) :
    K0 * (Cd * u ^ 2 * L) ≤ (K0 + 1) * Cd * u ^ 2 * L := by
  nlinarith [hX]

/-- The polynomial (`K`-) bound `π u² + 80 u √K·K + K² ≤ (π + 656)·u²`, valid under
`u ≥ 0`, `K√K ≤ 8u` and `K² ≤ 16u²`.  All hypotheses are plain real inequalities, so
`nlinarith` works on a clean context. -/
private lemma poly_bound (u K : ℝ) (hu : 0 ≤ u)
    (hKs : K * Real.sqrt K ≤ 8 * u) (hK2 : K * K ≤ 16 * u ^ 2) :
    Real.pi * u ^ 2 + 80 * u * (Real.sqrt K * K) + K * K ≤ (Real.pi + 656) * u ^ 2 := by
  have hKsqrt : Real.sqrt K * K ≤ 8 * u := by
    rw [mul_comm (Real.sqrt K) K]; exact hKs
  have h80 : 80 * u * (Real.sqrt K * K) ≤ 640 * u ^ 2 := by
    have hm : u * (Real.sqrt K * K) ≤ u * (8 * u) := mul_le_mul_of_nonneg_left hKsqrt hu
    have h1 : 80 * (u * (Real.sqrt K * K)) ≤ 80 * (u * (8 * u)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    nlinarith [h1]
  nlinarith [h80, hK2]

/-- **The final arithmetic of the round-6 pair bracket.**  If `u = θ√N ≥ N^{3/8} ≈ 1 ÷`,
`K ≥ 1` with `K√K ≤ 8u`, `K² ≤ 16u²`, `log K + 2 ≤ 4(log N + 2)`, and nonnegative `S₁, S₂, S₃`
satisfy `S₁ ≤ Cd·(log K + 2)^{2^18}`, `S₂ ≤ Cd·(√K·K)(log K + 2)^{2^18}`,
`S₃ ≤ Cd·(K·K)(log K + 2)^{2^18}` for some `Cd > 0`, then

  `2¹⁶·2¹⁶·(π u² S₁ + 80 u S₂ + S₃) ≤ C·Cd·u²·(log N + 2)^{2^18}`

with an absolute `C` (take `C = 65536²(π + 656)4^{2^18} + 1`). -/
theorem finalArith6Self :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ N u K S1 S2 S3 Cd : ℝ),
      0 < θ → θ ≤ 1 → 1 ≤ N → u = θ * Real.sqrt N → N ^ ((3 : ℝ) / 8) ≤ u →
      1 ≤ K → 0 < Cd → 0 ≤ S1 → 0 ≤ S2 → 0 ≤ S3 →
      Real.log K + 2 ≤ 4 * (Real.log N + 2) →
      K * Real.sqrt K ≤ 8 * u → K * K ≤ 16 * u ^ (2 : ℕ) →
      S1 ≤ Cd * (Real.log K + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) →
      S2 ≤ Cd * (Real.sqrt K * K) * (Real.log K + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) →
      S3 ≤ Cd * (K * K) * (Real.log K + 2) ^ ((2 : ℕ) ^ (18 : ℕ)) →
      65536 * (65536 * (Real.pi * u ^ (2 : ℕ) * S1 + 80 * u * S2 + S3))
        ≤ C * Cd * u ^ (2 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ) := by
  refine ⟨65536 * 65536 * (Real.pi + 656) * (4 : ℝ) ^ (262144 : ℕ) + 1, ?_, ?_⟩
  · have hP4 : (0 : ℝ) < (4 : ℝ) ^ (262144 : ℕ) := pow_pos (by norm_num) 262144
    have hp : (0 : ℝ) < Real.pi + 656 := add_pos Real.pi_pos (by norm_num)
    have hprod : (0 : ℝ) < 65536 * 65536 * (Real.pi + 656) * (4 : ℝ) ^ (262144 : ℕ) :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 65536)
        (by norm_num : (0 : ℝ) < 65536)) hp) hP4
    exact add_pos hprod zero_lt_one
  · intro θ N u K S1 S2 S3 Cd hθ hθ1 hN hu hN38u hK1 hCd hS1nn hS2nn hS3nn
      hlog hKsqrtK hKsq hS1 hS2 hS3
    rw [show (2 : ℕ) ^ (18 : ℕ) = 262144 by norm_num] at hS1 hS2 hS3
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
    have hCdnn : 0 ≤ Cd := le_of_lt hCd
    have hunn : 0 ≤ u :=
      le_trans (Real.rpow_nonneg (le_of_lt hNpos) ((3 : ℝ) / 8)) hN38u
    have hu2nn : 0 ≤ u ^ (2 : ℕ) := sq_nonneg u
    have hKnn : 0 ≤ K := le_trans zero_le_one hK1
    have hLnn : 0 ≤ Real.log N + 2 := add_nonneg (Real.log_nonneg hN) (by norm_num)
    have hMnn : 0 ≤ Real.log K + 2 := add_nonneg (Real.log_nonneg hK1) (by norm_num)
    have h4pownn : 0 ≤ (4 : ℝ) ^ (262144 : ℕ) := pow_nonneg (by norm_num) 262144
    have hLpownn : 0 ≤ (Real.log N + 2) ^ (262144 : ℕ) := pow_nonneg hLnn 262144
    -- the logarithm-power bound `M ≤ 4^n · L`
    have hpowM : (Real.log K + 2) ^ (262144 : ℕ)
        ≤ (4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ) := by
      have h := pow_le_pow_left₀ hMnn hlog 262144
      calc (Real.log K + 2) ^ (262144 : ℕ) ≤ (4 * (Real.log N + 2)) ^ (262144 : ℕ) := h
        _ = (4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ) := by rw [mul_pow]
    -- the polynomial (`K`-) bound
    have hpoly : Real.pi * u ^ (2 : ℕ) + 80 * u * (Real.sqrt K * K) + K * K
        ≤ (Real.pi + 656) * u ^ (2 : ℕ) := poly_bound u K hunn hKsqrtK hKsq
    have hsKnn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    -- term-by-term bounds from the `Sᵢ` hypotheses
    have hS1' : Real.pi * u ^ (2 : ℕ) * S1
        ≤ Real.pi * u ^ (2 : ℕ) * (Cd * (Real.log K + 2) ^ (262144 : ℕ)) :=
      mul_le_mul_of_nonneg_left hS1 (mul_nonneg (le_of_lt Real.pi_pos) hu2nn)
    have hS2' : 80 * u * S2
        ≤ 80 * u * (Cd * (Real.sqrt K * K) * (Real.log K + 2) ^ (262144 : ℕ)) :=
      mul_le_mul_of_nonneg_left hS2 (mul_nonneg (by norm_num) hunn)
    have hsum : Real.pi * u ^ (2 : ℕ) * S1 + 80 * u * S2 + S3
        ≤ Real.pi * u ^ (2 : ℕ) * (Cd * (Real.log K + 2) ^ (262144 : ℕ))
          + 80 * u * (Cd * (Real.sqrt K * K) * (Real.log K + 2) ^ (262144 : ℕ))
          + Cd * (K * K) * (Real.log K + 2) ^ (262144 : ℕ) :=
      add_le_add (add_le_add hS1' hS2') hS3
    have hcomb :=
      arith_combine Real.pi u Cd ((Real.log K + 2) ^ (262144 : ℕ)) (Real.sqrt K * K) (K * K)
    have hPnn : 0 ≤ Real.pi * u ^ (2 : ℕ) + 80 * u * (Real.sqrt K * K) + K * K :=
      add_nonneg
        (add_nonneg (mul_nonneg (le_of_lt Real.pi_pos) hu2nn)
          (mul_nonneg (mul_nonneg (by norm_num) hunn) (mul_nonneg hsKnn hKnn)))
        (mul_nonneg hKnn hKnn)
    have hBnn : 0 ≤ Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ)) :=
      mul_nonneg hCdnn (mul_nonneg h4pownn hLpownn)
    have hA : Cd * (Real.log K + 2) ^ (262144 : ℕ)
        ≤ Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpowM hCdnn
    have hAP : (Cd * (Real.log K + 2) ^ (262144 : ℕ))
            * (Real.pi * u ^ (2 : ℕ) + 80 * u * (Real.sqrt K * K) + K * K)
        ≤ (Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ)))
            * (Real.pi * u ^ (2 : ℕ) + 80 * u * (Real.sqrt K * K) + K * K) :=
      mul_le_mul_of_nonneg_right hA hPnn
    have hPQ : (Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ)))
            * (Real.pi * u ^ (2 : ℕ) + 80 * u * (Real.sqrt K * K) + K * K)
        ≤ (Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ)))
            * ((Real.pi + 656) * u ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpoly hBnn
    have hSle : Real.pi * u ^ (2 : ℕ) * S1 + 80 * u * S2 + S3
        ≤ Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ))
            * ((Real.pi + 656) * u ^ (2 : ℕ)) :=
      le_trans hsum (le_trans (le_of_eq hcomb) (le_trans hAP hPQ))
    have hgoal1 : 65536 * (65536 * (Real.pi * u ^ (2 : ℕ) * S1 + 80 * u * S2 + S3))
        ≤ 65536 * 65536 * (Cd * ((4 : ℝ) ^ (262144 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ))
            * ((Real.pi + 656) * u ^ (2 : ℕ))) := by
      have h := mul_le_mul_of_nonneg_left hSle (by norm_num : (0 : ℝ) ≤ 65536 * 65536)
      simpa only [mul_assoc] using h
    have hXnn : 0 ≤ Cd * u ^ (2 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ) :=
      mul_nonneg (mul_nonneg hCdnn hu2nn) hLpownn
    have hgoal2 : 65536 * 65536 * (Cd * ((4 : ℝ) ^ (262144 : ℕ)
            * (Real.log N + 2) ^ (262144 : ℕ)) * ((Real.pi + 656) * u ^ (2 : ℕ)))
        ≤ (65536 * 65536 * (Real.pi + 656) * (4 : ℝ) ^ (262144 : ℕ) + 1)
            * Cd * u ^ (2 : ℕ) * (Real.log N + 2) ^ (262144 : ℕ) := by
      rw [reorder6 Real.pi u Cd ((4 : ℝ) ^ (262144 : ℕ)) ((Real.log N + 2) ^ (262144 : ℕ))]
      exact le_succ_mul (65536 * 65536 * (Real.pi + 656) * (4 : ℝ) ^ (262144 : ℕ)) Cd u
        ((Real.log N + 2) ^ (262144 : ℕ)) hXnn
    exact le_trans hgoal1 hgoal2

end Work.FIArea2.R6
