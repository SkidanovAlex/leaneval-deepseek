import Mathlib

namespace Work.GM.Energy.EnergyCore2

set_option maxHeartbeats 1000000

/-- Pure real arithmetic in the assembly of GM Proposition 11.1: the `E`-free part of the bound.
With `K = Θ·N^{1/mm}`, `Λ = N^{12/mm+4ε}` and `Λ ≤ N^δ` (`N ≥ 100`, `mm ≥ 2`, `ε,δ > 0`,
`Θ ≥ 1`, `V ≥ 1`, `κ ≥ 0`, `T ≥ 1`), the `E`-free remainder is dominated by
`(a1+1)(g1+1)(l1+1)(Θ+1)^6 N^δ (κ^{21/8} T^{1/4} N / V^2 + κ^3 N / V^2)`. -/
theorem arith_B {N : ℕ} {mm : ℕ} {ε δ V κ T Λ Θ a1 g1 l1 K : ℝ}
    (hN : 100 ≤ N) (hmm : 2 ≤ mm) (hε : 0 < ε) (hδ : 0 < δ)
    (hV : 1 ≤ V) (hκ : 0 ≤ κ) (hT : 1 ≤ T)
    (ha1 : 0 ≤ a1) (hg1 : 0 ≤ g1) (hl1 : 0 ≤ l1) (hΘ : 1 ≤ Θ)
    (hK : K = Θ * (N : ℝ) ^ (1 / (mm : ℝ)))
    (hΛ : Λ = (N : ℝ) ^ ((12 : ℝ) / (mm : ℝ) + 4 * ε)) (hΛle : Λ ≤ (N : ℝ) ^ δ) :
    2 * (2 * (a1 * (K + 1) ^ 2 / V ^ 2) *
        (g1 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ 3 / K ^ (3 * (mm : ℝ)) +
          l1 * (N : ℝ) ^ (2 * ε) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8))))
      ≤ 512 * (a1 + 1) * (g1 + 1) * (l1 + 1) * (Θ + 1) ^ 6 * (N : ℝ) ^ δ *
          (κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2 + κ ^ 3 * (N : ℝ) / V ^ 2) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hN100 : (100:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNgt1 : (1:ℝ) < (N:ℝ) := by linarith
  have hmmR : (0:ℝ) < (mm:ℝ) := by exact_mod_cast (by omega : 0 < mm)
  have hmm2R : (2:ℝ) ≤ (mm:ℝ) := by exact_mod_cast hmm
  have hVpos : (0:ℝ) < V := by linarith
  have hV2pos : (0:ℝ) < V^2 := by positivity
  -- the exponent inequality `12/mm + 4ε ≤ δ` extracted from `Λ ≤ N^δ`
  have hexp : (12:ℝ)/(mm:ℝ) + 4*ε ≤ δ := by
    have h := hΛle
    rw [hΛ] at h
    exact (Real.rpow_le_rpow_left_iff hNgt1).mp h
  have h2mm_le : (2:ℝ)/(mm:ℝ) ≤ 1 := by rw [div_le_one hmmR]; exact hmm2R
  have h2mm12 : (2:ℝ)/(mm:ℝ) ≤ (12:ℝ)/(mm:ℝ) := by
    rw [div_le_div_iff_of_pos_right hmmR]; norm_num
  have h12nn : (0:ℝ) ≤ (12:ℝ)/(mm:ℝ) := by positivity
  have h1mmnn : (0:ℝ) ≤ 1/(mm:ℝ) := by positivity
  have hεδ : ε ≤ δ := by linarith [hexp, h12nn, hε]
  have h2εδ : 2*ε ≤ δ := by linarith [hexp, h12nn, hε]
  have hsym1 : (2:ℝ)/(mm:ℝ) + ε ≤ 1 + δ := by nlinarith [hexp, h1mmnn, h2mm12, hε]
  have hsym2 : (2:ℝ)/(mm:ℝ) + 2*ε ≤ δ := by nlinarith [hexp, h1mmnn, h2mm12, hε]
  -- monotonicity of the real power with base `N ≥ 1`
  have hpow_2mm : (N:ℝ)^(2/(mm:ℝ)) ≤ (N:ℝ) := by
    calc (N:ℝ)^(2/(mm:ℝ)) ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h2mm_le
      _ = (N:ℝ) := Real.rpow_one _
  have hpow_εδ : (N:ℝ)^ε ≤ (N:ℝ)^δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
  have hpow_2εδ : (N:ℝ)^(2*ε) ≤ (N:ℝ)^δ := Real.rpow_le_rpow_of_exponent_le hN1 h2εδ
  have hsum2 : (N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^(2*ε) ≤ (N:ℝ)^δ := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hsym2
  have hpow_1δ : (N:ℝ)^δ * (N:ℝ) = (N:ℝ)^(1+δ) := by
    rw [Real.rpow_add hNpos (1:ℝ) δ, Real.rpow_one]; ring
  -- the locality parameter `K`
  have hqle : (N:ℝ)^(1/(mm:ℝ)) ≤ K := by
    rw [hK]; exact le_mul_of_one_le_left (Real.rpow_nonneg (le_of_lt hNpos) _) hΘ
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hqle
  have hKnn : (0:ℝ) ≤ K := le_of_lt hKpos
  have hKpow : (N:ℝ)^3 ≤ K^(3*(mm:ℝ)) := by
    have hqe : ((N:ℝ)^(1/(mm:ℝ)))^(3*(mm:ℝ)) = (N:ℝ)^(3:ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]; congr 1; field_simp
    calc (N:ℝ)^3 = (N:ℝ)^(3:ℝ) := (Real.rpow_natCast (N:ℝ) 3).symm
      _ = ((N:ℝ)^(1/(mm:ℝ)))^(3*(mm:ℝ)) := hqe.symm
      _ ≤ K^(3*(mm:ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hNpos) _) hqle (by positivity)
  have hKsq : (K+1)^2 ≤ (Θ+1)^2 * (N:ℝ)^(2/(mm:ℝ)) := by
    have hK1 : K + 1 ≤ (Θ+1) * (N:ℝ)^(1/(mm:ℝ)) := by
      rw [hK]
      have : (1:ℝ) ≤ (N:ℝ)^(1/(mm:ℝ)) := Real.one_le_rpow hN1 (by positivity)
      nlinarith [hΘ]
    have hq : ((N:ℝ)^(1/(mm:ℝ)))^2 = (N:ℝ)^(2/(mm:ℝ)) := by
      rw [pow_two, ← Real.rpow_add hNpos]; congr 1; ring
    calc (K+1)^2 ≤ ((Θ+1)*(N:ℝ)^(1/(mm:ℝ)))^2 := pow_le_pow_left₀ (by linarith) hK1 2
      _ = (Θ+1)^2 * ((N:ℝ)^(1/(mm:ℝ)))^2 := by ring
      _ = (Θ+1)^2 * (N:ℝ)^(2/(mm:ℝ)) := by rw [hq]
  have hn2K : (N:ℝ)^2/K^(3*(mm:ℝ)) ≤ 1/(N:ℝ) := by
    have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ (N:ℝ)^2 by positivity)
        (show (0:ℝ) < (N:ℝ)^3 by positivity) hKpow
    have h23 : (N:ℝ)^2 / (N:ℝ)^3 = 1/(N:ℝ) := by field_simp
    rwa [h23] at h
  -- elementary scalar comparisons
  have hΘp : (Θ+1)^2 ≤ (Θ+1)^6 := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ Θ+1) (by norm_num)
  have hscalar1 : a1*g1*(Θ+1)^2 ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ) := by
    have h1 : a1*g1 ≤ (a1+1)*(g1+1) := by nlinarith [ha1, hg1]
    have h2 : (Θ+1)^2 ≤ (l1+1)*(Θ+1)^6*(N:ℝ) := by
      have hA : (Θ+1)^6 ≤ (l1+1)*(Θ+1)^6 := le_mul_of_one_le_left (by positivity) (by linarith)
      have hB : (l1+1)*(Θ+1)^6 ≤ (l1+1)*(Θ+1)^6*(N:ℝ) :=
        le_mul_of_one_le_right (by positivity) hN1
      exact le_trans hΘp (le_trans hA hB)
    calc a1*g1*(Θ+1)^2 ≤ ((a1+1)*(g1+1))*(Θ+1)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ((a1+1)*(g1+1))*((l1+1)*(Θ+1)^6*(N:ℝ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ) := by ring
  have hscalar2 : a1*l1*(Θ+1)^2 ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6 := by
    have h1 : a1*l1 ≤ (a1+1)*(l1+1) := by nlinarith [ha1, hl1]
    have h2 : (Θ+1)^2 ≤ (g1+1)*(Θ+1)^6 := by
      exact le_trans hΘp (le_mul_of_one_le_left (by positivity) (by linarith))
    calc a1*l1*(Θ+1)^2 ≤ ((a1+1)*(l1+1))*(Θ+1)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ((a1+1)*(l1+1))*((g1+1)*(Θ+1)^6) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6 := by ring
  -- the three "inner" bounds, in each case a power of `N` is absorbed into `N^δ`
  have hinner1 : (K+1)^2 * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ)) ≤ (Θ+1)^2 * (N:ℝ)^δ := by
    have ha : (K+1)^2 * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ))
        ≤ ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKsq (by positivity)) (by positivity)
    have hb : ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ)) ≤ (Θ+1)^2*(N:ℝ)^δ := by
      have heq : ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ))
          = (Θ+1)^2 * ((N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^ε * ((N:ℝ)^2/K^(3*(mm:ℝ)))) := by ring
      rw [heq]
      have h1 : (N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^ε * ((N:ℝ)^2/K^(3*(mm:ℝ))) ≤ (N:ℝ)^ε := by
        have hstep : (N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^ε * ((N:ℝ)^2/K^(3*(mm:ℝ))) ≤ (N:ℝ) * (N:ℝ)^ε * (1/(N:ℝ)) :=
          mul_le_mul (mul_le_mul hpow_2mm le_rfl (by positivity) (by positivity)) hn2K (by positivity) (by positivity)
        have h1b : (N:ℝ) * (N:ℝ)^ε * (1/(N:ℝ)) = (N:ℝ)^ε := by
          rw [mul_right_comm, mul_one_div, div_self (ne_of_gt hNpos), one_mul]
        rw [h1b] at hstep
        exact hstep
      calc (Θ+1)^2 * ((N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^ε * ((N:ℝ)^2/K^(3*(mm:ℝ))))
          ≤ (Θ+1)^2 * (N:ℝ)^ε := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (Θ+1)^2 * (N:ℝ)^δ := mul_le_mul_of_nonneg_left hpow_εδ (by positivity)
    exact le_trans ha hb
  have hinner2 : (K+1)^2 * (N:ℝ)^(2*ε) * (N:ℝ) ≤ (Θ+1)^2 * (N:ℝ)^(1+δ) := by
    have ha : (K+1)^2 * (N:ℝ)^(2*ε) * (N:ℝ) ≤ ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^(2*ε) * (N:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKsq (by positivity)) (by positivity)
    have hb : ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^(2*ε) * (N:ℝ) ≤ (Θ+1)^2 * (N:ℝ)^(1+δ) := by
      have heq : ((Θ+1)^2*(N:ℝ)^(2/(mm:ℝ))) * (N:ℝ)^(2*ε) * (N:ℝ)
          = (Θ+1)^2 * ((N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^(2*ε) * (N:ℝ)) := by ring
      rw [heq]
      calc (Θ+1)^2 * ((N:ℝ)^(2/(mm:ℝ)) * (N:ℝ)^(2*ε) * (N:ℝ))
          ≤ (Θ+1)^2 * ((N:ℝ)^δ * (N:ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum2 (by positivity)) (by positivity)
        _ = (Θ+1)^2 * (N:ℝ)^(1+δ) := by rw [hpow_1δ]
    exact le_trans ha hb
  -- the three product bounds
  have hP1 : (a1*(K+1)^2/V^2) * (g1*(N:ℝ)^ε*(N:ℝ)^2*κ^3/K^(3*(mm:ℝ)))
      ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by
    have hfact : (a1*(K+1)^2/V^2) * (g1*(N:ℝ)^ε*(N:ℝ)^2*κ^3/K^(3*(mm:ℝ)))
        = (a1*g1*κ^3/V^2) * ((K+1)^2 * (N:ℝ)^ε * (N:ℝ)^2 / K^(3*(mm:ℝ))) := by ring
    rw [hfact]
    have htail : (a1*g1*κ^3/V^2) * ((Θ+1)^2*(N:ℝ)^δ)
        ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by
      calc (a1*g1*κ^3/V^2) * ((Θ+1)^2*(N:ℝ)^δ)
          = (a1*g1*(Θ+1)^2) * ((N:ℝ)^δ*κ^3/V^2) := by ring
        _ ≤ ((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)) * ((N:ℝ)^δ*κ^3/V^2) :=
            mul_le_mul_of_nonneg_right hscalar1 (by positivity)
        _ = (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hinner1 (by positivity)) htail
  have hP2 : (a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*κ^3))
      ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by
    have hfact : (a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*κ^3))
        = (a1*l1*κ^3/V^2) * ((K+1)^2 * (N:ℝ)^(2*ε) * (N:ℝ)) := by ring
    rw [hfact]
    have htail : (a1*l1*κ^3/V^2) * ((Θ+1)^2*(N:ℝ)^(1+δ))
        ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by
      calc (a1*l1*κ^3/V^2) * ((Θ+1)^2*(N:ℝ)^(1+δ))
          = (a1*l1*(Θ+1)^2) * ((N:ℝ)^(1+δ)*κ^3/V^2) := by ring
        _ ≤ ((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6) * ((N:ℝ)^(1+δ)*κ^3/V^2) :=
            mul_le_mul_of_nonneg_right hscalar2 (by positivity)
        _ = (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2) := by
            rw [← hpow_1δ]; ring
    exact le_trans (mul_le_mul_of_nonneg_left hinner2 (by positivity)) htail
  have hP3 : (a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8)))
      ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2) := by
    have hfact : (a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8)))
        = (a1*l1*T^((1:ℝ)/4)*κ^((21:ℝ)/8)/V^2) * ((K+1)^2 * (N:ℝ)^(2*ε) * (N:ℝ)) := by ring
    rw [hfact]
    have htail : (a1*l1*T^((1:ℝ)/4)*κ^((21:ℝ)/8)/V^2) * ((Θ+1)^2*(N:ℝ)^(1+δ))
        ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2) := by
      calc (a1*l1*T^((1:ℝ)/4)*κ^((21:ℝ)/8)/V^2) * ((Θ+1)^2*(N:ℝ)^(1+δ))
          = (a1*l1*(Θ+1)^2) * ((N:ℝ)^(1+δ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8)/V^2) := by ring
        _ ≤ ((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6) * ((N:ℝ)^(1+δ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8)/V^2) :=
            mul_le_mul_of_nonneg_right hscalar2 (by positivity)
        _ = (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2) := by
            rw [← hpow_1δ]; ring
    exact le_trans (mul_le_mul_of_nonneg_left hinner2 (by positivity)) htail
  -- final assembly
  have hsplit : 2 * (2 * (a1*(K+1)^2/V^2) *
        (g1*(N:ℝ)^ε*(N:ℝ)^2*κ^3/K^(3*(mm:ℝ)) + l1*(N:ℝ)^(2*ε)*((N:ℝ)*κ^3 + (N:ℝ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8))))
      = 4*((a1*(K+1)^2/V^2) * (g1*(N:ℝ)^ε*(N:ℝ)^2*κ^3/K^(3*(mm:ℝ))))
      + 4*((a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*κ^3)))
      + 4*((a1*(K+1)^2/V^2) * (l1*(N:ℝ)^(2*ε)*((N:ℝ)*T^((1:ℝ)/4)*κ^((21:ℝ)/8)))) := by ring
  have hb1 := mul_le_mul_of_nonneg_left hP1 (by norm_num : (0:ℝ) ≤ 4)
  have hb2 := mul_le_mul_of_nonneg_left hP2 (by norm_num : (0:ℝ) ≤ 4)
  have hb3 := mul_le_mul_of_nonneg_left hP3 (by norm_num : (0:ℝ) ≤ 4)
  have hfinal : 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2))
      + 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2))
      + 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2))
      ≤ 512 * (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*
          (κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2 + κ^3*(N:ℝ)/V^2) := by
    have hXnn : (0:ℝ) ≤ (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ := by positivity
    have hYnn : (0:ℝ) ≤ κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2 := by positivity
    have hZnn : (0:ℝ) ≤ κ^3*(N:ℝ)/V^2 := by positivity
    have hlin : 4*(2*(κ^3*(N:ℝ)/V^2) + κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2)
        ≤ 512*((κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2) + (κ^3*(N:ℝ)/V^2)) := by linarith
    calc 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2))
        + 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^3*(N:ℝ)/V^2))
        + 4*((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*(κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2))
        = ((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ)
          * (4*(2*(κ^3*(N:ℝ)/V^2) + κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2)) := by ring
      _ ≤ ((a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ)
          * (512*((κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2) + (κ^3*(N:ℝ)/V^2))) :=
            mul_le_mul_of_nonneg_left hlin hXnn
      _ = 512 * (a1+1)*(g1+1)*(l1+1)*(Θ+1)^6*(N:ℝ)^δ*
          (κ^((21:ℝ)/8)*T^((1:ℝ)/4)*(N:ℝ)/V^2 + κ^3*(N:ℝ)/V^2) := by ring
  rw [hsplit]
  linarith [hb1, hb2, hb3, hfinal]

end Work.GM.Energy.EnergyCore2
