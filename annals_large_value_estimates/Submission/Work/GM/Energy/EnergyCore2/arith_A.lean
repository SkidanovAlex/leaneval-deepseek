import Mathlib

namespace Work.GM.Energy.EnergyCore2

set_option maxHeartbeats 800000

/-- `(x ^ a) ^ n = x ^ (a * n)` for a real exponent `a`, a natural exponent `n` and `x ≥ 0`. -/
private lemma rpow_pow_nat (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * (n : ℝ)) := by
  have h1 : (x ^ a) ^ n = (x ^ a) ^ ((n : ℝ)) := (Real.rpow_natCast _ _).symm
  rw [h1, ← Real.rpow_mul hx]

/-- Pure real arithmetic in the assembly of GM Proposition 11.1: the `√E` part of the bound.
With `K = Θ·N^{1/mm}`, `Λ = N^{12/mm+4ε}` and `Λ ≤ N^δ` (`N ≥ 100`, `mm ≥ 2`, `ε,δ > 0`,
`Θ ≥ 1`, `V ≥ 1`, `κ ≥ 0`), the square of the coefficient of `√E(W)` is dominated by
`(a1+1)²(g1+1)²(l1+1)²(Θ+1)^{12} N^δ κ N^4/V^4`. -/
theorem arith_A {N : ℕ} {mm : ℕ} {ε δ V κ Λ Θ a1 g1 l1 K : ℝ}
    (hN : 100 ≤ N) (hmm : 2 ≤ mm) (hε : 0 < ε) (hδ : 0 < δ)
    (hV : 1 ≤ V) (hκ : 0 ≤ κ)
    (ha1 : 0 ≤ a1) (hg1 : 0 ≤ g1) (hl1 : 0 ≤ l1) (hΘ : 1 ≤ Θ)
    (hK : K = Θ * (N : ℝ) ^ (1 / (mm : ℝ)))
    (hΛ : Λ = (N : ℝ) ^ ((12 : ℝ) / (mm : ℝ) + 4 * ε)) (hΛle : Λ ≤ (N : ℝ) ^ δ) :
    2 * (2 * (a1 * (K + 1) ^ 2 / V ^ 2) *
        (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2) +
          l1 * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2))) ^ 2
      ≤ 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ *
          (κ * (N : ℝ) ^ 4 / V ^ 4) := by
  have hN100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) := by linarith
  have hNlt : 1 < (N : ℝ) := by linarith
  have hNpos : 0 < (N : ℝ) := by linarith
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  -- `δ ≥ 12/mm + 4ε`, from `Λ = N^{12/mm+4ε} ≤ N^δ` with `N > 1`.
  have hδge : (12 : ℝ) / (mm : ℝ) + 4 * ε ≤ δ := by
    have h := hΛle
    rw [hΛ] at h
    exact (Real.rpow_le_rpow_left_iff hNlt).mp h
  -- `K ≥ 1`
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (mm : ℝ)) := Real.one_le_rpow hN1 (by positivity)
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ Θ * (N : ℝ) ^ (1 / (mm : ℝ)) := mul_le_mul hΘ h1 (by norm_num) (by positivity)
  have hKp1 : 1 ≤ K + 1 := by linarith
  -- `N^ε ≤ N^{2ε}`
  have hNeps : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (2 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- ### Step 1: bound `2g₁(K+1)⁴N^ε + l₁N^{2ε} ≤ 2(g₁+l₁)(K+1)⁴N^{2ε}`
  have hT0 : 0 ≤ 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε) := by positivity
  have hTle : 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)
      ≤ 2 * (g1 + l1) * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) := by
    have h1 : 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε
        ≤ 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left hNeps (by positivity)
    have h2 : l1 * (N : ℝ) ^ (2 * ε) ≤ 2 * l1 * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) := by
      have hKp : (1 : ℝ) ≤ 2 * (K + 1) ^ 4 := by
        have h : (1 : ℝ) ≤ (K + 1) ^ 4 := one_le_pow₀ hKp1
        nlinarith
      calc l1 * (N : ℝ) ^ (2 * ε) = 1 * (l1 * (N : ℝ) ^ (2 * ε)) := by ring
        _ ≤ (2 * (K + 1) ^ 4) * (l1 * (N : ℝ) ^ (2 * ε)) :=
            mul_le_mul_of_nonneg_right hKp (by positivity)
        _ = 2 * l1 * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) := by ring
    calc 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)
        ≤ 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε)
            + 2 * l1 * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) := add_le_add h1 h2
      _ = 2 * (g1 + l1) * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε) := by ring
  -- ### Step 2: square it
  have hsq : ((N : ℝ) ^ (2 * ε)) ^ 2 = (N : ℝ) ^ (4 * ε) := by
    rw [rpow_pow_nat (N : ℝ) hNnonneg (2 * ε) 2]
    congr 1
    ring
  have hTsq : (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
      ≤ 4 * (g1 + l1) ^ 2 * (K + 1) ^ 8 * (N : ℝ) ^ (4 * ε) := by
    have h := pow_le_pow_left₀ hT0 hTle 2
    have he : (2 * (g1 + l1) * (K + 1) ^ 4 * (N : ℝ) ^ (2 * ε)) ^ 2
        = 4 * (g1 + l1) ^ 2 * (K + 1) ^ 8 * (N : ℝ) ^ (4 * ε) := by
      rw [← hsq]; ring
    rwa [he] at h
  have hstep1 : 8 * (K + 1) ^ 4
        * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
      ≤ 32 * (g1 + l1) ^ 2 * (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε) := by
    have h1 : 8 * (K + 1) ^ 4
          * ((2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2)
        ≤ 8 * (K + 1) ^ 4 * (4 * (g1 + l1) ^ 2 * (K + 1) ^ 8 * (N : ℝ) ^ (4 * ε)) :=
      mul_le_mul_of_nonneg_left hTsq (by positivity)
    calc 8 * (K + 1) ^ 4
          * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
        = 8 * (K + 1) ^ 4
            * ((2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2) := by
          ring
      _ ≤ 8 * (K + 1) ^ 4 * (4 * (g1 + l1) ^ 2 * (K + 1) ^ 8 * (N : ℝ) ^ (4 * ε)) := h1
      _ = 32 * (g1 + l1) ^ 2 * (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε) := by ring
  -- ### Step 3: `(K+1)^12 ≤ 2^12 Θ^12 N^{12/mm}`, and `N^{12/mm} N^{4ε} ≤ N^δ`
  have hKp1le : K + 1 ≤ 2 * K := by linarith
  have h12 : (K + 1) ^ 12 ≤ 4096 * Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ)) := by
    have h1 : (K + 1) ^ 12 ≤ (2 * K) ^ 12 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ K + 1) hKp1le 12
    have h2 : (2 * K) ^ 12 = 4096 * K ^ 12 := by ring
    have h3 : K ^ 12 = Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ)) := by
      rw [hK, mul_pow, rpow_pow_nat (N : ℝ) hNnonneg (1 / (mm : ℝ)) 12]
      congr 1
      ring_nf
    calc (K + 1) ^ 12 ≤ (2 * K) ^ 12 := h1
      _ = 4096 * K ^ 12 := h2
      _ = 4096 * (Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ))) := by rw [h3]
      _ = 4096 * Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ)) := by ring
  have h12b : (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε) ≤ 4096 * Θ ^ 12 * (N : ℝ) ^ δ := by
    have hmul : (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε)
        ≤ (4096 * Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ))) * (N : ℝ) ^ (4 * ε) :=
      mul_le_mul_of_nonneg_right h12 (by positivity)
    have hexp : (N : ℝ) ^ (12 / (mm : ℝ)) * (N : ℝ) ^ (4 * ε)
        = (N : ℝ) ^ ((12 : ℝ) / (mm : ℝ) + 4 * ε) :=
      (Real.rpow_add hNpos _ _).symm
    have hle : (N : ℝ) ^ ((12 : ℝ) / (mm : ℝ) + 4 * ε) ≤ (N : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hN1 hδge
    calc (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε)
        ≤ (4096 * Θ ^ 12 * (N : ℝ) ^ (12 / (mm : ℝ))) * (N : ℝ) ^ (4 * ε) := hmul
      _ = 4096 * Θ ^ 12 * ((N : ℝ) ^ (12 / (mm : ℝ)) * (N : ℝ) ^ (4 * ε)) := by ring
      _ = 4096 * Θ ^ 12 * (N : ℝ) ^ ((12 : ℝ) / (mm : ℝ) + 4 * ε) := by rw [hexp]
      _ ≤ 4096 * Θ ^ 12 * (N : ℝ) ^ δ := mul_le_mul_of_nonneg_left hle (by positivity)
  have hstep2 : 32 * (g1 + l1) ^ 2 * (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε)
      ≤ 131072 * (g1 + l1) ^ 2 * Θ ^ 12 * (N : ℝ) ^ δ := by
    calc 32 * (g1 + l1) ^ 2 * (K + 1) ^ 12 * (N : ℝ) ^ (4 * ε)
        = 32 * (g1 + l1) ^ 2 * ((K + 1) ^ 12 * (N : ℝ) ^ (4 * ε)) := by ring
      _ ≤ 32 * (g1 + l1) ^ 2 * (4096 * Θ ^ 12 * (N : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left h12b (by positivity)
      _ = 131072 * (g1 + l1) ^ 2 * Θ ^ 12 * (N : ℝ) ^ δ := by ring
  -- ### Step 4: absorb into `(g₁+1)²(l₁+1)²(Θ+1)^{12}`
  have hgl : (g1 + l1) ^ 2 ≤ (g1 + 1) ^ 2 * (l1 + 1) ^ 2 := by
    have h1 : g1 + l1 ≤ (g1 + 1) * (l1 + 1) := by nlinarith [mul_nonneg hg1 hl1]
    have h2 : (g1 + l1) ^ 2 ≤ ((g1 + 1) * (l1 + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : ((g1 + 1) * (l1 + 1)) ^ 2 = (g1 + 1) ^ 2 * (l1 + 1) ^ 2 := by ring
    rwa [h3] at h2
  have hTh : Θ ^ 12 ≤ (Θ + 1) ^ 12 := pow_le_pow_left₀ (by linarith) (by linarith) 12
  have hstep3 : 131072 * (g1 + l1) ^ 2 * Θ ^ 12 * (N : ℝ) ^ δ
      ≤ 262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ := by
    have hprod : (g1 + l1) ^ 2 * Θ ^ 12
        ≤ (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 :=
      mul_le_mul hgl hTh (by positivity) (by positivity)
    have hXY : 131072 * ((g1 + l1) ^ 2 * Θ ^ 12)
        ≤ 262144 * ((g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12) :=
      calc 131072 * ((g1 + l1) ^ 2 * Θ ^ 12)
          ≤ 131072 * ((g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ ≤ 262144 * ((g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc 131072 * (g1 + l1) ^ 2 * Θ ^ 12 * (N : ℝ) ^ δ
        = 131072 * ((g1 + l1) ^ 2 * Θ ^ 12) * (N : ℝ) ^ δ := by ring
      _ ≤ 262144 * ((g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12) * (N : ℝ) ^ δ :=
          mul_le_mul_of_nonneg_right hXY (by positivity)
      _ = 262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ := by ring
  -- ### Step 5: the `a₁` factor
  have key : 8 * (K + 1) ^ 4
        * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
      ≤ 262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ :=
    le_trans (le_trans hstep1 hstep2) hstep3
  have hR0 : 0 ≤ 262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ := by
    positivity
  have ha1sq : a1 ^ 2 ≤ (a1 + 1) ^ 2 := pow_le_pow_left₀ ha1 (by linarith) 2
  have hred : 8 * a1 ^ 2 * (K + 1) ^ 4
        * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
      ≤ 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ := by
    calc 8 * a1 ^ 2 * (K + 1) ^ 4
          * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
        = a1 ^ 2 * (8 * (K + 1) ^ 4
            * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2) := by
          ring
      _ ≤ a1 ^ 2 * (262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left key (sq_nonneg a1)
      _ ≤ (a1 + 1) ^ 2
            * (262144 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_right ha1sq hR0
      _ = 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ := by
          ring
  -- ### Step 6: expand the two sides and multiply by `κ N⁴/V⁴`
  have hL : 2 * (2 * (a1 * (K + 1) ^ 2 / V ^ 2) *
        (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2) +
          l1 * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2))) ^ 2
      = 8 * a1 ^ 2 * (K + 1) ^ 4
          * (2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε + l1 * (N : ℝ) ^ (2 * ε)) ^ 2
          * (κ * (N : ℝ) ^ 4 / V ^ 4) := by
    set c := κ ^ ((1 : ℝ) / 2) with hc_def
    have hcc : c * c = κ := by rw [hc_def, ← sq, ← Real.sqrt_eq_rpow, Real.sq_sqrt hκ]
    rw [← hcc]
    ring
  have hR : 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12
        * (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)
      = (262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 * (N : ℝ) ^ δ) *
        (κ * (N : ℝ) ^ 4 / V ^ 4) := by ring
  rw [hL, hR]
  apply mul_le_mul_of_nonneg_right hred
  positivity

end Work.GM.Energy.EnergyCore2
