import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp

namespace Work.BourgainPlan.Maximal

open Filter Topology

/-- The arithmetic of the interpolation of the two major-arc endpoints (Mirek-Stein-Trojan §4.2, eqs. (73), (80)): for a fixed `θ ∈ (0,1)` and constants `C₁, C₂ > 0`,

  `(C₂ · 2^{−n/2})^{1−θ} · (C₁ · exp((n^1)^{1/10}))^θ ≤ C · 2^{−cn}`  for all `n ∈ ℕ`, some `C > 0`, `c > 0`.

This is what turns the interpolated constant of `opMulFinsuppLM_interp` (`Maximal/mst_majErr_interp.lean`) — the product of the `ℓ²` gain `2^{−n/2}` raised to `1−θ` and the trivial `ℓʳ` loss `exp(n^{1/10})` raised to `θ` — into an exponential gain, which is summable in `n`.  The loss is subexponential (`n^{1/10}`) while the gain is exponential, so any `θ < 1` works.

Suggested proof: choose `c := (1−θ)/16` and show that for `n` beyond an explicit threshold `N₀` one has `θ n^{1/10} ≤ ((1−θ) log 2 / 16) n`, using `n^{1/10} = n · n^{−9/10}` (`Real.rpow_add`) and `n^{−9/10} ≤ K` for `n ≥ K^{−10/9}` (`Real.rpow_le_rpow`/`Real.rpow_neg`); below the threshold `exp (θ n^{1/10})` is bounded by `exp (θ N₀^{1/10})`.  Rewrite `2^x = Real.exp (x log 2)` (`Real.rpow_def_of_pos`), `(a*b)^{1−θ} = a^{1−θ} b^{1−θ}` (`Real.mul_rpow`), `(2^{−n/2})^{1−θ} = 2^{−n(1−θ)/2}` (`Real.rpow_mul`), and `(C₁ Real.exp v)^θ = C₁^θ Real.exp (θ v)`.  Then take `C := max 1 (C₂^{1−θ} C₁^θ) · Real.exp (θ N₀^{1/10})`. -/
theorem mst_interp_arithmetic {θ C₁ C₂ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2))) ^ (1 - θ)
          * (C₁ * Real.exp (((n : ℝ) ^ (1 : ℕ)) ^ (1 / 10 : ℝ))) ^ θ
        ≤ C * (2 : ℝ) ^ (-(c * (n : ℝ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1θ : 0 < 1 - θ := by linarith
  have htend : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-(9 / 10 : ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 9/10)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ,
      ∀ n ≥ N₀, (n : ℝ) ^ (-(9 / 10 : ℝ)) < (1 - θ) * Real.log 2 / (4 * θ) :=
    Filter.eventually_atTop.1
      ((tendsto_order.1 htend).2 _ (div_pos (mul_pos h1θ hlog2) (by linarith)))
  have core : ∀ n : ℕ, θ * ((n : ℝ) ^ (1/10:ℝ)) - (1 - θ) * Real.log 2 * (n:ℝ) / 4
                        ≤ θ * ((N₀:ℝ) ^ (1/10:ℝ)) := by
    intro n
    rcases lt_or_ge n N₀ with hn | hn
    · have h1 : ((n:ℝ)^(1/10:ℝ)) ≤ ((N₀:ℝ)^(1/10:ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast le_of_lt hn) (by norm_num)
      have h2 : 0 ≤ (1 - θ) * Real.log 2 * (n:ℝ) / 4 :=
        div_nonneg (mul_nonneg (mul_nonneg (le_of_lt h1θ) (le_of_lt hlog2)) (Nat.cast_nonneg n))
          (by norm_num)
      have h3 : θ * ((n:ℝ)^(1/10:ℝ)) ≤ θ * ((N₀:ℝ)^(1/10:ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hθ0)
      linarith
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hN0 : N₀ = 0 := Nat.eq_zero_of_le_zero hn
        rw [hN0]
        simp only [Nat.cast_zero]
        rw [Real.zero_rpow (by norm_num : (1/10:ℝ) ≠ 0)]
        simp
      · have hv : (n:ℝ)^(1/10:ℝ) = (n:ℝ) * (n:ℝ)^(-(9/10:ℝ)) := by
          rw [show (1/10:ℝ) = 1 + (-(9/10):ℝ) by norm_num,
              Real.rpow_add (by exact_mod_cast hpos), Real.rpow_one]
        have hb := hN₀ n hn
        have hstep : (n:ℝ)^(1/10:ℝ) ≤ (n:ℝ) * ((1-θ) * Real.log 2 / (4*θ)) := by
          rw [hv]
          exact mul_le_mul_of_nonneg_left (le_of_lt hb) (Nat.cast_nonneg n)
        have hgoal : θ * ((n:ℝ) * ((1-θ)*Real.log 2/(4*θ))) = (1-θ)*Real.log 2*(n:ℝ)/4 := by
          field_simp
          try ring
        have hmain : θ * ((n:ℝ)^(1/10:ℝ)) ≤ (1-θ)*Real.log 2*(n:ℝ)/4 := by
          calc θ * ((n:ℝ)^(1/10:ℝ)) ≤ θ * ((n:ℝ) * ((1-θ)*Real.log 2/(4*θ))) :=
                mul_le_mul_of_nonneg_left hstep (le_of_lt hθ0)
            _ = (1-θ)*Real.log 2*(n:ℝ)/4 := hgoal
        have hMnn : 0 ≤ θ * ((N₀:ℝ)^(1/10:ℝ)) :=
          mul_nonneg (le_of_lt hθ0) (Real.rpow_nonneg (Nat.cast_nonneg N₀) _)
        linarith
  have hDpos : 0 < C₂ ^ (1 - θ) * C₁ ^ θ :=
    mul_pos (Real.rpow_pos_of_pos hC₂ _) (Real.rpow_pos_of_pos hC₁ _)
  refine ⟨C₂ ^ (1 - θ) * C₁ ^ θ * Real.exp (θ * (N₀ : ℝ) ^ (1/10 : ℝ)), (1 - θ) / 4,
    ?_, ?_, ?_⟩
  · exact mul_pos hDpos (Real.exp_pos _)
  · exact div_pos h1θ (by norm_num)
  · intro n
    have hv : ((n:ℝ)^(1:ℕ))^(1/10:ℝ) = (n:ℝ)^(1/10:ℝ) := by simp
    have hLHS : (C₂ * (2:ℝ)^(-((n:ℝ)/2)))^(1-θ) * (C₁ * Real.exp ((n:ℝ)^(1/10:ℝ)))^θ
        = (C₂^(1-θ) * C₁^θ) *
            Real.exp (Real.log 2 * (-((n:ℝ)/2) * (1-θ)) + (n:ℝ)^(1/10:ℝ) * θ) := by
      calc (C₂ * (2:ℝ)^(-((n:ℝ)/2)))^(1-θ) * (C₁ * Real.exp ((n:ℝ)^(1/10:ℝ)))^θ
          = (C₂^(1-θ) * ((2:ℝ)^(-((n:ℝ)/2)))^(1-θ)) *
              (C₁^θ * (Real.exp ((n:ℝ)^(1/10:ℝ)))^θ) := by
              rw [Real.mul_rpow (le_of_lt hC₂) (Real.rpow_nonneg (by norm_num) _),
                  Real.mul_rpow (le_of_lt hC₁) (le_of_lt (Real.exp_pos _))]
        _ = (C₂^(1-θ) * Real.exp (Real.log 2 * (-((n:ℝ)/2) * (1-θ)))) *
              (C₁^θ * Real.exp ((n:ℝ)^(1/10:ℝ) * θ)) := by
              rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
                  Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
                  Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        _ = (C₂^(1-θ) * C₁^θ) *
              (Real.exp (Real.log 2 * (-((n:ℝ)/2) * (1-θ))) *
                Real.exp ((n:ℝ)^(1/10:ℝ) * θ)) := by ring
        _ = (C₂^(1-θ) * C₁^θ) *
              Real.exp (Real.log 2 * (-((n:ℝ)/2) * (1-θ)) + (n:ℝ)^(1/10:ℝ) * θ) := by
              rw [Real.exp_add]
    have hRHS : (C₂^(1-θ) * C₁^θ) * Real.exp (θ * (N₀:ℝ)^(1/10:ℝ)) *
          (2:ℝ)^(-((1-θ)/4 * (n:ℝ)))
        = (C₂^(1-θ) * C₁^θ) *
            Real.exp (θ * (N₀:ℝ)^(1/10:ℝ) + Real.log 2 * (-((1-θ)/4 * (n:ℝ)))) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_assoc, ← Real.exp_add]
    have key : Real.log 2 * (-((n:ℝ)/2) * (1-θ)) + (n:ℝ)^(1/10:ℝ) * θ
        ≤ θ * (N₀:ℝ)^(1/10:ℝ) + Real.log 2 * (-((1-θ)/4 * (n:ℝ))) := by
      have h1 : Real.log 2 * (-((n:ℝ)/2) * (1-θ)) = -((1-θ) * Real.log 2 * (n:ℝ)/2) := by ring
      have h2 : Real.log 2 * (-((1-θ)/4 * (n:ℝ))) = -((1-θ) * Real.log 2 * (n:ℝ)/4) := by ring
      rw [h1, h2]
      linarith [core n]
    rw [hv, hLHS, hRHS]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (le_of_lt hDpos)


end Work.BourgainPlan.Maximal
