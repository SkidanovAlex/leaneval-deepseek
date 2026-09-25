import Mathlib

/-!
# Exponential decay beats polynomial decay

For `α γ K > 0` the exponential sequence `2 ^ (-(γ n))` eventually dominates the
polynomial sequence `(n+1) ^ (-α)` up to the constant `K`:

  `K * 2 ^ (-(γ n)) ≤ (n+1) ^ (-α)` for all large `n`.

This is used to absorb a constant multiplicative factor into the decay rate of the
dyadic (lacunary) scale `2 ^ n`.
-/

namespace Work.BourgainPlan.Maximal

open Filter
open scoped Topology

/-- Elementary algebra step: if `A, B > 0` and `K * B / A ≤ 1` then `K / A ≤ 1 / B`. -/
lemma inv_le_inv_of_mul_inv_le_one {K A B : ℝ} (hB : 0 < B) (h : K * B * A⁻¹ ≤ 1) :
    K * A⁻¹ ≤ B⁻¹ := by
  have h2 : (K * A⁻¹) * B ≤ 1 := by
    rw [mul_right_comm]
    exact h
  have hgoal : K * A⁻¹ ≤ 1 / B := (le_div_iff₀ hB).mpr h2
  simpa [one_div] using hgoal

lemma rpow_decay_le_exp_decay (α γ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (K : ℝ) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      K * (2 : ℝ) ^ (-(γ * (n : ℝ))) ≤ ((n : ℝ) + 1) ^ (-α) := by
  -- The exponential base: `2 ^ (γ n) = exp ((γ log 2) n)` with `γ log 2 > 0`.
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb : 0 < γ * Real.log 2 := mul_pos hγ hlog2
  -- Step 1: `x ↦ x ^ α * exp (-(γ log 2) x)` tends to `0` at `+∞`.
  have h0 : Tendsto (fun y : ℝ => y ^ α * Real.exp (-(γ * Real.log 2) * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero α (γ * Real.log 2) hb
  -- Shift the pivot so that the polynomial factor becomes `(x+1) ^ α`.
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_id
  have h1 : Tendsto (fun x : ℝ => (x + 1) ^ α * Real.exp (-(γ * Real.log 2) * x)) atTop (𝓝 0) := by
    have hfun : (fun x : ℝ => (x + 1) ^ α * Real.exp (-(γ * Real.log 2) * x))
        = fun x : ℝ => Real.exp (γ * Real.log 2) *
            ((x + 1) ^ α * Real.exp (-(γ * Real.log 2) * (x + 1))) := by
      funext x
      have hexp : Real.exp (γ * Real.log 2) * Real.exp (-(γ * Real.log 2) * (x + 1))
          = Real.exp (-(γ * Real.log 2) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring
    rw [hfun]
    simpa using (h0.comp hshift).const_mul (Real.exp (γ * Real.log 2))
  -- Step 2: restrict to `ℕ`.
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ α * Real.exp (-(γ * Real.log 2) * (n : ℝ)))
      atTop (𝓝 0) := by
    have := h1.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def] using this
  -- Step 3: multiply by the constant `K`.
  have h3 : Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ α * Real.exp (-(γ * Real.log 2) * (n : ℝ)))
      atTop (𝓝 0) := by
    have := h2.const_mul K
    simpa only [mul_assoc, mul_zero] using this
  -- Step 4: rewrite the exponential as the dyadic power `2 ^ (-(γ n))`.
  have h4 : Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ α * (2 : ℝ) ^ (-(γ * (n : ℝ))))
      atTop (𝓝 0) := by
    have hfun : (fun n : ℕ => K * ((n : ℝ) + 1) ^ α * (2 : ℝ) ^ (-(γ * (n : ℝ))))
        = fun n : ℕ => K * ((n : ℝ) + 1) ^ α * Real.exp (-(γ * Real.log 2) * (n : ℝ)) := by
      funext n
      congr 1
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
      congr 1
      ring
    rw [hfun]
    exact h3
  -- Step 5: the auxiliary sequence is eventually `≤ 1`.
  have hev : ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) + 1) ^ α * (2 : ℝ) ^ (-(γ * (n : ℝ))) ≤ 1 := by
    have := (tendsto_order.1 h4).2 1 zero_lt_one
    exact this.mono fun n hn => hn.le
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  -- Now convert `K * (n+1) ^ α * 2 ^ (-(γ n)) ≤ 1` into the desired inequality.
  have h := hN n hn
  have hA : (0 : ℝ) < (2 : ℝ) ^ (γ * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hB : (0 : ℝ) < ((n : ℝ) + 1) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hh : K * ((n : ℝ) + 1) ^ α * ((2 : ℝ) ^ (γ * (n : ℝ)))⁻¹ ≤ 1 := by
    simpa only [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)] using h
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num),
    Real.rpow_neg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
  exact inv_le_inv_of_mul_inv_le_one hB hh

end Work.BourgainPlan.Maximal
