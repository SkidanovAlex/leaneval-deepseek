import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotics

open Filter Topology

/-- If `log (W x)` is `o(√(log x))` and `σ < 1`, then `W x · x^{σ-1} · (log x)^k → 0`.
No positivity hypothesis on `W` is needed: if `W x = 0` then `Real.log 0 = 0` and the
product vanishes. -/
theorem tendsto_mul_rpow_mul_log_pow_zero {W : ℕ → ℕ} {σ : ℝ} (hσ : σ < 1) (k : ℕ)
    (hlq : Filter.Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x : ℕ => (W x : ℝ) * (x : ℝ) ^ (σ - 1) * (Real.log (x : ℝ)) ^ k)
      Filter.atTop (nhds 0) := by
  -- `log x → +∞`.
  have hB : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `√(log x) / log x → 0`, since `√t / t → 0` at `+∞`.
  have hG : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have h2 : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (nhds 0) := by
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [inv_eq_one_div]
      field_simp
      rw [Real.sq_sqrt ht.le]
    exact h2.comp hB
  -- Multiplying the hypothesis by `√(log x) / log x` gives `log (W x) / log x → 0`.
  have hAB : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.log (x : ℝ)) atTop (nhds 0) := by
    have h := hlq.mul hG
    have h' : Tendsto (fun x : ℕ =>
        (Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
          * (Real.sqrt (Real.log (x : ℝ)) / Real.log (x : ℝ))) atTop (nhds 0) := by
      simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
    have hl : Real.log (x:ℝ) ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hs : Real.sqrt (Real.log (x:ℝ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos_of_pos (Real.log_pos hx1))
    field_simp
  -- `log (log x) / log x → 0`.
  have hloglog : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hB
  -- The exponent of the product.
  let E : ℕ → ℝ := fun x => Real.log (W x : ℝ) + (σ - 1) * Real.log (x : ℝ)
      + (k : ℝ) * Real.log (Real.log (x : ℝ))
  -- `E x / log x → σ - 1`.
  have hEdiv : Tendsto (fun x : ℕ => E x / Real.log (x : ℝ)) atTop (nhds (σ - 1)) := by
    have hmain : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.log (x : ℝ)
        + (σ - 1) + (k : ℝ) * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) atTop
        (nhds (0 + (σ - 1) + (k : ℝ) * 0)) :=
      ((hAB.add tendsto_const_nhds).add (hloglog.const_mul (k : ℝ)))
    have hmain' : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.log (x : ℝ)
        + (σ - 1) + (k : ℝ) * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) atTop
        (nhds (σ - 1)) := by simpa using hmain
    refine hmain'.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hl : Real.log (x:ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < x)))
    dsimp only [E]
    field_simp
  -- `E x → -∞`, because `E x = log x · (E x / log x)` and the ratio tends to `σ - 1 < 0`.
  have hEatBot : Tendsto E atTop atBot := by
    have h := Tendsto.atTop_mul_neg (f := fun x : ℕ => Real.log (x : ℝ))
        (g := fun x : ℕ => E x / Real.log (x : ℝ)) (C := σ - 1) (by linarith) hB hEdiv
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hl : Real.log (x:ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < x)))
    field_simp
  have hexp : Tendsto (fun x : ℕ => Real.exp (E x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hEatBot
  -- Squeeze: `0 ≤ W x · x^{σ-1} · (log x)^k ≤ exp (E x)`, and `exp (E x) → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
    positivity
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
    have hx0 : (0:ℝ) < (x:ℝ) := by linarith
    have hl : 0 < Real.log (x:ℝ) := Real.log_pos hx1
    have e1 : (x:ℝ)^(σ-1) = Real.exp (Real.log (x:ℝ) * (σ-1)) :=
      Real.rpow_def_of_pos hx0 (σ-1)
    have e2 : (Real.log (x:ℝ))^k = Real.exp (Real.log (Real.log (x:ℝ)) * (k:ℝ)) := by
      rw [← Real.rpow_natCast (Real.log (x:ℝ)) k]
      exact Real.rpow_def_of_pos hl (k:ℝ)
    rw [e1, e2]
    have hWA : (W x : ℝ) ≤ Real.exp (Real.log (W x : ℝ)) := Real.le_exp_log _
    have hp1 : (0:ℝ) ≤ Real.exp (Real.log (x:ℝ) * (σ-1)) := (Real.exp_pos _).le
    have hp2 : (0:ℝ) ≤ Real.exp (Real.log (Real.log (x:ℝ)) * (k:ℝ)) := (Real.exp_pos _).le
    calc (W x : ℝ) * Real.exp (Real.log (x:ℝ) * (σ-1))
            * Real.exp (Real.log (Real.log (x:ℝ)) * (k:ℝ))
        ≤ Real.exp (Real.log (W x : ℝ)) * Real.exp (Real.log (x:ℝ) * (σ-1))
            * Real.exp (Real.log (Real.log (x:ℝ)) * (k:ℝ)) := by
          gcongr
        _ = Real.exp (E x) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          dsimp only [E]
          ring

end Commons.Analysis.Asymptotics