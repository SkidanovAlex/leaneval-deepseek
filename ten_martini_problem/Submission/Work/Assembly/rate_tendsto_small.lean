import Mathlib

namespace Work.Assembly

open Filter Asymptotics
open scoped Topology

theorem rate_tendsto_small (L : ℝ) (hL : 0 < L) (Cθ : ℝ) :
    (∃ Q₀ : ℝ, ∀ Q ≥ Q₀, (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q + 200 / Q ≤ L / 200) ∧
    (∃ R₀ : ℝ, ∀ R ≥ R₀, (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) ≤ L / 200) := by
  have hL200 : (0 : ℝ) < L / 200 := by linarith
  -- First rate: `(2 log(4/3) + 202 log Q)/Q + 200/Q → 0`.
  have hlogdiv : Tendsto (fun Q : ℝ => Real.log Q / Q) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
    simpa [Real.rpow_one] using h
  have key1 :
      Tendsto (fun Q : ℝ => (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q + 200 / Q)
        atTop (𝓝 0) := by
    have h1 : Tendsto (fun Q : ℝ => 2 * Real.log (4 / 3) * Q⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (2 * Real.log (4 / 3) : ℝ))).mul tendsto_inv_atTop_zero
      simpa using h
    have h2 : Tendsto (fun Q : ℝ => 202 * (Real.log Q / Q)) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (202 : ℝ))).mul hlogdiv
      simpa using h
    have h3 : Tendsto (fun Q : ℝ => 200 * Q⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (200 : ℝ))).mul tendsto_inv_atTop_zero
      simpa using h
    have hsum : Tendsto
        (fun Q : ℝ => 2 * Real.log (4 / 3) * Q⁻¹ + 202 * (Real.log Q / Q) + 200 * Q⁻¹)
        atTop (𝓝 0) := by
      simpa using (h1.add h2).add h3
    have heq : (fun Q : ℝ => (2 * Real.log (4 / 3) + 202 * Real.log Q) / Q + 200 / Q)
        = fun Q : ℝ => 2 * Real.log (4 / 3) * Q⁻¹ + 202 * (Real.log Q / Q) + 200 * Q⁻¹ := by
      funext Q
      ring
    rw [heq]
    exact hsum
  -- Second rate: `(8/3)(|Cθ| + 20 log(R+2))/R^(8/9) → 0`.
  have hs : (0 : ℝ) < 8 / 9 := by norm_num
  have hcomp : (fun R : ℝ => Real.log (R + 2)) =o[atTop]
      (fun R : ℝ => (R + 2) ^ (8 / 9 : ℝ)) := by
    have hg : Tendsto (fun R : ℝ => R + 2) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop (r := (8 / 9 : ℝ)) hs).comp_tendsto hg
  have hbig : (fun R : ℝ => (R + 2) ^ (8 / 9 : ℝ)) =O[atTop]
      (fun R : ℝ => R ^ (8 / 9 : ℝ)) := by
    refine IsBigO.of_bound (2 ^ (8 / 9 : ℝ)) ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have hR0 : 0 ≤ R := by linarith
    have hR20 : 0 ≤ R + 2 := by linarith
    have hle : R + 2 ≤ 2 * R := by linarith
    calc ‖(R + 2) ^ (8 / 9 : ℝ)‖ = (R + 2) ^ (8 / 9 : ℝ) :=
          Real.norm_of_nonneg (Real.rpow_nonneg hR20 _)
      _ ≤ (2 * R) ^ (8 / 9 : ℝ) := Real.rpow_le_rpow hR20 hle (le_of_lt hs)
      _ = 2 ^ (8 / 9 : ℝ) * R ^ (8 / 9 : ℝ) := Real.mul_rpow (by norm_num) hR0
      _ = 2 ^ (8 / 9 : ℝ) * ‖R ^ (8 / 9 : ℝ)‖ := by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg hR0 _)]
  have hv : Tendsto (fun R : ℝ => Real.log (R + 2) / R ^ (8 / 9 : ℝ)) atTop (𝓝 0) :=
    (hcomp.trans_isBigO hbig).tendsto_div_nhds_zero
  have hinvpow : Tendsto (fun R : ℝ => (R ^ (8 / 9 : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop hs
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx]
  have key2 :
      Tendsto (fun R : ℝ => (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ))
        atTop (𝓝 0) := by
    have hu : Tendsto
        (fun R : ℝ => (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ)) atTop (𝓝 0) := by
      have hA : Tendsto (fun R : ℝ => |Cθ| * (R ^ (8 / 9 : ℝ))⁻¹) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := (|Cθ| : ℝ))).mul hinvpow
        simpa using h
      have hB : Tendsto (fun R : ℝ => 20 * (Real.log (R + 2) / R ^ (8 / 9 : ℝ)))
          atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := (20 : ℝ))).mul hv
        simpa using h
      have hsum : Tendsto (fun R : ℝ => |Cθ| * (R ^ (8 / 9 : ℝ))⁻¹
          + 20 * (Real.log (R + 2) / R ^ (8 / 9 : ℝ))) atTop (𝓝 0) := by
        simpa using hA.add hB
      have heq : (fun R : ℝ => (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ))
          = fun R : ℝ => |Cθ| * (R ^ (8 / 9 : ℝ))⁻¹
              + 20 * (Real.log (R + 2) / R ^ (8 / 9 : ℝ)) := by
        funext R
        ring
      rw [heq]
      exact hsum
    have h : Tendsto
        (fun R : ℝ => (8 / 3) * ((|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (8 / 3 : ℝ))).mul hu
    have heq : (fun R : ℝ => (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ))
        = fun R : ℝ => (8 / 3) * ((|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ)) := by
      funext R
      ring
    rw [heq]
    exact h
  exact ⟨Filter.eventually_atTop.mp (Filter.Tendsto.eventually_le_const hL200 key1),
    Filter.eventually_atTop.mp (Filter.Tendsto.eventually_le_const hL200 key2)⟩

end Work.Assembly
