/-
# `Submission.Work.FIArea7.nc_termH`

Bound on the second term (`C_H`, "region II") of the `NumericCore` arithmetic of
`Submission/Work/FIArea7/Area7Assembly6.lean`.  With `X⁸ ≤ N^{δ₁}`, `δ₁ < 3/32`,
`K ≥ X³(log(N+2))²⁰`, `θ ≤ 1` and `UB ≤ 4θN+2`, the region-II term

`C_H(1+Clat)·1000(θN+√N+1)(log(N+2))³·(log(K+2))²·(X(2K+1)N^{1-δ₁} + X log(UB+2))`

is `≤ M·X⁻¹·N²·log N`.

The proof splits into four elementary pieces, each established in its own module:

* `nc_A_bound`   : `1000(θN+√N+1)(log(N+2))³ ≤ 3000·N·(log(N+2))³`;
* `nc_logK_bound`: `(log(K+2))² ≤ 2500·(log N)²`;
* `nc_XC_bound`  : `X·(X(2K+1)N^{1-δ₁} + X log(UB+2)) ≤ 6N^{1-3δ₁/8}(log(N+2))²⁰ + 2N^{δ₁/4}log N`;
* `nc_core_arith`: the final product bound `3000N·(log(N+2))³·2500(log N)²·(…) ≤ 6·10⁷ N² log N`,
  given the two log-domination facts `(log(N+2))²³log N ≤ N^{3δ₁/8}` and
  `(loga(N+2))³(log N)² ≤ N^{1-δ₁/4}` supplied by `nc_log_threshold`.
-/
import Mathlib
import Submission.Work.FIArea7.NCBasic
import Submission.Work.FIArea7.nc_log_threshold
import Submission.Work.FIArea7.nc_logK_bound
import Submission.Work.FIArea7.nc_XC_bound
import Submission.Work.FIArea7.nc_core_arith
import Submission.Work.FIArea7.nc_A_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open scoped BigOperators

theorem nc_termH (C_H Clat δ₁ : ℝ) (hCH : 0 < C_H) (hCl : 0 < Clat) (hδ0 : 0 < δ₁)
    (hδ32 : δ₁ < 3 / 32) :
    ∃ N₀ M : ℝ, 0 < M ∧ ∀ {N X θ UB : ℝ} {K : ℕ},
      3 ≤ N → N₀ ≤ N → 1 ≤ X → 0 < θ → θ ≤ 1 → X ^ 8 ≤ N ^ δ₁ → 1 ≤ (K : ℝ) →
      X ^ 3 * (Real.log (N + 2)) ^ 20 ≤ (K : ℝ) →
      (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20 →
      0 < UB → UB ≤ 4 * θ * N + 2 →
      C_H * (1 + Clat) * (1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3)
          * (Real.log ((K : ℝ) + 2)) ^ 2
          * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
        ≤ M * X⁻¹ * N ^ 2 * Real.log N := by
  obtain ⟨N₀, hN₀5, hthr⟩ := nc_log_threshold δ₁ hδ0 hδ32
  refine ⟨N₀, C_H * (1 + Clat) * 60000000, by positivity, ?_⟩
  intro N X θ UB K hN3 hN0 hX1 hθ0 hθ1 hX8 hK1 hKlo hKhi hUB0 hUBhi
  have hN5 : 5 ≤ N := le_trans hN₀5 hN0
  obtain ⟨ha, hb⟩ := hthr N hN0
  have hNpos : (0 : ℝ) < N := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  -- Abbreviate the three factors of the region-II term.
  set a : ℝ := 1000 * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3 with ha_def
  set b : ℝ := (Real.log ((K : ℝ) + 2)) ^ 2 with hb_def
  set c : ℝ := X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2) with hc_def
  -- The three factor bounds.
  have hA : a ≤ 3000 * N * (Real.log (N + 2)) ^ 3 := by
    rw [ha_def]; exact nc_A_bound hN3 hθ1
  have hB : b ≤ 2500 * (Real.log N) ^ 2 := by
    rw [hb_def]; exact nc_logK_bound hN5 hX1 hX8 hδ0 hδ32 hK1 hKhi
  have hXC : X * c ≤ 6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20
      + 2 * N ^ (δ₁ / 4) * Real.log N := by
    rw [hc_def]; exact nc_XC_bound hN5 hX1 hX8 hδ0 hδ32 hθ0 hθ1 hK1 hKhi hUB0 hUBhi
  -- The arithmetic core.
  have hcore : 3000 * N * (Real.log (N + 2)) ^ 3 * (2500 * (Real.log N) ^ 2)
      * (6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N)
      ≤ 60000000 * N ^ 2 * Real.log N := nc_core_arith hN5 hδ0 hδ32 ha hb
  have hL2nn : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hUBlog : 0 ≤ Real.log (UB + 2) := Real.log_nonneg (by linarith)
  have hc_nonneg : 0 ≤ c := by rw [hc_def]; positivity
  -- Assemble the three factor bounds.
  have hAB : a * b ≤ (3000 * N * (Real.log (N + 2)) ^ 3) * (2500 * (Real.log N) ^ 2) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have hABC : a * b * (X * c)
      ≤ (3000 * N * (Real.log (N + 2)) ^ 3) * (2500 * (Real.log N) ^ 2)
      * (6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N) :=
    mul_le_mul hAB hXC (by positivity) (by positivity)
  have hmain : a * b * (X * c) ≤ 60000000 * N ^ 2 * Real.log N := le_trans hABC hcore
  -- Pull the factor `X` out of `c`.
  have hsplit : a * b * (X * c) * X⁻¹ = a * b * c := by
    have h1 : a * b * (X * c) * X⁻¹ = a * b * c * (X * X⁻¹) := by ring
    rw [h1, mul_inv_cancel₀ (ne_of_gt hXpos), mul_one]
  have hmain2 : a * b * c ≤ 60000000 * N ^ 2 * Real.log N * X⁻¹ := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_right hmain (by positivity)
  have hscale : C_H * (1 + Clat) * (a * b * c)
      ≤ C_H * (1 + Clat) * (60000000 * N ^ 2 * Real.log N * X⁻¹) :=
    mul_le_mul_of_nonneg_left hmain2 (by positivity)
  calc C_H * (1 + Clat) * a * b * c
      = C_H * (1 + Clat) * (a * b * c) := by ring
    _ ≤ C_H * (1 + Clat) * (60000000 * N ^ 2 * Real.log N * X⁻¹) := hscale
    _ = C_H * (1 + Clat) * 60000000 * X⁻¹ * N ^ 2 * Real.log N := by ring

end Work.FIArea7
