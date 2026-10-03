import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Analysis.PertCrux

/-- **Growth of `m - CW * log(m+1)`.**  For nonnegative constants `C`, `CW` there is a natural
number `m` with `C + CW * (1 + log (m+1)) ≤ m`.  (Used to produce the landing time: the `O(log m)`
error of the Fatou-coordinate expansion is eventually dominated by `m` itself.)

The witness is explicit, `m = n^2` for any `n ≥ C + 5 * CW + 1`; the estimate
`log (n^2 + 1) ≤ 2 (n+1)` comes from `log x ≤ x` applied to `(n+1)^2 ≥ n^2 + 1`. -/
lemma exists_nat_ge_add_mul_log {C CW : ℝ} (hC : 0 ≤ C) (hCW : 0 ≤ CW) :
    ∃ m : ℕ, C + CW * (1 + Real.log ((m : ℝ) + 1)) ≤ (m : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (C + 5 * CW + 1)
  refine ⟨n ^ 2, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  have hlog : Real.log ((n : ℝ) ^ 2 + 1) ≤ 2 * ((n : ℝ) + 1) := by
    have hle : (n : ℝ) ^ 2 + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have h1 : Real.log ((n : ℝ) ^ 2 + 1) ≤ Real.log (((n : ℝ) + 1) ^ 2) :=
      Real.log_le_log (by positivity) hle
    have h2 : Real.log (((n : ℝ) + 1) ^ 2) = 2 * Real.log ((n : ℝ) + 1) := by
      rw [Real.log_pow]; push_cast; ring
    rw [h2] at h1
    have h3 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := Real.log_le_self (by linarith)
    linarith
  have hmain : C + CW * (2 * ((n : ℝ) + 1) + 1) ≤ (n : ℝ) ^ 2 := by
    nlinarith [hn, hC, hCW, hn1, hn0]
  nlinarith [hlog, hCW, hmain]

/-- **The `f`-independent landing time `m`, in the form needed by the perturbation assembly.**
Given the datum's bound `‖d.E w‖ ≤ MK` on `K` and the `O(log m)` location
`‖τ₀ p_w - (m + d.E w)‖ ≤ CW * (1 + log (m+1))` of `τ₀ p_w = τ₀ (f₀^[m] (d.φ w))` from the
Fatou-coordinate expansion, there is a single `m : ℕ` (depending only on `Ξ'`, `MK`, `CW`, `Λ`)
such that

* `m ≥ Ξ' + Λ`,
* `‖τ₀ p_w‖ ≤ m + MK + CW * (1 + log (m+1)) + 2` for every `w ∈ K`, and
* the closed ball of radius `Λ` around each `τ₀ p_w` lies in the right cone with vertex `Ξ'`,
  `Ξ' + 2Λ ≤ Re z + |Im z|`.

Indeed `Re τ₀ p_w ≥ m - MK - CW (1 + log(m+1))`, so it suffices to take
`m ≥ Ξ' + 3Λ + MK + CW (1 + log (m+1))`, which `exists_nat_ge_add_mul_log` provides. -/
theorem landing_data_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K : Set ℂ} {Ξ' MK CW Λ : ℝ} (hΞ' : 1 ≤ Ξ') (hMK0 : 0 ≤ MK) (hCW : 0 ≤ CW) (hΛ : 0 ≤ Λ)
    (hMK : ∀ w ∈ K, ‖d.E w‖ ≤ MK)
    (hW : ∀ w ∈ K, ∀ m : ℕ,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
        ≤ CW * (1 + Real.log ((m : ℝ) + 1))) :
    ∃ m : ℕ, Ξ' + Λ ≤ (m : ℝ) ∧
      (∀ w ∈ K, ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ (m : ℝ) + MK + CW * (1 + Real.log ((m : ℝ) + 1)) + 2) ∧
      (∀ w ∈ K, ∀ z : ℂ, ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Λ →
        Ξ' + 2 * Λ ≤ z.re + |z.im|) := by
  obtain ⟨m, hm⟩ := exists_nat_ge_add_mul_log (C := Ξ' + 3 * Λ + MK) (CW := CW)
    (by linarith) hCW
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hWlog : 0 ≤ CW * (1 + Real.log ((m : ℝ) + 1)) := mul_nonneg hCW (by linarith)
  refine ⟨m, by linarith, ?_, ?_⟩
  · intro w hw
    have hWw := hW w hw m
    have hMKw := hMK w hw
    have h1 : ‖((m : ℂ)) + d.E w‖ ≤ (m : ℝ) + MK := by
      calc ‖((m : ℂ)) + d.E w‖ ≤ ‖((m : ℂ))‖ + ‖d.E w‖ := norm_add_le _ _
        _ = (m : ℝ) + ‖d.E w‖ := by rw [Complex.norm_natCast]
        _ ≤ (m : ℝ) + MK := by linarith
    calc ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
        = ‖(MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w))
            + (((m : ℂ)) + d.E w)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖
            + ‖((m : ℂ)) + d.E w‖ :=
          norm_add_le _ _
      _ ≤ CW * (1 + Real.log ((m : ℝ) + 1)) + ((m : ℝ) + MK) := add_le_add hWw h1
      _ ≤ (m : ℝ) + MK + CW * (1 + Real.log ((m : ℝ) + 1)) + 2 := by linarith
  · intro w hw z hz
    have hWw := hW w hw m
    have hMKw := hMK w hw
    have hEre : -MK ≤ (d.E w).re := by
      have h1 : |(d.E w).re| ≤ MK := le_trans (Complex.abs_re_le_norm _) hMKw
      linarith [neg_abs_le ((d.E w).re)]
    have hre : (m : ℝ) - MK - CW * (1 + Real.log ((m : ℝ) + 1))
        ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by
      have hb : (((m : ℂ)) + d.E w).re
          - ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖
          ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by
        have h : |(MandelDim.tau0 (f₀^[m] (d.φ w))).re - (((m : ℂ)) + d.E w).re|
            ≤ ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖ := by
          have := Complex.abs_re_le_norm
            (MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w))
          simpa [Complex.sub_re] using this
        linarith [neg_abs_le ((MandelDim.tau0 (f₀^[m] (d.φ w))).re
          - (((m : ℂ)) + d.E w).re)]
      have hx : (((m : ℂ)) + d.E w).re = (m : ℝ) + (d.E w).re := by simp
      linarith
    have hzre : (MandelDim.tau0 (f₀^[m] (d.φ w))).re - Λ ≤ z.re := by
      have h1 : |z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re| ≤ Λ := by
        have h2 := Complex.abs_re_le_norm (z - MandelDim.tau0 (f₀^[m] (d.φ w)))
        have h3 : (z - MandelDim.tau0 (f₀^[m] (d.φ w))).re
            = z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by simp
        rw [h3] at h2
        exact le_trans h2 hz
      linarith [neg_abs_le (z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re)]
    have him : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith

end Work.Analysis.PertCrux
