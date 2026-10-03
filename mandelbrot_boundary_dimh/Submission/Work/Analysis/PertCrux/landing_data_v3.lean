import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.landing_data_v2

namespace Work.Analysis.PertCrux

/-- **The `f`-independent landing time `m`, with the quantitative bounds used by the assembly.**

This refines `landing_data_v2`: besides putting the ball of radius `Λ` around `τ₀ p_w` inside the
right cone at vertex `Ξ'`, the witness `m` is chosen small enough that the `O(log m)` error term is
at most `Λ / 16` and `m` itself is at most `(Ξ' + 3Λ + MK + 5CW + 2)^2 + 2`.

The witness is `m = n^2` with `n = ⌈Ξ' + Λ⌉₊`, so that `Ξ' + Λ ≤ m` and
`n + 1 ≤ Ξ' + 3Λ + MK + 5CW + 4`; the hypothesis `hΛlog` then gives

  `CW * (1 + log (m+1)) ≤ CW * (1 + 2 log (Ξ' + 3Λ + MK + 5CW + 4)) ≤ Λ / 16`,

while `m ≥ (Ξ' + Λ)^2 ≥ Λ^2 ≥ 64 Λ ≥ Ξ' + 3Λ + MK + CW * (1 + log (m+1))` places the ball in the
cone.  The pointwise estimates `‖τ₀ p_w‖ ≤ m + MK + CW (1 + log(m+1)) + 2` and
`Re τ₀ p_w ≥ m - MK - CW (1 + log(m+1))` come from `hW` and `hMK` by the triangle inequality. -/
theorem landing_data_v3 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K : Set ℂ} {Ξ' MK CW Λ : ℝ} (hΞ' : 1 ≤ Ξ') (hMK0 : 0 ≤ MK) (hCW : 0 ≤ CW)
    (hΛ16 : 64 ≤ Λ) (hΛΞ : Ξ' ≤ Λ) (hΛMK : MK ≤ Λ) (hΛCW : CW ≤ Λ)
    (hΛlog : 32 * CW * (2 + Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4)) ≤ Λ)
    (hMK : ∀ w ∈ K, ‖d.E w‖ ≤ MK)
    (hW : ∀ w ∈ K, ∀ m : ℕ,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
        ≤ CW * (1 + Real.log ((m : ℝ) + 1))) :
    ∃ m : ℕ, Ξ' + Λ ≤ (m : ℝ) ∧
      CW * (1 + Real.log ((m : ℝ) + 1)) ≤ Λ / 16 ∧
      (m : ℝ) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + 2 ∧
      (∀ w ∈ K, ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + MK + Λ + 4) ∧
      (∀ w ∈ K, ∀ z : ℂ, ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Λ →
        Ξ' + 2 * Λ ≤ z.re + |z.im|) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΞ0 : 0 ≤ Ξ' := by linarith
  -- Pointwise estimates at an arbitrary time `m`: the triangle inequality for `hW`, `hMK`.
  have key : ∀ (m : ℕ) (w : ℂ), w ∈ K →
      ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
          ≤ (m : ℝ) + MK + CW * (1 + Real.log ((m : ℝ) + 1)) + 2 ∧
      (m : ℝ) - MK - CW * (1 + Real.log ((m : ℝ) + 1))
          ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by
    intro m w hw
    have hWw := hW w hw m
    have hMKw := hMK w hw
    refine ⟨?_, ?_⟩
    · have h1 : ‖((m : ℂ)) + d.E w‖ ≤ (m : ℝ) + MK := by
        calc ‖((m : ℂ)) + d.E w‖ ≤ ‖((m : ℂ))‖ + ‖d.E w‖ := norm_add_le _ _
          _ = (m : ℝ) + ‖d.E w‖ := by rw [Complex.norm_natCast]
          _ ≤ (m : ℝ) + MK := by linarith
      calc ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
          = ‖(MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w))
              + (((m : ℂ)) + d.E w)‖ := by rw [sub_add_cancel]
        _ ≤ ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖
              + ‖((m : ℂ)) + d.E w‖ := norm_add_le _ _
        _ ≤ CW * (1 + Real.log ((m : ℝ) + 1)) + ((m : ℝ) + MK) := add_le_add hWw h1
        _ ≤ (m : ℝ) + MK + CW * (1 + Real.log ((m : ℝ) + 1)) + 2 := by linarith
    · have hEre : -MK ≤ (d.E w).re := by
        have h1 : |(d.E w).re| ≤ MK := le_trans (Complex.abs_re_le_norm _) hMKw
        linarith [neg_abs_le ((d.E w).re)]
      have hproj : (((m : ℂ)) + d.E w).re
            - ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖
          ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by
        have h : |(MandelDim.tau0 (f₀^[m] (d.φ w))).re - (((m : ℂ)) + d.E w).re|
            ≤ ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w)‖ := by
          have h2 := Complex.abs_re_le_norm
            (MandelDim.tau0 (f₀^[m] (d.φ w)) - (((m : ℂ)) + d.E w))
          simpa [Complex.sub_re] using h2
        linarith [neg_abs_le ((MandelDim.tau0 (f₀^[m] (d.φ w))).re
          - (((m : ℂ)) + d.E w).re)]
      have hx : (((m : ℂ)) + d.E w).re = (m : ℝ) + (d.E w).re := by simp
      linarith
  -- The explicit witness: `n = ⌈Ξ' + Λ⌉₊`, so that `Ξ' + Λ ≤ n < Ξ' + Λ + 1`.
  obtain ⟨n, hn, hclt⟩ : ∃ n : ℕ, Ξ' + Λ ≤ (n : ℝ) ∧ (n : ℝ) < Ξ' + Λ + 1 :=
    ⟨⌈Ξ' + Λ⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcast : (((n ^ 2 : ℕ) : ℝ)) = (n : ℝ) ^ 2 := by push_cast; ring
  -- `log (n^2 + 1) ≤ 2 log (Ξ' + 3Λ + MK + 5CW + 4)`, hence the error is at most `Λ / 16`.
  have hCWlog : CW * (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1)) ≤ Λ / 16 := by
    have hlogb : Real.log (((n ^ 2 : ℕ) : ℝ) + 1)
        ≤ 2 * Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4) := by
      rw [hcast]
      have h1 : (n : ℝ) ^ 2 + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have h2 := Real.log_le_log (by positivity) h1
      have h3 : Real.log (((n : ℝ) + 1) ^ 2) = 2 * Real.log ((n : ℝ) + 1) := by
        rw [Real.log_pow]; norm_num
      rw [h3] at h2
      have h4 : (n : ℝ) + 1 ≤ Ξ' + 3 * Λ + MK + 5 * CW + 4 := by linarith
      have h5 : Real.log ((n : ℝ) + 1) ≤ Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4) :=
        Real.log_le_log (by linarith) h4
      have h6 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      linarith
    have hstep : CW * (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1))
        ≤ CW * (1 + 2 * Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCW
    have h16 : 16 * (CW * (1 + 2 * Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4))) ≤ Λ := by
      nlinarith [hΛlog]
    linarith
  -- `m = n^2` dominates `Ξ' + 3Λ + MK + CW (1 + log (m+1))`, since `(Ξ' + Λ)^2 ≥ Λ^2 ≥ 64Λ`.
  have hΛsq : 64 * Λ ≤ Λ ^ 2 := by nlinarith [hΛ16, hΛ0]
  have hmb : Ξ' + 3 * Λ + MK + CW * (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1))
      ≤ ((n ^ 2 : ℕ) : ℝ) := by
    have hge : (Ξ' + Λ) ^ 2 ≤ ((n ^ 2 : ℕ) : ℝ) := by rw [hcast]; nlinarith [hn, hΞ0, hΛ0]
    have hge2 : Λ ^ 2 ≤ (Ξ' + Λ) ^ 2 := by nlinarith [hΞ0, hΛ0]
    have hup : Ξ' + 3 * Λ + MK + CW * (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1)) ≤ Λ ^ 2 := by
      nlinarith [hΛΞ, hΛMK, hΛsq, hCWlog, hΛ0]
    linarith [hge, hge2, hup]
  refine ⟨n ^ 2, ?_, hCWlog, ?_, ?_, ?_⟩
  · rw [hcast]; nlinarith [hn, hn0]
  · rw [hcast]
    have hS : (n : ℝ) ≤ Ξ' + 3 * Λ + MK + 5 * CW + 2 := by linarith
    have hm2 : (n : ℝ) ^ 2 ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hn0 hS
    linarith
  · intro w hw
    obtain ⟨h1, _⟩ := key (n ^ 2) w hw
    have h3 : (((n ^ 2 : ℕ) : ℝ)) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 := by
      rw [hcast]
      have hS : (n : ℝ) ≤ Ξ' + 3 * Λ + MK + 5 * CW + 2 := by linarith
      simpa [pow_two] using mul_self_le_mul_self hn0 hS
    have h4 : CW * (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1)) ≤ Λ := by linarith
    nlinarith [h1, h3, h4, hMK0, hΛ0]
  · intro w hw z hz
    obtain ⟨_, h2⟩ := key (n ^ 2) w hw
    have hzre : (MandelDim.tau0 (f₀^[n ^ 2] (d.φ w))).re - Λ ≤ z.re := by
      have h3 : |z.re - (MandelDim.tau0 (f₀^[n ^ 2] (d.φ w))).re| ≤ Λ := by
        have h5 := Complex.abs_re_le_norm (z - MandelDim.tau0 (f₀^[n ^ 2] (d.φ w)))
        have h6 : (z - MandelDim.tau0 (f₀^[n ^ 2] (d.φ w))).re
            = z.re - (MandelDim.tau0 (f₀^[n ^ 2] (d.φ w))).re := by simp
        rw [h6] at h5; exact le_trans h5 hz
      linarith [neg_abs_le (z.re - (MandelDim.tau0 (f₀^[n ^ 2] (d.φ w))).re)]
    have him : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith [hmb, hzre, him]

end Work.Analysis.PertCrux
