import Mathlib
import Submission.Work.Pert.tools
import Submission.Work.Pert.Ksub2.tauC_tau0_close_sharp

namespace Work.PertCrux

/-!
# `tauC_tau0_close_of_far`

The chart `τ_f = Work.Pert.tauC σ α` (Shishikura (A.1.5)) is compared with the unperturbed
chart `τ₀ y = -1/y` (`MandelDim.tau0`) at two points `ς`, `y` of comparable size `≳ M` that are
close (`‖ς - y‖ ≤ 2 dev`), under the normalisation `1 - σ u(0) = exp(2πiα)` of Lemma A.1.2:

  `‖τ_f(ς) - τ₀(y)‖ ≤ C · (dev/M² + ‖u(0) - 1‖/M + ‖α‖)`.

The two ingredients are

* the *sharp first-order* form `Work.Pert.Ksub2.tauC_tau0_close_sharp`, which describes
  `τ_f ∘ τ₀` near the identity in the regime `‖2πiα·(τ₀ y)‖ ≤ 1/2` — applied at the point
  `τ₀ ς`, whose `τ₀`-image is `ς` because `τ₀` is an involution (`Work.Pert.tau0_tau0`);

  `τ_f(ς) - τ₀ ς = O(‖τ₀ ς‖‖u(0)-1‖ + ‖α‖(1 + ‖τ₀ ς‖))` with `‖τ₀ ς‖ = 1/‖ς‖ ≤ 2/M`;

* the Lipschitz continuity of `τ₀` off a disc, `‖τ₀ ς - τ₀ y‖ ≤ 8 dev/M²`
  (`τ₀ ς - τ₀ y = (ς - y)/(ςy)` and `‖ς‖, ‖y‖ ≥ M/2`).

The sharp lemma's regime hypothesis `‖2πiα/τ₀ ς‖ ≤ 1/2` is *exactly* the hypothesis
`2π‖α‖‖ς‖ ≤ 1/2` supplied here, since `‖2πiα/τ₀ ς‖ = 2π‖α‖‖ς‖`. -/

theorem tauC_tau0_close_of_far :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : ℂ → ℂ} {σ α ς y : ℂ} {M dev : ℝ},
      0 < M → 1 ≤ M → 0 ≤ dev → M / 2 ≤ ‖ς‖ → M / 2 ≤ ‖y‖ → ‖ς - y‖ ≤ 2 * dev →
      2 * Real.pi * ‖α‖ * ‖ς‖ ≤ 1 / 2 →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      ‖u 0 - 1‖ ≤ 1 / 4 → ‖α‖ ≤ 1 / 4 →
      ‖Work.Pert.tauC σ α ς - MandelDim.tau0 y‖ ≤ C * (dev / (M * M) + ‖u 0 - 1‖ / M + ‖α‖) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.Pert.Ksub2.tauC_tau0_close_sharp
  refine ⟨4 * C₀ + 8, by linarith, ?_⟩
  intro u σ α ς y M dev hM0 hM1 hdev hς hy hclose hgate hnorm hα0 hu0 hα
  have hM2 : 0 < M / 2 := by linarith
  have hς0 : ς ≠ 0 := by
    intro h; rw [h, norm_zero] at hς; linarith
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  -- `τ₀ ς = -1/ς`, so its norm is `1/‖ς‖`
  have htau0n : ‖MandelDim.tau0 ς‖ = 1 / ‖ς‖ := by
    rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
  have h2M : 2 / M ≤ 2 := by rw [div_le_iff₀ hM0]; linarith
  have htau0le : ‖MandelDim.tau0 ς‖ ≤ 2 / M := by
    rw [htau0n]
    calc 1 / ‖ς‖ ≤ 1 / (M / 2) := one_div_le_one_div_of_le hM2 hς
      _ = 2 / M := by rw [one_div, inv_div]
  -- the regime hypothesis of the sharp lemma, `‖2πiα/τ₀ ς‖ = 2π‖α‖‖ς‖`
  have hwn : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hgate' : ‖2 * Real.pi * Complex.I * α / MandelDim.tau0 ς‖ ≤ 1 / 2 := by
    rw [norm_div, hwn, htau0n]
    have h : (2 * Real.pi * ‖α‖) / (1 / ‖ς‖) = 2 * Real.pi * ‖α‖ * ‖ς‖ := by
      rw [div_eq_mul_inv, inv_div]; ring
    rw [h]
    exact hgate
  -- the sharp lemma applied at `y := τ₀ ς`, whose `τ₀`-image is `ς`
  have h1raw := hC₀ (u := u) (σ := σ) (α := α) (y := MandelDim.tau0 ς)
    hnorm hα0 hu0 hα hgate'
  rw [Work.Pert.tau0_tau0] at h1raw
  have h1 : ‖Work.Pert.tauC σ α ς - MandelDim.tau0 ς‖
      ≤ C₀ * (2 * (‖u 0 - 1‖ / M) + 3 * ‖α‖) := by
    refine le_trans h1raw (mul_le_mul_of_nonneg_left ?_ hC₀pos.le)
    have hb1 : ‖MandelDim.tau0 ς‖ * ‖u 0 - 1‖ ≤ 2 * (‖u 0 - 1‖ / M) := by
      have h := mul_le_mul_of_nonneg_right htau0le (norm_nonneg (u 0 - 1))
      calc ‖MandelDim.tau0 ς‖ * ‖u 0 - 1‖ ≤ (2 / M) * ‖u 0 - 1‖ := h
        _ = 2 * (‖u 0 - 1‖ / M) := by ring
    have hb3 : ‖α‖ * (1 + ‖MandelDim.tau0 ς‖) ≤ 3 * ‖α‖ := by
      have h2 : 1 + ‖MandelDim.tau0 ς‖ ≤ 3 := by linarith
      calc ‖α‖ * (1 + ‖MandelDim.tau0 ς‖) ≤ ‖α‖ * 3 :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg α)
        _ = 3 * ‖α‖ := by ring
    linarith [hb1, hb3]
  -- Lipschitz continuity of `τ₀` off the disc of radius `M/2`
  have htau0diff : MandelDim.tau0 ς - MandelDim.tau0 y = (ς - y) / (ς * y) := by
    rw [MandelDim.tau0, MandelDim.tau0]
    field_simp
    ring
  have h2 : ‖MandelDim.tau0 ς - MandelDim.tau0 y‖ ≤ 8 * dev / (M * M) := by
    rw [htau0diff, norm_div, norm_mul]
    have hden_pos : (0:ℝ) < (M / 2) * (M / 2) := mul_pos hM2 hM2
    have hden_le : (M / 2) * (M / 2) ≤ ‖ς‖ * ‖y‖ := by nlinarith [hς, hy]
    have hstep : ‖ς - y‖ / (‖ς‖ * ‖y‖) ≤ (2 * dev) / ((M / 2) * (M / 2)) :=
      div_le_div₀ (by linarith) hclose hden_pos hden_le
    have heq : (2 * dev) / ((M / 2) * (M / 2)) = 8 * dev / (M * M) := by
      have hMne : M ≠ 0 := ne_of_gt hM0
      field_simp
      ring
    linarith [hstep, heq.le, heq.ge]
  have h2' : ‖MandelDim.tau0 ς - MandelDim.tau0 y‖ ≤ 8 * (dev / (M * M)) := by
    rw [show (8:ℝ) * (dev / (M * M)) = 8 * dev / (M * M) from by ring]
    exact h2
  -- assemble
  have hsplit : Work.Pert.tauC σ α ς - MandelDim.tau0 y
      = (Work.Pert.tauC σ α ς - MandelDim.tau0 ς) + (MandelDim.tau0 ς - MandelDim.tau0 y) := by ring
  rw [hsplit]
  have hd1 : 0 ≤ dev / (M * M) := div_nonneg hdev (by positivity)
  have hd2 : 0 ≤ ‖u 0 - 1‖ / M := div_nonneg (norm_nonneg _) hM0.le
  have hd3 : 0 ≤ ‖α‖ := norm_nonneg _
  have hca : 0 ≤ C₀ * (dev / (M * M)) := mul_nonneg hC₀pos.le hd1
  have haa : 0 ≤ C₀ * (‖u 0 - 1‖ / M) := mul_nonneg hC₀pos.le hd2
  have hba : 0 ≤ C₀ * ‖α‖ := mul_nonneg hC₀pos.le hd3
  calc ‖(Work.Pert.tauC σ α ς - MandelDim.tau0 ς) + (MandelDim.tau0 ς - MandelDim.tau0 y)‖
      ≤ ‖Work.Pert.tauC σ α ς - MandelDim.tau0 ς‖ + ‖MandelDim.tau0 ς - MandelDim.tau0 y‖ :=
        norm_add_le _ _
    _ ≤ (4 * C₀ + 8) * (dev / (M * M) + ‖u 0 - 1‖ / M + ‖α‖) := by
        nlinarith [h1, h2', hd1, hd2, hd3, hca, haa, hba]

end Work.PertCrux
