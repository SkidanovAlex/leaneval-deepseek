import Mathlib
import Submission.Work.FIArea6V.CleanVDefs
import Submission.Work.FIArea6Road.TailLogNStep
import Submission.Work.FIArea6Road.sum_tau_sq_window_le
import Submission.Work.FIArea6.TauCore.tau_window_tau_sq_le
import Submission.Work.FIArea6.TauCore.params_caseB_bounds

namespace Work.FIArea6V

/-- Pure arithmetic core of `S16CleanTailArithSmallTheta`.

Given the uniform window bound `W ≤ 8·C₀·(θN+1)·L³ + 4·C₀·(2N)^{3/4}·L²`
(`tau_window_tau_sq_le`), the small-θ hypothesis `θ ≤ S·L³` (`S = e^{-√L/4}`, the exponential
slot `L = log N`), and the two elementary lower bounds `1 ≤ S·N·L³`, `2 ≤ S·N^{1/4}·L⁴` (both
automatic once `N ≥ e^{25}`), the trivial Fourier mass `10⁷·(4W)` is dominated by
`10⁹·C₀·S·N·L⁶`: the three terms `θNL³`, `L³`, `(2N)^{3/4}L²` are each absorbed into
`S·N·L⁶`, the last one using `(2N)^{3/4}L² = 2^{3/4}·(N^{3/4}L²)` with `N^{3/4} = N/N^{1/4}`
and the gain `2 ≤ S·N^{1/4}L⁴ ≥ 2^{3/4}`. -/
private lemma smallTheta_tail_arith (C0 N L θ S W : ℝ) (hC0 : 0 < C0) (hS : 0 < S)
    (hN : 0 < N) (hL : 1 ≤ L)
    (hθS : θ ≤ S * L ^ 3) (hSNL3 : 1 ≤ S * N * L ^ 3)
    (hSNL4 : 2 ≤ S * N ^ ((1 : ℝ) / 4) * L ^ 4)
    (hW : W ≤ 8 * C0 * (θ * N + 1) * L ^ 3 + 4 * C0 * (2 * N) ^ ((3 : ℝ) / 4) * L ^ 2) :
    10000000 * (4 * W) ≤ (10 : ℝ) ^ (9 : ℕ) * C0 * S * N * L ^ (6 : ℕ) := by
  have hC0nn : (0 : ℝ) ≤ C0 := le_of_lt hC0
  have hNnn : (0 : ℝ) ≤ N := le_of_lt hN
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hL3nn : (0 : ℝ) ≤ L ^ 3 := by positivity
  have hL2nn : (0 : ℝ) ≤ L ^ 2 := by positivity
  -- the three core inequalities, each `≤ S·N·L⁶`
  have cA : θ * N * L ^ 3 ≤ S * N * L ^ 6 := by
    have h1 : θ * N ≤ (S * L ^ 3) * N := mul_le_mul_of_nonneg_right hθS hNnn
    have h2 : (θ * N) * L ^ 3 ≤ ((S * L ^ 3) * N) * L ^ 3 :=
      mul_le_mul_of_nonneg_right h1 hL3nn
    have h3 : ((S * L ^ 3) * N) * L ^ 3 = S * N * L ^ 6 := by ring
    linarith [h2, h3.le, h3.ge]
  have cB : L ^ 3 ≤ S * N * L ^ 6 := by
    have h2 : 1 * L ^ 3 ≤ (S * N * L ^ 3) * L ^ 3 := mul_le_mul_of_nonneg_right hSNL3 hL3nn
    have h3 : (S * N * L ^ 3) * L ^ 3 = S * N * L ^ 6 := by ring
    linarith [h2, h3.le, h3.ge]
  have cC : (2 * N) ^ ((3 : ℝ) / 4) * L ^ 2 ≤ S * N * L ^ 6 := by
    have h23 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hN34nn : (0 : ℝ) ≤ N ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hNnn _
    have hstep1 : (2 * N) ^ ((3 : ℝ) / 4) * L ^ 2
        = (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
      rw [Real.mul_rpow (by norm_num) hNnn]
    have hstep2 : (2 : ℝ) ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) * L ^ 2
        ≤ 2 * N ^ ((3 : ℝ) / 4) * L ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hL2nn
      exact mul_le_mul_of_nonneg_right h23 hN34nn
    have hstep3 : 2 * N ^ ((3 : ℝ) / 4) * L ^ 2
        ≤ (S * N ^ ((1 : ℝ) / 4) * L ^ 4) * (N ^ ((3 : ℝ) / 4) * L ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hSNL4 (mul_nonneg hN34nn hL2nn)
      linarith [h]
    have hstep4 : (S * N ^ ((1 : ℝ) / 4) * L ^ 4) * (N ^ ((3 : ℝ) / 4) * L ^ 2)
        = S * N * L ^ 6 := by
      have h1 : N ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) = N := by
        rw [← Real.rpow_add hN]; norm_num
      have h2 : L ^ 4 * L ^ 2 = L ^ 6 := by ring
      rw [show (S * N ^ ((1 : ℝ) / 4) * L ^ 4) * (N ^ ((3 : ℝ) / 4) * L ^ 2)
            = S * (N ^ ((1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) * (L ^ 4 * L ^ 2) by ring, h1, h2]
    linarith [hstep1.le, hstep1.ge, hstep2, hstep3, hstep4.le, hstep4.ge]
  -- combine
  have hW' := mul_le_mul_of_nonneg_left hW (by norm_num : (0 : ℝ) ≤ 10000000 * 4)
  have eA : 10000000 * 4 * (8 * C0 * (θ * N + 1) * L ^ 3)
      = 320000000 * C0 * (θ * N * L ^ 3) + 320000000 * C0 * L ^ 3 := by ring
  have eC : 10000000 * 4 * (4 * C0 * (2 * N) ^ ((3 : ℝ) / 4) * L ^ 2)
      = 160000000 * C0 * ((2 * N) ^ ((3 : ℝ) / 4) * L ^ 2) := by ring
  have hA2 : 320000000 * C0 * (θ * N * L ^ 3) ≤ 320000000 * C0 * (S * N * L ^ 6) :=
    mul_le_mul_of_nonneg_left cA (by positivity)
  have hB2 : 320000000 * C0 * L ^ 3 ≤ 320000000 * C0 * (S * N * L ^ 6) :=
    mul_le_mul_of_nonneg_left cB (by positivity)
  have hC2 : 160000000 * C0 * ((2 * N) ^ ((3 : ℝ) / 4) * L ^ 2)
      ≤ 160000000 * C0 * (S * N * L ^ 6) :=
    mul_le_mul_of_nonneg_left cC (by positivity)
  have hS6nn : (0 : ℝ) ≤ C0 * (S * N * L ^ 6) := by positivity
  have hsum : 320000000 * C0 * (S * N * L ^ 6) + 320000000 * C0 * (S * N * L ^ 6)
      + 160000000 * C0 * (S * N * L ^ 6) = 800000000 * (C0 * (S * N * L ^ 6)) := by ring
  have hfin : 800000000 * (C0 * (S * N * L ^ 6)) ≤ (10 : ℝ) ^ (9 : ℕ) * C0 * S * N * L ^ 6 := by
    have h10 : (800000000 : ℝ) ≤ 10 ^ 9 := by norm_num
    have := mul_le_mul_of_nonneg_right h10 hS6nn
    nlinarith [this]
  have hgoal : 10000000 * (4 * W) = 10000000 * 4 * W := by ring
  rw [hgoal] at *
  nlinarith [hW', eA, eC, hA2, hB2, hC2, hsum, hfin, hS6nn]

/-- Arithmetic of the tail in the regime `θ ≤ exp(-(√log N)/4)·(log N)^3`: the trivial
(no-cancellation) Fourier-frequency tail, i.e. the total Fourier mass `10^7` times the norm-window
mass `4·winTauSq Pa` (`winTauSq` is the window `Σ_{⌊N⌋+1 ≤ n ≤ ⌊(1+θ)N⌋} τ(n)²`), is dominated by
the target's exponential slot `exp(-(√log N)/4)·N·(log N)^6`.

Route: `Work.FIArea6Road.sum_tau_sq_window_le` gives
`winTauSq ≤ C((M-N+1)(log(M+2))^3 + M^{3/4}(log(M+2))^2)` with `M ≤ (1+θ)N`, whence
`winTauSq ≤ C'((θN+2)(log N)^3 + (2N)^{3/4}(log N)^2)`; each of the three resulting terms is
`≤ (const)·exp(-(√log N)/4)·N·(log N)^6` for `N` large, using only `θ ≤ exp(-(√log N)/4)(log N)^3`
and `N → ∞`.  The thresholds are uniform in all the parameters of `Pa`, since the only asymptotic
input is `log N ≥ (1/4)log x` (`Work.FIArea6Road.TailLogNStep`) and `e^{3v/4}v^3 → ∞`. -/
theorem S16CleanTailArithSmallTheta :
    ∃ CT x0 : ℝ, 0 < CT ∧ 0 < x0 ∧ ∀ Pa : Work.FITop.Params, x0 ≤ (Pa.x : ℝ) →
      Pa.θ ≤ Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * (Real.log Pa.N) ^ (3 : ℕ) →
      10000000 * (4 * Work.FIArea6V.winTauSq Pa)
        ≤ CT * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
            * (Real.log Pa.N) ^ (6 : ℕ) := by
  obtain ⟨C0, hC0pos, hC0b⟩ := Work.FIArea6Road.sum_tau_sq_window_le
  refine ⟨(10 : ℝ) ^ (9 : ℕ) * C0, Real.exp 100, by positivity, Real.exp_pos 100, ?_⟩
  intro Pa hx hθsmall
  -- `x ≥ e^100 ≥ e^8`, so the case-B parameter bounds apply.
  have hx8 : Real.exp 8 ≤ (Pa.x : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  obtain ⟨hlogN1, hN3, hθ1⟩ := Work.FIArea6.TauCore.params_caseB_bounds Pa hx8
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hlogx100 : (100 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 100) hx
    rwa [Real.log_exp] at h
  have hL25 : (25 : ℝ) < Real.log Pa.N := by
    have := Work.FIArea6Road.TailLogNStep Pa
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N := by linarith
  -- the uniform window bound, in the form consumed by the arithmetic core
  have hW : Work.FIArea6V.winTauSq Pa
      ≤ 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ)
        + 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) :=
    Work.FIArea6.TauCore.tau_window_tau_sq_le C0 hC0pos hC0b Pa Pa.hN1 hN3 Pa.hθ0 hθ1
  have hLnn : (0 : ℝ) ≤ Real.log Pa.N := by linarith
  have hsqrtL_le : Real.sqrt (Real.log Pa.N) ≤ Real.log Pa.N := by
    rw [Real.sqrt_le_iff]
    exact ⟨hLnn, by nlinarith⟩
  -- the two elementary lower bounds on the exponential slot
  have hSNL3 : 1
      ≤ Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
    have hL3 : (1 : ℝ) ≤ (Real.log Pa.N) ^ (3 : ℕ) := one_le_pow₀ hL1
    have hsub : (0 : ℝ) ≤ Real.log Pa.N - Real.sqrt (Real.log Pa.N) / 4 := by linarith
    have hexp1 : (1 : ℝ) ≤ Real.exp (Real.log Pa.N - Real.sqrt (Real.log Pa.N) / 4) :=
      Real.one_le_exp hsub
    have hmain : (1 : ℝ)
        ≤ Real.exp (Real.log Pa.N - Real.sqrt (Real.log Pa.N) / 4) * (Real.log Pa.N) ^ (3 : ℕ) :=
      by nlinarith [mul_le_mul hexp1 hL3 (by norm_num) (by linarith)]
    have hmul : Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Real.exp (Real.log Pa.N)
        = Real.exp (Real.log Pa.N - Real.sqrt (Real.log Pa.N) / 4) := by
      rw [← Real.exp_add]; ring_nf
    calc (1 : ℝ)
        ≤ Real.exp (Real.log Pa.N - Real.sqrt (Real.log Pa.N) / 4) * (Real.log Pa.N) ^ (3 : ℕ) :=
          hmain
      _ = Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Real.exp (Real.log Pa.N)
            * (Real.log Pa.N) ^ (3 : ℕ) := by rw [hmul]
      _ = Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
          rw [Real.exp_log hNpos]
  have hSNL4 : 2
      ≤ Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N ^ ((1 : ℝ) / 4)
          * (Real.log Pa.N) ^ (4 : ℕ) := by
    have hL4 : (2 : ℝ) ≤ (Real.log Pa.N) ^ (4 : ℕ) := by
      have h25 : (25 : ℝ) ^ (4 : ℕ) ≤ (Real.log Pa.N) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt hL25) 4
      norm_num at h25; linarith
    have hsub : (0 : ℝ) ≤ Real.log Pa.N / 4 - Real.sqrt (Real.log Pa.N) / 4 := by linarith
    have hexp2 : (1 : ℝ) ≤ Real.exp (Real.log Pa.N / 4 - Real.sqrt (Real.log Pa.N) / 4) :=
      Real.one_le_exp hsub
    have hmain : (2 : ℝ)
        ≤ Real.exp (Real.log Pa.N / 4 - Real.sqrt (Real.log Pa.N) / 4)
            * (Real.log Pa.N) ^ (4 : ℕ) :=
      by nlinarith [mul_le_mul hexp2 hL4 (by norm_num) (by linarith)]
    have hmul : Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Real.exp (Real.log Pa.N / 4)
        = Real.exp (Real.log Pa.N / 4 - Real.sqrt (Real.log Pa.N) / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hrpow : Pa.N ^ ((1 : ℝ) / 4) = Real.exp (Real.log Pa.N / 4) := by
      rw [Real.rpow_def_of_pos hNpos,
        show Real.log Pa.N * ((1 : ℝ) / 4) = Real.log Pa.N / 4 by ring]
    calc (2 : ℝ)
        ≤ Real.exp (Real.log Pa.N / 4 - Real.sqrt (Real.log Pa.N) / 4)
            * (Real.log Pa.N) ^ (4 : ℕ) := hmain
      _ = Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Real.exp (Real.log Pa.N / 4)
            * (Real.log Pa.N) ^ (4 : ℕ) := by rw [hmul]
      _ = Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N ^ ((1 : ℝ) / 4)
            * (Real.log Pa.N) ^ (4 : ℕ) := by rw [hrpow]
  exact smallTheta_tail_arith C0 Pa.N (Real.log Pa.N) Pa.θ
    (Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))) (Work.FIArea6V.winTauSq Pa)
    hC0pos (Real.exp_pos _) hNpos hL1 hθsmall hSNL3 hSNL4 hW

end Work.FIArea6V
