import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.chainWindowFacts
import Submission.Work.FIChain.zc_DpiC_range
import Submission.Work.FIChain.bprime_window_tail_le
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FITop.RCPrelude
import Submission.Work.FIPiChain.P2Rho.ZcExpProductLe
import Submission.Work.FIPiChain.P2Rho.ZcFloorRpowRange
import Submission.Work.FIPiChain.P2Rho.ZcLogBoundsCm

namespace Work.FIPiChain.P2Rho

theorem RhoWin2RangeCm (B B₀ : ℝ) (hB : 4 ≤ B) (hB₀ : B₀ + 5 ≤ B) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      1 ≤ Real.log (x : ℝ) ∧
      0 < Work.FIChain.zc x B ∧
      1 ≤ ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) ∧
      ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) ≤
        (Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ))) ^ (1 - (1 : ℝ) / 256) ∧
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 256) + 1 < Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) ∧
      Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B) ≤
        (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) ∧
      Real.log ((Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)) /
        (Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ))) ≤ 2 * Real.log (x : ℝ) ∧
      Real.log (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
        ≤ 2 * Real.log (x : ℝ) ∧
      Real.log ((Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)) /
        Work.FIChain.zc x B) ≤ 2 * Real.log (x : ℝ) ∧
      1 ≤ (Work.FIChain.DpiC x : ℝ) ∧
      2 ≤ Work.FIChain.Pzc x ∧
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Work.FIChain.Pzc x : ℝ) ∧
      Real.log (Work.FIChain.Pzc x : ℝ)
        ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) := by
  have hBpos : (0 : ℝ) < B := by linarith
  -- collect the eventual facts
  obtain ⟨x₁, h₁⟩ := Filter.eventually_atTop.mp (ZcLogBoundsCm B hBpos)
  obtain ⟨x₂, h₂⟩ := Filter.eventually_atTop.mp (ZcFloorRpowRange B hBpos)
  obtain ⟨x₃, h₃⟩ := Filter.eventually_atTop.mp (ZcExpProductLe B B₀ hBpos hB₀)
  obtain ⟨x₄, h₄⟩ := Filter.eventually_atTop.mp
    (Work.FIChain.window_marginsC ((1 : ℝ) / 64) B (by norm_num) (by norm_num) hBpos)
  obtain ⟨x₅, h₅⟩ := Filter.eventually_atTop.mp (Work.FIChain.scale_factsC B hBpos)
  obtain ⟨x₆, h₆⟩ := Filter.eventually_atTop.mp (Work.FITop.FI_ev_log_ge_nat 1)
  refine ⟨x₁ + x₂ + x₃ + x₄ + x₅ + x₆, fun x hx => ?_⟩
  have e₁ : x₁ ≤ x := by omega
  have e₂ : x₂ ≤ x := by omega
  have e₃ : x₃ ≤ x := by omega
  have e₄ : x₄ ≤ x := by omega
  have e₅ : x₅ ≤ x := by omega
  have e₆ : x₆ ≤ x := by omega
  obtain ⟨a₁, a₂, a₃⟩ := h₁ x e₁
  obtain ⟨b₁, b₂⟩ := h₂ x e₂
  have c₁ := h₃ x e₃
  obtain ⟨-, -, d₃, d₄, d₅, -, -⟩ := h₄ x e₄
  obtain ⟨f₁, -, -, -, -, -, -, -, -, f₁₀, -, -, -, -, -, -⟩ := h₅ x e₅
  have g₁ : (1 : ℝ) ≤ Real.log (x : ℝ) := h₆ x e₆
  -- `zc x B ≥ 256` and hence `0 < zc x B`, `1 ≤ zc x B`
  have hzc_ge : (256 : ℝ) ≤ Work.FIChain.zc x B := by
    rw [Work.FIChain.zc, Work.FIChain.Zc]
    exact_mod_cast f₁
  have hzcpos : 0 < Work.FIChain.zc x B := by linarith
  have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by linarith
  -- `1 ≤ ⌊zc^{1-η_c}⌋₊`
  have hfloor_ge : (1 : ℝ) ≤ (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ)) := by
    have h1mη : (0 : ℝ) ≤ 1 - Work.FIChain.etac := by norm_num [Work.FIChain.etac]
    have hpow : (1 : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) :=
      Real.one_le_rpow hzc1 h1mη
    have hfl : (1 : ℕ) ≤ ⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact hpow
    exact_mod_cast hfl
  -- `1 ≤ Δπ`
  have hDpi_ge : (1 : ℝ) ≤ (Work.FIChain.DpiC x : ℝ) := by
    have h : (0 : ℕ) < Work.FIChain.DpiC x := by
      rw [Work.FIChain.DpiC, Work.FIChain.Dpi]
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    have h2 : (1 : ℕ) ≤ Work.FIChain.DpiC x := by omega
    exact_mod_cast h2
  exact ⟨g₁, hzcpos, hfloor_ge, b₁, b₂, c₁, a₁, a₂, a₃, hDpi_ge, d₃, d₄, d₅⟩

end Work.FIPiChain.P2Rho
