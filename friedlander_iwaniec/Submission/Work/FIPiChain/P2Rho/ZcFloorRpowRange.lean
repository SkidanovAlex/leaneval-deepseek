import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_DpiC_range

namespace Work.FIPiChain.P2Rho

theorem ZcFloorRpowRange (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) ≤
        (Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ))) ^ (1 - (1 : ℝ) / 256) ∧
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 256) + 1 <
        Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) := by
  -- `zc_DpiC_range` is stated for `0 < η < 1/32`; we instantiate it at `η = 1/64`,
  -- for which `1 - η = 1 - 1/64` and `1 - η/4 = 1 - 1/256`, `1/4 + η/4 = 1/4 + 1/256`.
  have hη : (0 : ℝ) < 1 / 64 := by norm_num
  have hη16 : (1 / 64 : ℝ) < 1 / 32 := by norm_num
  have hmain := Work.FIChain.zc_DpiC_range (1 / 64) hη hη16 B hB
  filter_upwards [hmain] with x hx
  obtain ⟨_hdpi, hfloor, hlow⟩ := hx
  rw [show (1 : ℝ) / 64 / 4 = 1 / 256 by norm_num] at hfloor hlow
  -- `DpiC x ≥ 1`
  have hDpiCpos : 0 < Work.FIChain.DpiC x := by
    rw [Work.FIChain.DpiC, Work.FIChain.Dpi]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hdpi1 : (1 : ℝ) ≤ (Work.FIChain.DpiC x : ℝ) := by exact_mod_cast hDpiCpos
  have hdpos : (0 : ℝ) < (Work.FIChain.DpiC x : ℝ) := by exact_mod_cast hDpiCpos
  -- the third range fact gives `zc/DpiC > 1`, hence `zc ≥ 1`
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hlt1 : (1 : ℝ) < Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) := by
    have h0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 256) := Real.rpow_nonneg hxnn _
    linarith
  have hzc1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
    have h := (lt_div_iff₀ hdpos).mp hlt1
    linarith
  refine ⟨?_, hlow⟩
  -- `zc^{1-etac} ≤ zc^{1-1/64}` since `etac = 1/32 < 1/64` and `zc ≥ 1`
  have hexp : (1 - Work.FIChain.etac : ℝ) ≤ 1 - (1 : ℝ) / 64 := by
    rw [Work.FIChain.etac]; norm_num
  have hrpow : (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)
      ≤ (Work.FIChain.zc x B) ^ (1 - (1 : ℝ) / 64) :=
    Real.rpow_le_rpow_of_exponent_le hzc1 hexp
  have hmono := Nat.floor_mono hrpow
  exact le_trans (by exact_mod_cast hmono) hfloor

end Work.FIPiChain.P2Rho
