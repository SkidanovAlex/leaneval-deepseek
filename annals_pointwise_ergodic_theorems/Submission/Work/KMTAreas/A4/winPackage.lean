/-
# The smoothing-window package of the reproducing kernel `win M γ`

This module records the two facts about the normalized reproducing window
`win M γ m = M⁻¹ ψ(m/M) e(m γ)` (`ψ = lipSchPsi`) and its `ℤ`-Fourier transform
`winFT M s t = ∑_n χ (M (t - s + n))` (`χ = lipSchChi`) that the reproduction step of
Proposition `lip-2` consumes:

* **support in a single arc.**  For `M ≥ 2`, `𝓕_ℤ (win M γ)` is supported in the closed arc
  `arcSet γ (1/M)` of radius `1/M`: the summand `χ (M (t - s + n))` can be non-zero only if
  `|M (t - s + n)| < 1`, i.e. `|t - s + n| < 1/M`, which says precisely that `t` is within the
  arc of radius `1/M` of `s` *unless* it is outside the whole closed arc.  (The reproducing
  radius used by `Work.KMTAreas.A4.lip2Reproduce` is the smaller `1/(2M)`, on which `winFT = 1`;
  here we record the *support* statement, which holds on the larger closed arc.)

* **reality.**  `winFT M s t` is real, because every summand `χ (M (t - s + n))` is real
  (`χ = 𝓕⁻χ'` for the real bump `χ' = lipSchBump`, so `χ z = ((χ' z : ℝ) : ℂ)`) and `M ≠ 0`
  makes `winFT` a finite sum (`Work.KMTAreas.A4.winFT_eq_sum_Icc`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Kernel

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **The coordinate description of an arc.**  If an integer translate of `t - s` has absolute
value at most `r`, then the class of `t` lies in the closed arc of radius `r` around the class
of `s`: take `θ = t - s + n` as the offset. -/
theorem coe_mem_arcSet_of_abs_le {r t s : ℝ} (n : ℤ) (h : |t - s + (n : ℝ)| ≤ r) :
    ((t : ℝ) : FreqCircle) ∈ arcSet ((s : ℝ) : FreqCircle) r := by
  refine ⟨t - s + (n : ℝ), h, ?_⟩
  have hn0 : (((n : ℤ) : ℝ) : FreqCircle) = 0 := by
    rw [show ((n : ℤ) : ℝ) = n • (1 : ℝ) by simp]
    rw [AddCircle.coe_zsmul]
    simp [AddCircle.coe_period]
  rw [← AddCircle.coe_add, show s + (t - s + (n : ℝ)) = t + (n : ℝ) by ring,
    AddCircle.coe_add, hn0, add_zero]

/-- **The window symbol is real.**  For `M ≠ 0` the periodization
`winFT M s t = ∑_n χ (M (t - s + n))` is a finite sum of real summands, hence real. -/
theorem winFT_eq_ofReal_re {M s t : ℝ} (hM : M ≠ 0) :
    winFT M s t = ((winFT M s t).re : ℂ) := by
  have hfin : winFT M s t
      = ((∑ n ∈ Finset.Icc (-(⌈|t - s| + 1 / |M|⌉ : ℤ)) (⌈|t - s| + 1 / |M|⌉ : ℤ),
          lipSchBump (M * (t - s + n)) : ℝ) : ℂ) := by
    rw [winFT_eq_sum_Icc hM, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [lipSchChi_apply, lipSchBumpFun]
  rw [hfin]
  simp

/-- **The smoothing-window package.**
For `2 ≤ M` the reproducing window `win M s` has `ℤ`-Fourier transform supported in the closed
arc of radius `1/M` around the frequency `s`, and its symbol `winFT M s` is real-valued. -/
theorem winPackage (M s : ℝ) (hM : 2 ≤ M) :
    Work.Analysis.InverseTheory.FourierSupportIn
        (Work.KMTAreas.A4.win M ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle))
        (Work.KMTAreas.A4.arcSet ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle) (1 / M)) ∧
      (∀ t : ℝ, Work.KMTAreas.A4.winFT M s t
        = ((Work.KMTAreas.A4.winFT M s t).re : ℂ)) := by
  have hMpos : 0 < M := by linarith
  refine ⟨?_, fun t => winFT_eq_ofReal_re (ne_of_gt hMpos)⟩
  intro ξ hξ
  -- Lift the frequency to a real representative.
  obtain ⟨b, -, hb⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) ξ
  rw [← hb, winZFourier M s b hMpos]
  -- Every summand vanishes: its argument is too large.
  have hterm : ∀ n : ℤ, lipSchChi (M * (b - s + (n : ℝ))) = 0 := by
    intro n
    apply lipSchChi_eq_zero
    have hle : 1 / M ≤ |b - s + (n : ℝ)| := by
      by_contra hcon
      -- Otherwise `b` would lie in the arc, contradiction.
      have hlt : |b - s + (n : ℝ)| < 1 / M := not_le.mp hcon
      have hmem : ((b : ℝ) : FreqCircle) ∈ arcSet ((s : ℝ) : FreqCircle) (1 / M) :=
        coe_mem_arcSet_of_abs_le n (le_of_lt hlt)
      exact hξ (hb ▸ hmem)
    rw [abs_mul, abs_of_pos hMpos]
    have h1 : M * (1 / M) ≤ M * |b - s + (n : ℝ)| := mul_le_mul_of_nonneg_left hle hMpos.le
    rw [mul_one_div, div_self (ne_of_gt hMpos)] at h1
    exact h1
  show (∑' n : ℤ, lipSchChi (M * (b - s + (n : ℝ)))) = 0
  rw [tsum_congr hterm, tsum_zero]

end Work.KMTAreas.A4
