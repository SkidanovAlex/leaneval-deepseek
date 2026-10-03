import Mathlib
import Submission.Work.FIArea7.SepBump
import Submission.Work.FIArea7.SepK
import Submission.Work.FIArea7.SepArith
import Submission.Work.FIArea7.FourierL1
import Submission.Work.FIArea7.FourierIdentity

/-!
# `Work.FIArea7.exists_separating_function` — *FI* Lemma 26.1

For `x ≥ 1` there is an `L¹` function `h : ℝ → ℝ` with `∫ |h| < log 6x` such that
`∫ h(t) k^{it} dt = 1` for every positive integer `k ≤ x` and `= 0` for `k > x`.

The construction: put `M = ⌊x⌋`, `λ = (log M + log(M+1))/(4π)`, `ε = (log(M+1) - log M)/(4π)`,
let `K = sepK λ ε` be the smooth trapezoid which is `1` on `[-λ+ε, λ-ε]` and `0` outside
`[-λ-ε, λ+ε]` (built in `SepBump`/`SepK`), and take `h` to be the real part of the Fourier
transform of `K`.  Then `∫ h(t) k^{it} dt = K(log k / 2π)` by Fourier inversion
(`FourierIdentity`), which is `1` for `k ≤ M` and `0` for `k ≥ M+1`; and
`∫|h| ≤ (2/π)(2 + log(16λ/(15ε))) < log 6x` (`FourierL1` and `SepArith`).
-/

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology FourierTransform

noncomputable section

/-- **DFI Lemma 9 = *FI* Lemma 26.1: the separating function for `mn ≤ x`.**  For `x ≥ 1` there is
an `L¹` function `h : ℝ → ℝ` with `∫_ℝ |h(t)| dt < log 6x` and, for every positive integer `k`,

  `∫_ℝ h(t)·k^{it} dt = 1` if `k ≤ x`, and `0` otherwise. -/
theorem exists_separating_function (x : ℝ) (hx : 1 ≤ x) :
    ∃ h : ℝ → ℝ, (∫ t : ℝ, |h t|) < Real.log (6 * x) ∧
      ∀ k : ℕ, 1 ≤ k →
        (∫ t : ℝ, (h t : ℂ) * (k : ℂ) ^ (t * Complex.I)) = if (k : ℝ) ≤ x then 1 else 0 := by
  set M : ℕ := ⌊x⌋₊ with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.le_floor (by exact_mod_cast hx)
  have hMx : (M : ℝ) ≤ x := by
    rw [hMdef]
    exact Nat.floor_le (by linarith)
  refine ⟨fun t => ((FourierTransform.fourier
    (fun y : ℝ => (sepK (sepLam M) (sepEps M) y : ℂ)) t).re), ?_, ?_⟩
  · have h1 := FourierL1 (sepLam M) (sepEps M) (sepEps_pos hM1) (sepEps_le_sepLam hM1)
    have h2 := SepArith M hM1
    have h3 : Real.log (6 * (M:ℝ)) ≤ Real.log (6 * x) := by
      apply Real.log_le_log (by positivity)
      linarith
    linarith
  · intro k hk
    rw [FourierIdentity (sepLam M) (sepEps M) (sepEps_pos hM1) (sepEps_le_sepLam hM1) k hk]
    rcases le_or_gt (k : ℝ) x with hkx | hkx
    · have hkM : k ≤ M := by
        rw [hMdef]
        exact Nat.le_floor hkx
      rw [sepK_sepLam_sepEps_of_le hM1 hk hkM, if_pos hkx]
      norm_num
    · have hMk : M + 1 ≤ k := by
        by_contra h
        push Not at h
        have : (k : ℝ) ≤ x := by
          calc (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : k ≤ M)
            _ ≤ x := hMx
        linarith
      rw [sepK_sepLam_sepEps_of_lt hM1 hMk, if_neg (not_le.mpr hkx)]
      norm_num

end

end Work.FIArea7
