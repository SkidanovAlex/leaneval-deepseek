import Mathlib
import Submission.Work.Smooth.Morse.Flow

namespace Work.BoxShrink.Bubble.Smooth

/-- **A critical-value-free window around a regular value.**

If the critical values of `hh|_F` are locally finite and `0` is a regular value, then `0` is
contained in a closed interval `[a,b]` with `a < 0 < b` on which *every* level is regular.

Indeed `criticalValues ψ hh ∩ [-1,1]` is finite and does not contain `0`; a finite set is closed,
so its complement is a neighbourhood of `0`, say of radius `ε > 0`.  Taking
`a = -min ε 1 / 2`, `b = min ε 1 / 2`, every `t ∈ [a,b]` satisfies `|t| < ε` (hence `t` is not a
critical value) and `|t| < 1` (hence, were `t` a critical value, it would lie in
`criticalValues ψ hh ∩ [-1,1]`, a contradiction). -/
theorem criticalFreeWindow {ψ : Submission.Diffeo} {hh : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ}
    (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ hh)
    (h0 : Work.Smooth.Morse.IsRegularValue ψ hh 0) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      (∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ hh t) := by
  have hfin : (Work.Smooth.Morse.criticalValues ψ hh ∩ Set.Icc (-1:ℝ) 1).Finite :=
    hcrit (-1) 1
  have h0' : (0:ℝ) ∉ Work.Smooth.Morse.criticalValues ψ hh ∩ Set.Icc (-1:ℝ) 1 :=
    fun h => h0 h.1
  have hopen : IsOpen (Work.Smooth.Morse.criticalValues ψ hh ∩ Set.Icc (-1:ℝ) 1)ᶜ :=
    hfin.isClosed.isOpen_compl
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa using h0')
  have hm : 0 < min ε 1 := lt_min hεpos one_pos
  refine ⟨-(min ε 1)/2, (min ε 1)/2, by linarith, by linarith, ?_⟩
  intro t ht
  have ht_abs_le : |t| ≤ min ε 1 / 2 := by
    rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht_lt_eps : |t| < ε := by
    have h1 : min ε 1 / 2 < min ε 1 := by linarith
    have h2 : min ε 1 ≤ ε := min_le_left ε 1
    linarith
  have ht_lt_one : |t| < 1 := by
    have h1 : min ε 1 / 2 < min ε 1 := by linarith
    have h2 : min ε 1 ≤ 1 := min_le_right ε 1
    linarith
  have ht_notin : t ∉ Work.Smooth.Morse.criticalValues ψ hh ∩ Set.Icc (-1:ℝ) 1 := by
    have hb : t ∈ (Work.Smooth.Morse.criticalValues ψ hh ∩ Set.Icc (-1:ℝ) 1)ᶜ :=
      hball (by simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using ht_lt_eps)
    simpa using hb
  intro htc
  exact ht_notin ⟨htc, by
    rw [abs_lt] at ht_lt_one
    exact ⟨le_of_lt ht_lt_one.1, le_of_lt ht_lt_one.2⟩⟩

end Work.BoxShrink.Bubble.Smooth
