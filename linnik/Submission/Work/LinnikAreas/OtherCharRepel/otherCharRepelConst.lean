import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.dhApply85
import Submission.Work.LinnikAreas.OtherCharRepel.designatedTrichotomy
import Submission.Work.LinnikAreas.OtherCharRepel.sameCharNonRealRepel
import Submission.Work.LinnikAreas.OtherCharRepel.farZeroLambdaLowerDecent
import Submission.Work.LinnikAreas.OtherCharRepel.sameCharRepelConst

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex

set_option maxHeartbeats 1000000

/-
# `otherCharRepelConst` — Deuring–Heilbronn repulsion for the other characters
(Heath-Brown 1992, Principle 2)

For `q ≥ q₀`, `χ₀` a real character with a real minimal zero `ρ₀` of `λ(ρ₀) ≤ 1/100`, every zero
`ρ` with `|Im ρ| ≤ 1` of every `χ ≠ χ₀, χ₀⁻¹, 1` satisfies `λ(ρ) ≥ 1/25`.

## Route

Write `λ(ρ) = lamOf q ρ`.  Split at `1/25 ≤ λ(ρ)`.  Otherwise `λ(ρ) < 1/25`, and the
designated-pair trichotomy (`designatedTrichotomy`, proved from the finite-minimiser argument of
`DhRepel.existsDesignated3` with the far bound supplied by `farZeroLambdaLowerDecent`) applies to
`(χ,ρ)`:

* **first alternative** `1/25 ≤ λ(ρ)`: the desired conclusion;
* **second alternative**: `χ₀` has another zero `ρ' ≠ ρ₀` with `|Im ρ'| ≤ 1`,
  `λ(ρ') < λ(ρ) < 1/25`, and the ball-maximality `λ(ρ') ≤ λ(u)` for every `zeroMult`-zero `u` with
  `|Im u| ≤ |Im ρ'| + 1` other than `(χ₀,ρ₀)`.  If `ρ'` is real then the two-real-zero repulsion
  `twoRealZerosRepel` gives `λ(ρ') ≥ 1/4 > 1/25`, and if `ρ'` is not real then
  `sameCharNonRealRepel` gives `λ(ρ') ≥ 1/25`; either way `λ(ρ) > λ(ρ') ≥ 1/25`, a contradiction;
* **third alternative**: a designated pair `(χ₂,ρ₂)` with `χ₂ ≠ χ₀, 1`, `zeroMult χ₂ ρ₂ ≠ 0`,
  `|Im ρ₂| ≤ 1`, `λ(ρ₂) ≤ λ(ρ) < 1/25` and the same ball-maximality.  `IsMin1` gives
  `λ(ρ₀) ≤ λ(ρ₂)`, so `dhApply85` yields `λ(ρ₂) ≥ 1/25`, again contradicting `λ(ρ) ≥ λ(ρ₂)`.

The far bound `farZeroLambdaLowerDecent` (the de la Vallée Poussin zero-free region in the
`λ`-normalisation: `1 ≤ |Im u| ≤ 4 ⟹ λ(u) ≥ 1/25`) is what forces the minimiser of the
trichotomy to lie in the band `|Im| ≤ 1`.
-/

/-- `3 ≤ q` gives `1 ≤ log q` (used for the height condition `|γ₂| + 1 ≤ 10 log q`). -/
private lemma one_le_log_of_three_le {q : ℕ} (hq : 3 ≤ q) : (1 : ℝ) ≤ Real.log (q : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    _ ≤ (q : ℝ) := by exact_mod_cast hq

theorem otherCharRepelConst : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ χ₀⁻¹ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
        (1/25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨qF, hfar⟩ := farZeroLambdaLowerDecent
  obtain ⟨qD, hdesig⟩ := designatedTrichotomy ⟨qF, hfar⟩
  obtain ⟨q8, h8⟩ := dhApply85
  obtain ⟨qS, hS⟩ := sameCharNonRealRepel
  obtain ⟨q2, h2⟩ := twoRealZerosRepel
  refine ⟨max (max (max qF qD) (max q8 qS)) (max q2 3), ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 hlam0 χ ρ hχne _hχinv hχ1 hzm himρ
  have hqF : qF ≤ q := by omega
  have hqD : qD ≤ q := by omega
  have hq8 : q8 ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hq2 : q2 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  by_cases hmain : (1/25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ
  · exact hmain
  · push_neg at hmain
    have hρeq : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him0]
    rcases hdesig q hqD χ₀ ρ₀ hmin hsq him0 hlam0 χ ρ hχne hχ1 hzm himρ with h | h | h
    · exfalso; linarith
    · obtain ⟨ρ', hzm', him', hne', hlt, hball⟩ := h
      have hlt' : Work.LinnikContract.lamOf q ρ' < (1/25 : ℝ) := lt_trans hlt hmain
      by_cases him0' : ρ'.im = 0
      · have hρ'eq : ρ' = ((ρ'.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him0']
        have hres := h2 q hq2 χ₀ ρ₀.re ρ'.re (hmin.1.1)
          (by rw [← hρeq]; exact hmin.1.2.1)
          (by rw [← hρ'eq]; exact hzm')
          (fun hh => hne' (by rw [hρ'eq, hρeq, hh]))
          (by rw [← hρeq]; exact hlam0)
        rw [← hρ'eq] at hres
        linarith
      · have hres := hS q hqS χ₀ ρ₀ ρ' hmin hsq him0 hlam0 hzm' him' hne' him0' hball
        linarith
    · obtain ⟨χ₂, ρ₂, hχ₂χ₀, hχ₂1, hzm₂, him₂, hle, hball₂⟩ := h
      have hle0 : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ₂ :=
        hmin.2 χ₂ ρ₂ ⟨hχ₂1, hzm₂, him₂⟩
      have hle1 : Work.LinnikContract.lamOf q ρ₂ ≤ 1 := by linarith
      have hγ : |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) := by
        have h1 := one_le_log_of_three_le hq3
        linarith [him₂, h1]
      have hres := h8 q hq8 χ₀ ρ₀ χ₂ ρ₂ hmin hsq him0 hlam0 hχ₂1 hχ₂χ₀ hzm₂ hle0 hle1 hγ hball₂
      linarith

end Work.LinnikAreas.OtherCharRepel
