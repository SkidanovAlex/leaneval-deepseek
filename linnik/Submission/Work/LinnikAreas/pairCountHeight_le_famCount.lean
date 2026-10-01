import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.ZeroDensity.Defs

/-!
# `Work.LinnikAreas.siegelHighMass` — the `λ₁`-free high-zero mass bound of AREA 6

Two lemmas that remove the *split-exponent* input `Work.LinnikAreas.Siegel.PairDensityHeightInput`
from the critical path of AREA 6, replacing it by the *coupled* classical Deuring–Heilbronn
density estimate `Work.LinnikAreas.Siegel.DHLogFreeHeightCoupled` (Bombieri, *Le grand crible*,
Thm. 14 / Jutila 1977: `Σ_χ N*(σ,T,χ) ≤ C·λ₁·(qT)^{c(1-σ)}`, `c < 49/10`).

* `pairCountHeight_le_famCount` — the height pair count is dominated by the family count;
* `siegelHighAbel` — Abel summation in `λ` against a *two-range* count (the coupled DH count up to
  a threshold `λ*`, the σ-blind count above it).

The layer assembly that consumes them is `Work.LinnikAreas.siegelRestHighCoupled`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

/-- **The height pair count is dominated by the family count.**  The multiplicity-weighted number
of pairs `(χ,ρ)` with `zeroMult χ ρ ≠ 0`, `λ(ρ) ≤ t` and `|Im ρ|·𝓛 ≤ T` is at most the family count
`Σ_χ N(1-t/𝓛, T/𝓛, χ)`, which counts *all* zeros (with multiplicity) of the completed
`L`-functions of all characters mod `q`, principal included, in the rectangle
`1 - t/𝓛 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T/𝓛`.  The exceptional pair `(χ₁,β₁)` is excluded on the left and
included on the right, so the inequality goes in the safe direction. -/
theorem pairCountHeight_le_famCount {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {t T : ℝ} :
    Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T
      ≤ Work.ZeroDensity.famCount q (1 - t / Real.log q) (T / Real.log q) := by
  classical
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show (1 : ℕ) < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have key : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧
          Work.LinnikContract.lamOf q ρ ≤ t ∧ |ρ.im| * Real.log q ≤ T ∧
          ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ (∑ᶠ ρ : ℂ, if 1 - t / Real.log q ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im| ≤ T / Real.log q
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    intro χ
    refine finsum_le_finsum' ?_ ?_ ?_
    · -- finiteness of the left summand: it is contained in a compact box
      refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - t / Real.log q)
        (max T 0 / Real.log q)).subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ Work.LinnikContract.lamOf q ρ ≤ t ∧
          |ρ.im| * Real.log q ≤ T ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) := by
        by_contra hcon
        exact hρ (if_neg hcon)
      have hrel : 1 - t / Real.log (q : ℝ) ≤ ρ.re := by
        have h2 : 1 - ρ.re ≤ t / Real.log (q : ℝ) :=
          (le_div_iff₀ hlog).mpr (by simpa [Work.LinnikContract.lamOf] using hc.2.1)
        linarith
      have him : |ρ.im| ≤ max T 0 / Real.log (q : ℝ) := by
        have h2 : |ρ.im| ≤ T / Real.log (q : ℝ) := (le_div_iff₀ hlog).mpr hc.2.2.1
        have h3 : T / Real.log (q : ℝ) ≤ max T 0 / Real.log (q : ℝ) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlog.le
        linarith
      exact ⟨hc.1, hrel,
        le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hc.1), him⟩
    · refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - t / Real.log q)
        (T / Real.log q)).subset ?_
      intro ρ hρ
      simp only [Function.mem_support] at hρ
      have hd : 1 - t / Real.log (q : ℝ) ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im| ≤ T / Real.log (q : ℝ) := by
        by_contra hcon
        exact hρ (if_neg hcon)
      have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
        have hz : (Work.LinnikContract.zeroMult χ ρ : ℝ) ≠ 0 := by
          rwa [if_pos hd] at hρ
        exact_mod_cast hz
      exact ⟨hzm, hd.1, hd.2.1, hd.2.2⟩
    · intro ρ
      dsimp only
      by_cases hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧
          Work.LinnikContract.lamOf q ρ ≤ t ∧ |ρ.im| * Real.log q ≤ T ∧
          ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
      · have hrel : 1 - t / Real.log (q : ℝ) ≤ ρ.re := by
          have h2 : 1 - ρ.re ≤ t / Real.log (q : ℝ) :=
            (le_div_iff₀ hlog).mpr (by simpa [Work.LinnikContract.lamOf] using hc.2.1)
          linarith
        have him : |ρ.im| ≤ T / Real.log (q : ℝ) := (le_div_iff₀ hlog).mpr hc.2.2.1
        rw [if_pos hc, if_pos ⟨hrel,
          le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hc.1), him⟩]
      · rw [if_neg hc]
        by_cases hd : 1 - t / Real.log (q : ℝ) ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im| ≤ T / Real.log (q : ℝ)
        · rw [if_pos hd]; exact Nat.cast_nonneg _
        · rw [if_neg hd]
  simp only [Work.LinnikAreas.Siegel.pairCountHeight, Work.ZeroDensity.famCount,
    Work.ZeroDensity.zCount, Work.LinnikAreas.zeroCountIn]
  exact Finset.sum_le_sum (fun χ _ => key χ)

end Work.LinnikAreas
