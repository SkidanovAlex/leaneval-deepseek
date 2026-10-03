/-
# `Submission.Work.FIArea6Hecke.R.logDerivNearZeroPF`

The near-zero logarithmic-derivative bound for an admissible Hecke completion, in the form used by
the de la Vallée Poussin region of *FI* (16.20).

For every admissible completion `Λ` (`Work.FIArea6Hecke.R.IsCompleted`), every zero
`ρ = β + iγ` of `Λ` with `0 < β < 1` and every `σ` with `1 < σ ≤ 2`,

  `1/(σ − β) − C·log(4d(|m|+|γ|+3)) ≤ Re (Λ'/Λ)(σ + iγ)`.

The proof has two inputs, both already available in the tree:

* the Hadamard partial fraction `Work.FIArea6Hecke.R.lamPartialFraction` of the completion (whose
  growth hypothesis is `Work.FIArea6Hecke.R.lamGrowth`, and whose validity at the chosen base point
  `-2 + iγ` uses `Work.FIArea6Hecke.R.zerosInStrip` to see that `-2 + iγ` is not a zero), and
* the uniform lower bound `Work.FIArea6Hecke.R.baseLowerNegTwoUniform` at the line `re s = -2`.

The extraction of the polar term `1/(σ − β)` from the partial fraction at the pair
`(σ + iγ, -2 + iγ)` is `Work.FIArea6Hecke.R.re_logDeriv_rebase_negTwo`: at every zero
`u` with `-1 ≤ re u ≤ 1` the rebasing kernel `Re(1/(s−u) − 1/(s₁−u))` is nonnegative (both terms of
`(σ − re u)/|s−u|² + (2 + re u)/|s₁−u|²` are), while at `ρ` itself it equals
`1/(σ − β) + 1/(2 + β) ≥ 1/(σ − β)`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.lamGrowth
import Submission.Work.FIArea6Hecke.R.lamPartialFraction
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.re_logDeriv_rebase_negTwo
import Submission.Work.FIArea6Hecke.R.conductorFECleanNoDep
import Submission.Work.FIArea6Hecke.R.pfacBaseLowerUniform

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped BigOperators Topology

noncomputable section

/-- **The near-zero lower bound for the logarithmic derivative of an admissible completion.**

There is `C > 0` such that for every strict character `χ` mod `4d`, every `m : ℤ`, every entire
completion `Λ` of `Λ(s,ψ)` and every zero `β + iγ` of `Λ` with `0 < β < 1`, and every `σ` with
`1 < σ ≤ 2`,

  `1/(σ − β) − C·log(4d(|m|+|γ|+3)) ≤ Re (Λ'/Λ)(σ + iγ)`. -/
theorem logDerivNearZeroPF :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
        Work.FIArea6Hecke.R.IsCompleted d chi m Lam →
        ∀ σ β γ : ℝ, 1 < σ → σ ≤ 2 → 0 < β → β ≤ 1 →
          Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
          1 / (σ - β) - C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) ≤
            (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) /
              Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨C, hCpos, hbase⟩ := pfacBaseLowerUniform (fun d chi m (hd : 1 ≤ d) hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt)
  refine ⟨C, hCpos, ?_⟩
  intro d chi m Lam hadm σ β γ hσ hσ2 hβ0 hβ1 hzero
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hadm' : IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  -- the Hadamard partial fraction, via the circle growth of the completion
  have hpf := lamPartialFraction d chi m Lam hadm' (lamGrowth d chi m Lam hadm')
  -- the zeros of `Λ` lie in `[-1,1]`
  have hzeros := zerosInStrip_of_conductorFE (fun d chi m (hd : 1 ≤ d) hchi hnt => Work.FIArea6Hecke.RC.conductorFECleanNoDep d hd chi m hchi hnt) d chi m Lam hadm'
  -- `Λ` does not vanish on `re s > 1`, hence at `σ + iγ`
  have hσre : (1 : ℝ) < ((σ : ℂ) + (γ : ℂ) * Complex.I).re := by simpa using hσ
  have hs : Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
    lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hagr hσre
  -- `Λ` does not vanish at the base point `-2 + iγ`, which lies outside the strip
  have hs₁ : Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have h := (hzeros _ h0).1
    simp at h
  have hρ : Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := hzero
  -- the rebasing inequality extracts the polar term `1/(σ - β)`
  have hreb := re_logDeriv_rebase_negTwo Lam hDiff hpf hzeros hσ hβ0 hβ1 hρ hs hs₁
  -- the uniform lower bound at `re s = -2`
  have hbase' := hbase d chi m Lam hadm' γ
  linarith

end

end Work.FIArea6Hecke.R
