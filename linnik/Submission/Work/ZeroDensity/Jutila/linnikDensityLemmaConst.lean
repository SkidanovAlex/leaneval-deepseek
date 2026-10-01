import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Jutila.kernelSumHalf
import Submission.Work.ZeroDensity.Jutila.linnikDensityAuxArith
import Submission.Work.ZeroDensity.Jutila.linnikDensityAuxKernel
import Submission.Work.ZeroDensity.Jutila.linnikDensityAuxBox

/-!
# Linnik's density lemma with an explicit (non-sharp) constant

This file proves `Work.ZeroDensity.Jutila.linnikDensityLemmaConst`: for a non-principal
Dirichlet character `χ` mod `q`, `0 ≤ σ ≤ 1` and `T ≥ 1`, the multiplicity weighted number of
zeros of the completed `L`-function of the primitive character inducing `χ` in the box
`σ ≤ Re ρ ≤ 1`, `|Im ρ - T| ≤ (1-σ)/2` is at most `C · ((1-σ)·log(q(T+1)) + 1)` for an absolute
constant `C` (here `C = 30`).

The mathematics is Jutila (1977), Lemma 8 (= Prachar, *Primzahlverteilung*, p. 331): the box has
"side" `λ = 1-σ` attached to the line `Re = 1`.  The proof is the classical Hadamard partial
fraction argument, in the form in which the workspace already has it:

* `kernelSumHalf` (Jutila's sharp kernel-sum bound, proved in
  `Submission/Work/ZeroDensity/Jutila/kernelSumHalf.lean`) bounds the divisor weighted sum of the
  rebased kernel `Re (1/((1+λ+iT) - ρ))` over *all* zeros in a ball by
  `1/λ + ½log N + ½log(2+T) + 4`;
* every box zero contributes at least `1/(5λ)` to that sum (`linnikDensityAuxKernel`);
* the bookkeeping that converts the box sum into the ball sum is `linnikDensityAuxBox`;
* the final elementary estimate on the resulting expression is `linnikDensityAuxArith`.
-/

namespace Work.ZeroDensity.Jutila

open scoped Classical BigOperators
open Complex DirichletCharacter Metric

noncomputable section

/-- The completed `L`-function of the primitive character inducing `χ`. -/
def primLam {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  DirichletCharacter.completedLFunction χ.primitiveCharacter

/-- The primitive character inducing a non-principal character is non-principal. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  refine hχ ?_
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h, map_one] at h2
  exact h2.symm

/-- `primLam χ` is entire for a non-principal `χ`. -/
lemma primLam_analytic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (primLam χ) Set.univ := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdiff : Differentiable ℂ (primLam χ) := by
    rw [primLam]
    exact DirichletCharacter.differentiable_completedLFunction (primitiveCharacter_ne_one χ hχ)
  exact fun z _ => hdiff.analyticAt z

/-- Every zero of the completed `L`-function of the primitive character inducing a
non-principal `χ` lies in the open critical strip. -/
lemma primLam_zero_strip {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {u : ℂ}
    (hu : primLam χ u = 0) : 0 < u.re ∧ u.re < 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [primLam] at hu
  exact Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
    (primitiveCharacter_ne_one χ hχ) (DirichletCharacter.primitiveCharacter_isPrimitive χ) u hu

/-- `Re (1/((a + i b) - u)) = (a - Re u)/((a - Re u)^2 + (b - Im u)^2)`. -/
lemma re_one_div_sub (a b : ℝ) (u : ℂ) :
    (1 / (((a : ℂ) + Complex.I * (b : ℂ)) - u)).re
      = (a - u.re) / ((a - u.re) ^ 2 + (b - u.im) ^ 2) := by
  have hre : (((a : ℂ) + Complex.I * (b : ℂ)) - u).re = a - u.re := by simp
  have him : (((a : ℂ) + Complex.I * (b : ℂ)) - u).im = b - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him]
  ring

/-- **Linnik's density lemma, in the form the sources actually state it.**

There is an absolute constant `C > 0` such that for every non-principal `χ` mod `q ≥ 2`, every
`0 ≤ σ ≤ 1` and every `T ≥ 1`, the multiplicity-weighted number of zeros `ρ` of the completed
`L`-function of (the primitive character inducing) `χ` with `σ ≤ Re ρ ≤ 1` and
`|Im ρ - T| ≤ (1-σ)/2` is at most `C·((1-σ)·log(q(T+1)) + 1)`.

This is Jutila (1977), Lemma 8 (p. 51), i.e. Prachar, *Primzahlverteilung*, p. 331: "the number of
zeros in `α ≤ σ ≤ 1`, `|t - T| ≤ (1-α)/2` is `≪ (1-α)log(q(|T|+2)) + 1`".  Every careful statement
in the literature (Pintz, impAN Lemma 1; Ye, Pacific J. Math. 207 (2002), Lemma 21; Akbary–Trudgian,
arXiv:1312.5820, Density Lemma) carries an **implied constant**; the standard proof (Hadamard
partial fraction at `s₀ = 1 + r + iT`, where each box zero contributes `≥ 1/(5r)`) gives `C = 5`.
The existing stub `Work.ZeroDensity.Jutila.linnikDensityLemma` states the constant as `1`, which the
reviewers of `Work.ZeroDensity.Jutila.nearLineBoxCount` (see
`Submission/Work/ZeroDensity/Jutila/NOTE_nearLineBoxCount_verdict.md`) rejected as an unsupported
sharpening; the version below is the one that the sources support and that the Jutila §3 assembly
consumes (it needs only `O(1)` zeros per box). -/
theorem linnikDensityLemmaConst : ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T),
    (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  refine ⟨30, by norm_num, ?_⟩
  intro q _inst χ hχ σ T hσ0 hσ1 hT
  show (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
      |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0))
    ≤ 30 * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with hq | hq
    · have hqne : q ≠ 0 := NeZero.ne q
      have hq1 : q = 1 := by omega
      subst hq1
      exact absurd (DirichletCharacter.level_one χ) hχ
    · exact hq
  have hN1 : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hNq : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hbox := linnikDensityAuxBox (primLam χ) (primLam_analytic χ hχ)
    (fun u hu => primLam_zero_strip χ hχ hu) hσ0 hσ1 hT
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ 1 - σ by linarith) with hl | hl
  · have hl1 : 1 - σ ≤ 1 := by linarith
    have hkh := kernelSumHalf (χ.primitiveCharacter) (primitiveCharacter_ne_one χ hχ)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)
      (σ := 1 + (1 - σ)) (τ := T) (by linarith) (by linarith) (T + 2)
    have hkh' : (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) *
          ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2)))
        ≤ 1 / (1 - σ) + (1 / 2) * Real.log ((χ.conductor : ℕ) : ℝ)
          + (1 / 2) * Real.log (2 + |T|) + 4 := by
      have hkey : (∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) *
            ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2)))
          = (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor
              (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) *
              (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * ((T : ℝ) : ℂ) - u)).re) := by
        refine finsum_congr (fun u => ?_)
        have hdd : ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ)
            = ((MeromorphicOn.divisor
                (DirichletCharacter.completedLFunction χ.primitiveCharacter)
                (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) := by
          rw [primLam]
        rw [hdd, re_one_div_sub]
      rw [hkey]
      have hc : (1 : ℝ) + (1 - σ) - 1 = 1 - σ := by ring
      rw [hc] at hkh
      exact hkh
    have hTabs : |T| = T := abs_of_nonneg (by linarith)
    rw [hTabs] at hkh'
    have harith := linnikDensityAuxArith (q := q) (N := χ.conductor) (l := 1 - σ) (T := T)
      hq2 hN1 hNq hT hl hl1
    have hfac : (0 : ℝ) ≤ 5 * (1 - σ) := by linarith
    calc (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0))
        ≤ 5 * (1 - σ) * (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (T + 2)) u : ℤ) : ℝ) *
              ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2))) := hbox
      _ ≤ 5 * (1 - σ) * (1 / (1 - σ) + (1 / 2) * Real.log ((χ.conductor : ℕ) : ℝ)
            + (1 / 2) * Real.log (2 + T) + 4) := by
          refine mul_le_mul_of_nonneg_left hkh' hfac
      _ ≤ 30 * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := harith
  · have hl0 : 1 - σ = 0 := hl.symm
    have h := hbox
    rw [hl0] at h
    have hz : (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0)) ≤ 0 := by
      simpa [hl0] using h
    have hgoal : (1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1 = 1 := by
      rw [hl0]; ring
    rw [hgoal]
    linarith

end

end Work.ZeroDensity.Jutila
