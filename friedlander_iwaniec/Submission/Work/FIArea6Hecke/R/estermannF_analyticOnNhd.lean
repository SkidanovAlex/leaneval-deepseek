import Mathlib
import Submission.Work.FIArea6Hecke.R.estermann_defs

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- The factor `s ↦ 1 - 2^{-s}` is entire: `2^{-s} = exp(-s log 2)` is the composition of the
linear map `s ↦ -s` with a `cpow` at the non-zero constant `2`. -/
lemma analyticAt_one_sub_two_cpow (z : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (-s)) z :=
  (Differentiable.const_sub
    (Differentiable.const_cpow (Differentiable.neg differentiable_id)
      (Or.inl (two_ne_zero : (2 : ℂ) ≠ 0))) (1 : ℂ)).analyticAt z

/-- `estermannF d₁ d₂ Lam₁ Lam₂ F` is analytic on a neighbourhood of the closed disc
`|s - 2| ≤ 3/2`: each of its five factors is analytic there, the two quotients
`Lval d 0 Lam = Lam / heckeArch d 0` because `heckeArch d 0` is non-vanishing and analytic for
`re s > 0` (true on the disc), and `LFunction chi4C` because a Dirichlet `L`-function is entire. -/
theorem estermannF_analyticOnNhd {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {Lam₁ Lam₂ F : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ) (hAn₂ : AnalyticOn ℂ Lam₂ Set.univ)
    (hFan : AnalyticOn ℂ F Set.univ) :
    AnalyticOnNhd ℂ (estermannF d₁ d₂ Lam₁ Lam₂ F) (Metric.closedBall (2 : ℂ) (3 / 2)) := by
  intro z hz
  -- the five factors, each analytic at `z`
  have hfac1 : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (-s)) z :=
    analyticAt_one_sub_two_cpow z
  have hfac2 : AnalyticAt ℂ (DirichletCharacter.LFunction chi4C) z :=
    (DirichletCharacter.differentiable_LFunction chi4C_ne_one).analyticAt z
  have hfac3 : AnalyticAt ℂ (fun s : ℂ => Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s) z :=
    analyticAt_Lval_of_mem_ball h₁ hAn₁ hz
  have hfac4 : AnalyticAt ℂ (fun s : ℂ => Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s) z :=
    analyticAt_Lval_of_mem_ball h₂ hAn₂ hz
  have hfac5 : AnalyticAt ℂ F z :=
    AnalyticOn.analyticAt (s := Set.univ) Filter.univ_mem hFan
  have hprod : AnalyticAt ℂ
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (-s)) * DirichletCharacter.LFunction chi4C s *
        Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s * F s) z :=
    (((hfac1.mul hfac2).mul hfac3).mul hfac4).mul hfac5
  unfold estermannF
  exact hprod

end

end Work.FIArea6Hecke.R
