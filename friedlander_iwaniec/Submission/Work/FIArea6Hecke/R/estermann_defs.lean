/-
# `Submission.Work.FIArea6Hecke.R.estermann_defs`

Vocabulary for the Goldfeld/Estermann step (*FI* Lemma 16.1) of the real-axis zero-free region:
the auxiliary function `estermannF` to which Estermann's positivity lemma is applied, together
with the elementary analytic facts about `Lval d 0 Lam = Lam / heckeArch d 0` on the disc
`|s - 2| ≤ 3/2` on which the positivity engine works.
-/
import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.heckeArch_facts
import Submission.Work.FIArea6Hecke.ZFRDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **The function to which Estermann's positivity lemma is applied.**  It is the completing
factor `(1 - 2^{-s})·L(χ₄,s) = ζ_K(s)/ζ(s)` of the Dedekind zeta function of `ℚ(i)`, multiplied by
the (continued) Hecke `L`-functions `Lam₁/heckeArch d₁ 0`, `Lam₂/heckeArch d₂ 0`, `F`. -/
def estermannF (d₁ d₂ : ℕ) (Lam₁ Lam₂ F : ℂ → ℂ) : ℂ → ℂ :=
  fun s => (1 - (2 : ℂ) ^ (-s)) * DirichletCharacter.LFunction chi4C s *
    Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s * F s

/-- On the disc `|s - 2| ≤ 3/2` the real part is `≥ 1/2 > 0`, so all the archimedean factors are
non-vanishing there. -/
lemma ball_re_pos {z : ℂ} (hz : z ∈ Metric.closedBall (2 : ℂ) (3 / 2)) : 0 < z.re := by
  have h : |z.re - 2| ≤ ‖z - 2‖ := by
    simpa using Complex.abs_re_le_norm (z - 2)
  have hnorm : ‖z - 2‖ ≤ 3 / 2 := by simpa [dist_eq_norm] using hz
  have hle := abs_le.mp (le_trans h hnorm)
  linarith [hle.1]

/-- `Lval d 0 Lam = Lam / heckeArch d 0` is analytic at every point of the disc `|s - 2| ≤ 3/2`
when `Lam` is entire: the denominator is a non-vanishing analytic function there. -/
lemma analyticAt_Lval_of_mem_ball {d : ℕ} (hd : 1 ≤ d) {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ) {z : ℂ} (hz : z ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    AnalyticAt ℂ (fun s => Work.FIArea6Hecke.Lval d 0 Lam s) z := by
  obtain ⟨hne, han⟩ := heckeArch_facts hd
  have hzpos := ball_re_pos hz
  have hLam : AnalyticAt ℂ Lam z := AnalyticOn.analyticAt (s := Set.univ) Filter.univ_mem hAn
  have hdiv : AnalyticAt ℂ (fun s => Lam s / Work.FITop4.Bridge.heckeArch d 0 s) z :=
    hLam.div (han z hzpos) (hne z hzpos)
  simpa [Work.FIArea6Hecke.Lval] using hdiv

end

end Work.FIArea6Hecke.R
