import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.zerosInStrip

/-!
# `Submission.Work.FIArea6Hecke.R.lvalSameSeries`

**Transport of the `L`-value `Lval d m Lam` between two completions with the same `L`-series.**

If `Lam` is entire and completes `(chi, m)` (`Lam = heckeArch d m · L(chi,m)` on `re s > 1 + |m|/2`)
and `Lam'` is entire and completes `(chi', 0)` with `L(chi',0) = L(chi,m)`, then the *meromorphic*
functions `Lval d m Lam` and `Lval d 0 Lam'` agree on the half-plane `re s > 0`.  Both are analytic
there (`heckeArch d m` is analytic and zero-free for `re s > 0`, as `re s > -|m|/2`), and they agree
on the sub-half-plane `re s > 1 + |m|/2`, so the identity theorem on a half-plane
(`Work.FIArea6Hecke.R.eqOn_of_agrees_halfplane`) applies.

This is the analytic step of the reduction of the zero-free regions for a *self-dual* character
pair to a genuinely *real* one: it transports non-vanishing of `Lval` between the two completions,
so that the Siegel input `Work.FIArea6Hecke.R.heckeZFRrealAxisClean` (proved for real `ψ`) can be
applied.

Everything here is FE-free and axiom-clean.
-/
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric
open scoped Topology

noncomputable section

/-- `heckeArch d m` is analytic on the half-plane `re s > 0`. -/
theorem analyticOn_heckeArch_pos (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    AnalyticOn ℂ (Work.FITop4.Bridge.heckeArch d m) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOn (fun w hw => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (heckeArch_differentiableAt_of_pos hd m hw).differentiableWithinAt

/-- **The identity theorem for `Lval`.**  Two entire completions with the same `L`-series have the
same `L`-value on `re s > 0`. -/
theorem lval_eq_of_same_series {d : ℕ} {chi chi' : GaussianInt → ℂ} {m : ℤ} {Lam Lam' : ℂ → ℂ}
    (hd : 1 ≤ d)
    (hAn : AnalyticOn ℂ Lam Set.univ) (hAn' : AnalyticOn ℂ Lam' Set.univ)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    (hagr' : ∀ s : ℂ, 1 < s.re →
      Lam' s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi' 0 s)
    (hL : Work.FIArea5.S16Hecke.heckeLSeries chi' 0 = Work.FIArea5.S16Hecke.heckeLSeries chi m) :
    ∀ w : ℂ, 0 < w.re → Lval d m Lam w = Lval d 0 Lam' w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOn ℂ (fun w => Lam w / Work.FITop4.Bridge.heckeArch d m w)
      {z : ℂ | 0 < z.re} :=
    AnalyticOn.div (hAn.mono (Set.subset_univ _)) (analyticOn_heckeArch_pos d hd m)
      (fun w hw => heckeArch_ne_zero_of_pos_re d hd m hw)
  have hG : AnalyticOn ℂ (fun w => Lam' w / Work.FITop4.Bridge.heckeArch d 0 w)
      {z : ℂ | 0 < z.re} :=
    AnalyticOn.div (hAn'.mono (Set.subset_univ _)) (analyticOn_heckeArch_pos d hd 0)
      (fun w hw => heckeArch_ne_zero_of_pos_re d hd 0 hw)
  refine eqOn_of_agrees_halfplane (F := fun w => Lam w / Work.FITop4.Bridge.heckeArch d m w)
    (G := fun w => Lam' w / Work.FITop4.Bridge.heckeArch d 0 w) (T := 0)
    (T' := max 1 (1 + |(m : ℝ)| / 2)) (le_trans zero_le_one (le_max_left _ _)) hF hG ?_
  intro s hs
  have hs1 : 1 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : 1 + |(m : ℝ)| / 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hs0 : 0 < s.re := lt_trans one_pos hs1
  rw [hagr s hs2, hagr' s hs1, hL]
  rw [mul_div_cancel_left₀ _ (heckeArch_ne_zero_of_pos_re d hd m hs0),
    mul_div_cancel_left₀ _ (heckeArch_ne_zero_of_pos_re d hd 0 hs0)]

end

end Work.FIArea6Hecke.R
