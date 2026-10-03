import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeStripZFR

namespace Work.FIArea6Hecke

theorem heckeStripZFR (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 :=
  Work.FIArea6Hecke.R.heckeStripZFR ε hε hε4

end Work.FIArea6Hecke
