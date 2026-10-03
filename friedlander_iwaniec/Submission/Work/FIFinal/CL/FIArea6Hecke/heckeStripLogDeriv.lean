import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeStripLogDeriv

namespace Work.FIArea6Hecke

theorem heckeStripLogDeriv (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          ‖deriv (Work.FIArea6Hecke.Lval d m Lam) s / Work.FIArea6Hecke.Lval d m Lam s‖
            ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε) :=
  Work.FIArea6Hecke.R.heckeStripLogDeriv ε hε hε4

end Work.FIArea6Hecke
