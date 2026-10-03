/-
# `Submission.Work.FIArea6Hecke.heckeLcontInvBound_strip` — *FI* (16.23) in the half-strip

The target is *FI* (16.23)/(16.24),
`‖(Lam s / heckeArch d m s)⁻¹‖ ≤ C·d·log²(|m|+|s.im|+3)` for
`1 - c/(d^ε·log(|m|+|s.im|+3)) < s.re ≤ 1`, where `Lam` is an entire completion of the
Hecke `L`-function of `ℚ(i)` (`Lam s = heckeArch d m s · heckeLSeries chi m s` for
`s.re > 1 + |m|/2`, which determines `Lam` uniquely by analytic continuation).

`Lam / heckeArch` is the meromorphic continuation of the Hecke `L`-function, so the bound is
the classical inverse bound (16.23).  Following the paper ("one may begin with the
corresponding bound for `L'/L`, integrate it to the right to obtain a bound for `|log L|` and
then exponentiate the latter"), the proof is split into the analytic input and a formal
reduction:

* `Work.FIArea6Hecke.StripCore ε` (`StripCoreDefs.lean`) — the paper's (16.20) + Lemma 16.1
  (Siegel), i.e. the zero-free region, together with the bound for `L'/L` inside it;
* `Work.FIArea6Hecke.StripNearOne ε` — the elementary lower bound for `L` just to the right of
  `s = 1`, which anchors the integration;
* `Work.FIArea6Hecke.heckeStripGlue` — the reduction: integrate `L'/L` along the horizontal
  segment from `s` up to `1 + min(1/(K log M), 1/2)`, then exponentiate.

The two analytic inputs are supplied by `heckeStripCore` and `heckeStripNearOne`, and the
target is their combination through `heckeStripGlue`.
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeStripCore
import Submission.Work.FIArea6Hecke.heckeStripNearOne
import Submission.Work.FIArea6Hecke.heckeStripGlue

namespace Work.FIArea6Hecke

/-- *FI* (16.23)/(16.24) in the half-strip `s.re ≤ 1`: the inverse bound for the analytic
continuation of the Hecke `L`-function of `ℚ(i)`, uniform in the strict character `χ` modulo
`4d`, in the weight `m` and in `s`. -/
theorem heckeLcontInvBound_strip :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
          Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
          AnalyticOn ℂ Lam Set.univ →
          (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
            Lam s = Work.FITop4.Bridge.heckeArch d m s *
              Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
          ∀ s : ℂ,
            1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 1 →
            ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
              ≤ C * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  intro ε hε hε4
  exact heckeStripGlue ε hε hε4 (heckeStripCore ε hε hε4) (heckeStripNearOne ε hε hε4)

end Work.FIArea6Hecke
