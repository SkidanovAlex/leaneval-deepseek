import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.Trunc.curlAgmon
import Submission.Work.FTS.EllSol.Shift2Flat.niceSlotBoundHE
import Submission.Work.FTS.EllSol.Shift2Flat.niceRangePlanch
import Submission.Work.FTS.EllSol.Shift2Flat.mixedSlotOfNiceE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

set_option autoImplicit false

/-- **The quantitative `NiceFlat` bound for the heavy mixed slot.**

For data of class `Work.FTS.EllSol.FlatFT.NiceFlat` (jointly `C²` on the open strip, vanishing
at the two angles as *values*, and uniformly compactly supported in `t`) whose three
`σ_η`-weighted shifted slots are integrable, the `σ_η`-weighted mixed slot
`∂_θ(∂_t - b)u` is bounded by `C·(V + √(Z·Q))`.

This is the `hNice` input of `Work.FTS.EllSol.Shift2Flat.mixedSlotOfNice`: the quantitative
per-`θ` Plancherel data are supplied by `niceRangePlanch` and the `ℂ`-valued sharp angular
Agmon estimate by `Work.FTS.EllSol.Trunc.curlAgmon` (whose weight `thEta` is `sEta`), so that
`niceSlotBoundHE` applies verbatim. -/
theorem niceBoundQuantFts :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (u : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat u →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) →
      (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2))
        ≤ ENNReal.ofReal (C * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
              (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
                * Work.FTS.EllipticEst.sEta p.2)
            + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                  (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
                    + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                    (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
                      * Work.FTS.EllipticEst.sEta p.2)))) := by
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.EllSol.Trunc.curlAgmon
  refine ⟨Cc, hCcpos, ?_⟩
  intro b u hg hSp hSpp hQ
  obtain ⟨h1, h2, h3⟩ := niceRangePlanch (b := b) hg
  have hmain := niceSlotBoundHE (Cc := Cc) hCcpos hCc (b := b) (u := u) hg
    h1 h2 h3
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hSp)
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hSpp)
    (by simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hQ)
  simpa only [Work.FTS.EllSol.FlatFT.wE_eq_sEta] using hmain

/-- `∫∫ (∂_θ(pz u - b·u))² σ_η < ⊤` from the three weighted slots of `u`.

A complete, hand-verified route is written up in
`Submission/Work/FTS/EllSol/Shift2Flat/NOTES_mixedSlot_route.md` (truncate `u` in `t` by
`Work.FTS.EllSol.Trunc.chi`, apply the complex Agmon inequality `Work.FTS.EllSol.Trunc.curlAgmon`
to the `θ`-slices of the truncated `t`-Fourier transform for each frequency, Plancherel per
slice, `μ(ξ) = (2πξ)² + b²` and Cauchy–Schwarz in `ξ`, then Fatou in the truncation scale).
The statement is TRUE — do not declare false. -/
theorem mixedSlotFiniteness {b : ℝ} (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) < ⊤ := by
  exact mixedSlotOfNice niceBoundQuantFts b u hu h0 hπ hV hZ hQ

end Work.FTS.EllSol.Shift2Flat
