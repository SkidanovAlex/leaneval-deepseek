/-
# `Work.FTS.EllSol.EllPkgAux.mollFatouAssembly` — the Fatou assembly of the mollification transfer

The datum `G` of the trace-class interpolation is recovered from its doubly-mollified
approximants `Φ_{δ,ε} = zmoll G δ ε` by **lower semicontinuity** (Fatou): the approximants
converge to `G` in the pointwise a.e. sense supplied by the hypotheses `hconv`, `hhon`, hence

  `∫_Iz mixIntS G ≤ liminf_n ∫_Iz mixIntS Φ_{tseq n, tseq n}`,

and consequently one can pick a single pair `(δ, ε)` (here the diagonal sequence
`tseq n = 1/(n+2)`) with `∫_Iz mixIntS G ≤ ∫_Iz mixIntS Φ_{δ,ε} + η`.

Two points make the argument non-trivial.

* The `θ`-slice integrals occurring in `mixIntS` are *junk-value zero* wherever the slice is not
  integrable, so the comparison between `mixIntS Φ z` and the `θ`-lower integral of its
  integrand is an inequality in the wrong direction unless the slices of `Φ` are honest.
  Honesty of the approximants is supplied by `StripAdm`: `zmoll G δ ε` is `C^∞` on the half
  strip and vanishes at `θ = 0, π/2`, so `∂_z∂_θ Φ` is bounded on the compact slice
  `{z} × [0,π/2]`.
* All the lower-semicontinuity steps are performed at the `ℝ≥0∞` level (`lintegral`), where no
  integrability is needed; the `IntegrableOn` hypotheses `hF` (for `G`) and `hint` (for the
  approximants) are what allow the final conversion back to the Bochner integrals.

The proof is assembled from four modules of this directory:

* `MollAssem.Defs`  — the Fatou device and the interval estimate `sliceIntBoundMFA`;
* `MollAssem.StripAdm` — the slice domination `sliceDomMFA` and the strip-admissibility
  `mollAdmMFA : StripAdm G δ ε` of the approximant (from the sorry-free pieces of `MollSmooth`);
* `MollMFA.zmollSliceHonest` — `StripAdm` gives the honesty of the approximant's `θ`-slices;
* `MollAssem.FatouCore` — the Fatou core `mollFatouCore`, which takes that honesty as an
  explicit hypothesis; the present file discharges it.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.StripAdm
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.FatouCore
import Submission.Work.FTS.EllSol.EllPkgAux.MollMFA.zmollSliceHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

theorem mollFatouAssembly (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (hint : ∀ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε → MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) Work.Spaces.Iz) (hconv : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Filter.atTop (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) (hhon : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) (hhonG : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) : ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε ∧ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  have hhonest : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro n z hz
    exact Work.FTS.EllSol.EllPkgAux.MollMFA.zmollSliceHonest G (tseq n) (tseq n)
      (MollAssem.mollAdmMFA G hT hF (tseq n) (tseq n) (params_tseq n)) z hz
  exact MollAssem.mollFatouCore G hT hF hint hconv hhon hhonest

end Work.FTS.EllSol.EllPkgAux
