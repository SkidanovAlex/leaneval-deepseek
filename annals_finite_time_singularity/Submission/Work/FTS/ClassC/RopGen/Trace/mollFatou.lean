/-
# `Work.FTS.ClassC.RopGen.Trace.mollFatou` — the Fatou step of the mollification transfer

For a datum `G` in the trace class with the four outer integrabilities and `η > 0`, there are
mollification parameters `δ, ε ∈ Params` with

  `∫_z mixIntS G ≤ ∫_z mixIntS (zmoll G δ ε) + η`.

The proof is the standard lower-semicontinuity (Fatou) argument along the diagonal sequence
`tseq n = 1/(n+2) → 0`: the slice integrands `(D_z∂_θ Φₙ)² σ_η` converge a.e. to
`(D_z∂_θ G)² σ_η` and are honest and measurable, so that Fatou in `θ` and then in `z` compares
`∫_z mixIntS G` with `liminf_n ∫_z mixIntS Φₙ`; an index is then extracted with the `+η` slack.

The analytic content is entirely in the imported pieces:

* `zmollDzPth` (`ZmollAux/zmollDzPth.lean`, this area) identifies `D_z∂_θ Φ` as the double
  convolution of the datum against the derivative kernels `sKerd δ`, `sKerd ε`;
* `mollKernelLimit` / `mollTargetDeriv` turn that convolution into the pointwise limit
  `D_z∂_θ G` (an approximate identity in two variables);
* `mollHon` and `mollHconv` supply the a.e. strong measurability and the a.e. convergence of
  the slice integrands;
* `mollSliceBound` / `mollHdom` supply the local integrability of the dominating function used
  in the identification above;
* `mollAdmMFA` (via `MollMFA.zmollSliceHonest`) makes the approximant's slices honest, and
  `MollAssem.mollFatouCore` performs the two Fatou steps and the extraction of `(δ, ε)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollFatouHelpers
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.mollKernelLimit
import Submission.Work.FTS.EllSol.EllPkgAux.mollTargetDeriv
import Submission.Work.FTS.EllSol.EllPkgAux.mollHdom
import Submission.Work.FTS.EllSol.EllPkgAux.mollHon
import Submission.Work.FTS.EllSol.EllPkgAux.mollHconv
import Submission.Work.FTS.EllSol.EllPkgAux.mollFatouAssembly
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace

set_option autoImplicit false
set_option linter.unusedVariables false

theorem mollFatou : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G →
    Work.FTS.EllSol.EllPkgAux.FourInts G →
    (∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε → MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
      Work.Spaces.Iz) →
    ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε ∧
      (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  intro G hT hF hint η hη
  -- the slice bound and the local integrability of the dominating function
  obtain ⟨C, hC, hslBound⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  obtain ⟨hslG, hintMGG⟩ := hslBound G hT hF
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- the domination hypothesis of `zmollDzPth`
  have hdom := Work.FTS.EllSol.EllPkgAux.mollHdom G hS C hC hslG hintMGG
  -- the identification of the mixed derivative of the approximant
  have hid : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ
        = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t')
            * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s)
                * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s) :=
    fun t ht0 ht1 =>
      Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth G hT hdom ht0 ht1 ht0 ht1
  -- the limit of the double kernel convolution
  have hderiv : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z)
        = Work.Spaces.Dz (Work.Spaces.pth G) z θ :=
    fun z hz θ h0 h1 => Work.FTS.EllSol.EllPkgAux.mollTargetDeriv G hS hz h0 h1
  have hlim : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto
        (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t u
          * Work.FTS.EllSol.EllPkgAux.sKerd t v
          * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ)
          (Real.log z))) := by
    intro z hz θ h0 h1
    have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      isOpen_univ.prod isOpen_Ioo
    have hmem : (Real.log z, θ) ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨trivial, h0, h1⟩
    exact Work.FTS.EllSol.EllPkgAux.mollKernelLimit
      (H := Work.FTS.EllSol.EllPkgAux.Hxyc G)
      (U := (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
      (x := Real.log z) (y := θ) hU hmem
      (Work.FTS.EllSol.EllPkgAux.contDiffOn_uncurry_Hxyc G hS 2)
  -- pointwise convergence along the sequence
  have hconv := Work.FTS.EllSol.EllPkgAux.mollHconv G hS hderiv hid hlim
  -- honesty of the approximant's slice integrals
  have hhon : ∀ (n : ℕ) (z : ℝ), 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n)
            (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n z hz =>
      Work.FTS.EllSol.EllPkgAux.mollHon G hS (Work.FTS.EllSol.EllPkgAux.tseq n)
        (Work.FTS.EllSol.EllPkgAux.tseq_pos n) (Work.FTS.EllSol.EllPkgAux.tseq_le_half n) z hz
        (fun θ hθ => hid (Work.FTS.EllSol.EllPkgAux.tseq n)
          (Work.FTS.EllSol.EllPkgAux.tseq_pos n) (Work.FTS.EllSol.EllPkgAux.tseq_le_half n)
          z hz θ hθ)
  -- honesty of the datum's slice integrals
  have hhonG : ∀ z : ℝ, 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun z hz => Work.FTS.EllSol.EllPkgAux.aeStronglyMeasurable_slice_G G hS hz
  exact Work.FTS.EllSol.EllPkgAux.mollFatouAssembly G hT hF hint hconv hhon hhonG η hη

end Work.FTS.ClassC.RopGen.Trace
