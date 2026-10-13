/-
# `zmollDzPth` — the mixed derivative `D_z∂_θ` of the double mollification

Assembling the two halves of the computation of `D_z∂_θ Φ` for `Φ = zmoll G δ ε`:

* `zmollPthEq` identifies the *angular* derivative `∂_θ Φ` with the `t`-integral of the radial
  kernel against the angular derivative kernel `sKerd ε`;
* `logConvDeriv` differentiates the surviving radial convolution in the *logarithmic* variable,
  which is exactly the operator `D_z = z ∂_z`.

The result is the identity used by the Fatou step: for `z > 0` and `θ ∈ Iθ`,

  `D_z∂_θ Φ z θ = ∫_t sKerd δ (log z - t) · (∫_s sKerd ε (θ - s) · Qext G (exp t) s)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollPthEq
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.hxycSliceLocIntHonest
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.logConvDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext thMoll zmoll sKer)
open Work.FTS.EllSol.EllPkgAux (sKerd Hxyc)

/-- **The mixed derivative of the double mollification.** -/
theorem zmollDzPth (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Hxyc G t s|) MeasureTheory.volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (zmoll G δ ε)) z θ
        = ∫ t : ℝ, sKerd δ (Real.log z - t)
            * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) := by
  intro z hz θ hθ
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the angular derivative slice is locally integrable
  obtain ⟨Mε, hMε0, hMεb, hMεv⟩ := exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  have hli : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s : ℝ,
      sKerd ε (θ - s) * Hxyc G t s) MeasureTheory.volume :=
    hxycSliceLocIntHonest G hT hdom
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0 hε1 hMε0 hMεb hMεv hθw
  -- the angular derivative, for every positive radius
  have hA : ∀ z' : ℝ, 0 < z' → Work.Spaces.pth (zmoll G δ ε) z' θ
      = ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) :=
    fun z' hz' => zmollPthEq G hT hdom hδ0 hδ1 hε0 hε1 hz' hθ
  have hcongr : (fun z' : ℝ => Work.Spaces.pth (zmoll G δ ε) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)) :=
    Filter.Eventually.mono (Ioi_mem_nhds hz) (fun z' hz' => hA z' hz')
  calc Work.Spaces.Dz (Work.Spaces.pth (zmoll G δ ε)) z θ
      = z * deriv (fun z' : ℝ => Work.Spaces.pth (zmoll G δ ε) z' θ) z := rfl
    _ = z * deriv (fun z' : ℝ => ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)) z := by
        rw [Filter.EventuallyEq.deriv_eq hcongr]
    _ = ∫ t : ℝ, sKerd δ (Real.log z - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) :=
        logConvDeriv (fun t : ℝ => ∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) hli hδ0 z hz

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
