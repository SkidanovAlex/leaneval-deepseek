/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_id`

The mixed derivative `D_z ∂_θ` of the doubly mollified datum `Φ = zmoll G δ ε`, in the form in
which the two mollifying kernels have *both* been consumed:

  `D_z ∂_θ Φ(z,θ) = ∫_t sKerd δ (log z - t) · ∂_θ(thMoll G ε)(eᵗ) θ`

for `z > 0` and `θ ∈ Iθ`.  Here `∂_θ(thMoll G ε)(eᵗ) θ` is the *angular* derivative of the
angular mollification, taken at the log-radial radius `eᵗ`.

The two halves of the identity are the two differentiations that the iterated integral
`Φ z θ = ∫_t sKer δ (log z - t) · thMoll G ε (eᵗ) θ` admits:

* the `∂_θ`-half is `thMoll_hasDerivAt`, applied slicewise with `Q := Qext G (eᵗ)` (the
  mollifying kernel `sKer ε` is replaced by its derivative `sKerd ε`), giving
  `∂_θ(thMoll G ε)(eᵗ) θ = ∫_s sKerd ε (θ - s) · Qext G (eᵗ) s` for **every** `t` (no `a.e.`
  issue: `eᵗ > 0` always);
* the outer `D_z` is the logarithmic convolution with `sKerd δ`, which is the already proved
  identity `zmollDzPth`.

The hypothesis `hF` (`FourInts G`) enters only through the local integrability of the angular
slice functional `t ↦ ∫_{Iθ} |Hxyc G t s|`, obtained from `mollSliceBound` + `mollHdom`; it is
the domination needed to differentiate under the outer `t`-integral.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollDzPthConv
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.mollHdom
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.unusedVariables false

/-- **The angular derivative of the angular mollification, as a convolution with `sKerd ε`.**

For a trace-class datum `G`, a mollification scale `ε ∈ (0, 1/2]` and any bound `M` of the
derivative kernel `sKerd ε`, the `θ`-derivative of `θ' ↦ thMoll G ε w θ'` at any `θ ∈ Iθ` is the
convolution of the (doubly odd extension of the) slice `s ↦ Qext G w s` with `sKerd ε`, for
*every* radius `w > 0`; we state it for `w = eᵗ`.

This is `MollDzAux.thMoll_hasDerivAt` applied with `Q := Qext G (eᵗ)` and the slice identity
`thMoll G ε w θ' = ∫ s, sKer ε (θ' - s) * Qext G w s`. -/
theorem thMoll_pth_kernel (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M) :
    ∀ t : ℝ, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ') (Real.exp t) θ
        = ∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
            * Work.FTS.EllSol.EllPkgAux.Hxyc G t s := by
  intro t θ hθ
  -- `θ ∈ Iθ` lies in the window on which the differentiation under the integral is available
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  have h := Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
      (Q := fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp t) s)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hε0 hε1 hM hθw
  simpa only [Work.Spaces.pth, Work.FTS.EllSol.PkgK5.K5c.thMoll,
    Work.FTS.EllSol.EllPkgAux.Hxyc] using h.deriv

theorem zmoll_mixed_id (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
        = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
            * (Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ') (Real.exp t) θ) := by
  intro z hz θ hθ
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  -- ## local integrability of the angular slice functional (the domination for the outer `t`-integral)
  have hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume := by
    obtain ⟨C, hC, hslB⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
    obtain ⟨hslG, hintMGG⟩ := hslB G hT hF
    exact Work.FTS.EllSol.EllPkgAux.mollHdom G hT.1 C hC hslG hintMGG
  -- ## a bound for the derivative kernel `sKerd ε`
  obtain ⟨Mε, _hMε0, hMεb, -⟩ := Work.FTS.ClassC.RopGen.Trace.ZmollAux.exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  -- ## the outer `D_z`, i.e. the logarithmic convolution with `sKerd δ`
  rw [Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth G hT hdom (δ := δ) (ε := ε)
    hδ0 hδ1 hε0 hε1 z hz θ hθ]
  -- ## the inner `∂_θ`, i.e. the convolution of the slice with `sKerd ε`, for every `t`
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [thMoll_pth_kernel G hT hε0 hε1 hMεb t θ hθ]

end Work.FTS.EllSol.EllPkgAux.MollDom
