/-
# The `L₁₂` zero-mode identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`

This is the paper's `L₁₂(𝓛_Γ f) = 𝓛(L₁₂ f)` at `z = 0` (Elgindi, Annals 194(3) 2021,
§Modulation, tex 1366–1381).  The proof is assembled here from the pieces proved in the
sibling files of this directory:

* `ZM_slice_relation` — the a.e. fibre FTC `∫_r^∞ K(θ)∂_z f = -K(θ)f(r,θ)`, the integrability
  of the `θ`-slices of `K·f`, and the identity `∫_θ K f = -NOf f r`;
* `ZM_Nfun_zero`, `ZM_Nfun_limits` — the boundary value `NOf f 0 = 0` and the limits of `NOf`
  and `ROf`;
* `ZM_mderiv_fubini` — Fubini for `mdOf f r = ∫_θ K(θ)∂_zf(r,θ)`;
* `ZM_IBP_R` — integration by parts for `ROf`;
* `ZM_density_ae` — the a.e. identity
  `L₁₂dens(𝓛_Γ f)(r) - L₁₂dens(f)(r) = mdOf f r - 2u/(1+r) - 2R/(1+r)²`;
* `zm_main` (in `ZM_Main.lean`) — the main computation turning those into the zero-mode
  identity, using the measure-theoretic limits of `ZM_Limits_L1`.

The statement is untouched; only the proof is filled in.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Apriori.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs
import Submission.Work.Coercivity.not_integrableOn_of_rpow_le
import Submission.Work.FTS.Apriori.ZeroMode.ZM_Limits_L1
import Submission.Work.FTS.Apriori.ZeroMode.ZM_Main
import Submission.Work.FTS.Apriori.ZeroMode.ZM_slice_relation
import Submission.Work.FTS.Apriori.ZeroMode.ZM_Nfun_zero
import Submission.Work.FTS.Apriori.ZeroMode.ZM_Nfun_limits
import Submission.Work.FTS.Apriori.ZeroMode.ZM_mderiv_fubini
import Submission.Work.FTS.Apriori.ZeroMode.ZM_IBP_R
import Submission.Work.FTS.Apriori.ZeroMode.ZM_density_ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

theorem L12_LGamma_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => Work.Spaces.pz f s θ) (Set.Ici 0))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0))
    (hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL2 : MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens f z) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens (Work.Coercivity.LGamma α f) z) (Set.Ioi 0)) :
    Work.Construction.L12 (Work.Coercivity.LGamma α f) 0
      = - Work.Construction.L12 f 0 := by
  have H : L12Hyp α f := ⟨hα, hα1, hdiff, hcont, hdec, hvan, hint, hintL, hintL2, hint3⟩
  have hSR := ZM_slice_relation H
  have hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ :=
    hSR.2.1
  -- `r * L₁₂dens f r = -NOf f r`
  have hrel : ∀ r : ℝ, 0 < r → r * uOf f r = - NOf f r := by
    intro r hr
    have h3 := hSR.2.2 r hr
    have hdiv : uOf f r = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ) / r := by
      show Work.FM.L12dens Work.Spaces.K f r = _
      exact Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (ne_of_gt hr)
    rw [hdiv, h3]
    field_simp
  have hNL := ZM_Nfun_limits H
  have hNcont : ContinuousOn (NOf f) (Set.Ici 0) := hNL.1
  have hNtop : Filter.Tendsto (NOf f) Filter.atTop (𝓝 0) := hNL.2.1
  have hR0 : Filter.Tendsto (ROf f) (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)) := hNL.2.2.1
  have hRtop : Filter.Tendsto (fun r : ℝ => ROf f r / (1 + r)) Filter.atTop (𝓝 0) := hNL.2.2.2
  have hN0 : NOf f 0 = 0 :=
    ZM_Nfun_zero H hrel (hNcont.continuousWithinAt (by simp))
  -- continuity of `uOf f` on `(0,∞)`, from `uOf f r = -NOf f r / r`
  have hu : ContinuousOn (uOf f) (Set.Ioi 0) := by
    have hnil : ∀ r ∈ Set.Ioi (0:ℝ), uOf f r = - NOf f r / r := by
      intro r hr
      rw [eq_div_iff (ne_of_gt hr)]
      have h := hrel r hr
      linarith
    refine ContinuousOn.congr ?_ hnil
    exact (hNcont.mono (Set.Ioi_subset_Ici_self)).neg.div continuousOn_id
      (fun r hr => ne_of_gt hr)
  have hMF := ZM_mderiv_fubini H
  have hibp := ZM_IBP_R H hu
  have hae := ZM_density_ae H hslice
  have hGint : MeasureTheory.IntegrableOn (GOf α f) (Set.Ioi 0) := H.hint3
  have huint : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0) := H.hintL2
  exact zm_main H hslice hrel hNcont hNtop hR0 hRtop hN0 hMF.1 hMF.2.1 hibp hae hGint huint

end Work.FTS.Apriori.ZeroMode
