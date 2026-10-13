import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0Left
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0Right
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate.sliceGradSq_rate_of_trace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The a.e. trace and rate of `z ∂_z u` at the two angular endpoints

This module proves `Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0`: for a datum
`AeData α u G` with

* `hsl` : for a.e. `z > 0` the angular slice `θ ↦ (z ∂_z ∂_θ u(z,θ))² sin(2θ)^{-η}` is
  integrable on `Iθ` (the a.e.-in-`z` clause of the mixed honesty `ℋ⁰`), and
* `hsl2`: the `z`-integral of that slice energy is integrable on `Iz` (the outer clause),

the slice `θ ↦ z ∂_z u(z,θ)` tends to `0` at both endpoints `0⁺` and `(π/2)⁻` for a.e. `z > 0`,
and satisfies the two *marginal* Hardy-type rates
`(z ∂_z u(z,θ))² ≤ 4 · dist^{1+η} · ∫ (z ∂_z ∂_θ u)² σ` against the *truncated* energies.

Note that `Work.Spaces.Dz (Work.Spaces.pth u) z θ = z * ∂_z ∂_θ u(z,θ)` and
`Work.FTS.EllipticEst.sEta θ = sin(2θ)^{-η}` are definitionally the objects of the hypotheses,
so `hsl`/`hsl2` *are* the two clauses of the mixed honesty in `Dz`-form; no Clairaut rewrite is
needed (the two mixed partials agree on the open quadrant anyway, `Spaces.pz_pth_comm`).

The route is the one of `AngAWeak.aeGradTraceLeft` / `aeGradTraceRightMine` (the *global*-honesty
version), with the outer hypothesis `∫_z w² ∫_θ (z ∂_z∂_θ u)² σ < ∞` weakened to
`∫_z ∫_θ (z ∂_z∂_θ u)² σ < ∞`: the only place the weighted form was used was the local
integrability of `√sliceE` on a compact `[a,b] ⊆ (0,∞)` (there via the lower bound
`1 ≤ b⁴ w(s)²`), which the weaker hypothesis supplies directly (Cauchy–Schwarz on the finite
interval).  The two rates are the per-slice estimates `sliceRateTwoLeft` / `sliceRateTwoRight`
applied to the slice (module `GlueRate`), the additive constants being identified with `0` by the
trace vanishing.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngAWeak

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

theorem aeGradTrace0 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (hsl2 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
          * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 < z ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (z * Work.Spaces.pz u z θ)^2 ≤ K * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t)^2
              * (Real.sin (2*t)) ^ (-(Work.Spaces.eta))))
      ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (z * Work.Spaces.pz u z θ)^2 ≤ K * (Real.pi/2 - θ) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo θ (Real.pi / 2), (z * Work.Spaces.pz (Work.Spaces.pth u) z t)^2
              * (Real.sin (2*t)) ^ (-(Work.Spaces.eta)))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)
  -- `hsl`/`hsl2` are the mixed honesty in `Dz`-form, definitionally
  have hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ := hsl
  have hE : MeasureTheory.IntegrableOn (sliceE u) Iz := hsl2
  refine ⟨4, by norm_num, ?_⟩
  have htrL := aeGradTraceLeft_of_energy α u G h hGae hE
  have htrR := aeGradTraceRight_of_energy α u G h hGae hE
  filter_upwards [htrL, htrR, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hsl]
    with z hzL hzR hzpos hzsl
  have hintπ : MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) :=
    hzsl.mono_set Set.Ioo_subset_Icc_self
  obtain ⟨hrateL, hrateR⟩ :=
    Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueRate.sliceGradSq_rate_of_trace
      hS hzpos hintπ hzL hzR
  exact ⟨hzpos, hzL, hzR, hrateL, hrateR⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
