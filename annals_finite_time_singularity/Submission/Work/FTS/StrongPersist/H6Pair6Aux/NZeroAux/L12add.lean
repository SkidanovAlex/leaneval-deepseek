import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

/-! ## Additivity and differentiability of `L₁₂` over `F_* + f`

`L₁₂(g)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` is an integral, hence additive in the
profile as soon as the pieces are integrable; and it is a primitive of `-L12dens`, hence
differentiable at every point at which the density is continuous.  For a datum `f` of the
interior class (`SmoothOpen f`, `HkMem α 4 f`) all the required integrability and continuity
certificates are available:

* the angular slice of `f`, `θ ↦ K θ f(s,θ)/s`, is integrable for `s > 0`
  (`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`);
* the density `L12dens K f` is integrable on `(0,∞)`
  (`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`) and continuous at every
  `z > 0` (`Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk`);
* for the full profile `F_* + f` the same two facts hold
  (`Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_Fstar_add`,
  `Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_Fstar_add`), the reference contribution
  being the elementary `α·2/(1+s)²`.

Additivity is `Work.FTS.LocData.L12_add_mul` (with the `F_*`-slice of
`Work.Stability.integrableOn_slice_Fstar` and the `F_*`-density of
`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`), the two differentiability
statements are `Work.FM.hasDerivAt_L12`. -/

theorem L12add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    (∀ z : ℝ, 0 ≤ z → Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z) ∧
    (∀ z : ℝ, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z) ∧
    (∀ z : ℝ, 0 < z → DifferentiableAt ℝ
        (fun z' => Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z') z) := by
  -- the density of `f`, integrable on `(0,∞)`
  have hdens_f0 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
    Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hso hmem
  -- the slice and density of `f` are integrable above any `z ≥ 0`
  have hslice_f : ∀ z : ℝ, 0 ≤ z → ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    fun z hz s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hso hmem
      (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs))
  have hdens_f : ∀ z : ℝ, 0 ≤ z →
      MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi z) :=
    fun z hz => hdens_f0.mono_set fun s hs => lt_of_le_of_lt hz (Set.mem_Ioi.mp hs)
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
      (a := Work.Construction.Fstar α) (b := f)
      (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
      (hslice_f z hz)
      (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
      (hdens_f z hz)).1
  · have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
      Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk hso hmem hz
    exact (Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) (ρ := z)
      (hdens_f 0 le_rfl) hcont hz).differentiableAt
  · have hint : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)) (Set.Ioi 0) :=
      Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_Fstar_add hα hα1 hso hmem
    have hcont : ContinuousAt
        (Work.FM.L12dens Work.Spaces.K
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)) z :=
      Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_Fstar_add hα hα1 hso hmem hz
    exact (Work.FM.hasDerivAt_L12 (K := Work.Spaces.K)
      (f := fun z θ => Work.Construction.Fstar α z θ + f z θ) (a := 0) (ρ := z)
      hint hcont hz).differentiableAt

end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
