import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.HkIntegrand_integral_le_pth2_pth_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary vocabulary for the proof

`Sfun` is the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`; `Bdom` is the dominating function by which a single angular
integrand (at a fixed radial level `z`, with a fixed value `M` of the `H^k`-integral of
`∂_θ² f`) is bounded. -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
private def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)









/-!
**The per-`z` angular Poincaré comparison `∂_θf` vs `∂_θ²f` in the half-strip class.**

This is the port of the *already proved*
`Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2_pth`
(`Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_integral_le_pth2_pth.lean`, sorry-free) from
the hypothesis `Work.Spaces.SmoothNbhd f` to the weaker, provable hypothesis
`Work.FTS.EllipticEst.SmoothHalf f` (see `Submission/Work/FTS/EllipticEst/HalfSmooth.lean`).

ROUTE: copy the proof of the original file (the same proof as the `∂_θ²`-version, with the
`∂_θ`-slice estimate `Blocks.slice_d_bound` in place of `Blocks.slice_f_bound`, i.e. with `deriv u`
in the role of `u`) and replace `SmoothNbhd f` by `SmoothHalf f`, using the half-strip layer
`Submission/Work/Blocks/SmoothHalfAux.lean` (namespace `Work.FTS.EllipticEst.HalfU`, sorry-free).
The original proof runs in the branch `0 < z` (`hzpos`) for everything after the `z = 0` case,
exactly the regime in which the half-strip layer applies; `hsm.halfAn : HalfU.HalfAn f` is the
second conjunct of `SmoothHalf`.  The replacements are

* `SmoothNbhd.DzIter hsm j` + `sliceSmooth_of_SmoothNbhd … hz` ↦ `HalfU.HalfAn.slice_DzIter hsm.halfAn j hzpos`;
* `sliceV_DzIter hsm j hz hθ` ↦ `HalfU.sliceV_DzIter hsm.halfAn j hzpos hθ`;
* `LopIter_sliceV_DzIter_eq_mixed hsm j m hz hθ` ↦ `HalfU.LopIter_sliceV_DzIter_eq_mixed hsm.halfAn j m hzpos hθ`;
* `DzIter_pth_eq_deriv hsm j hz hθ` ↦ `HalfU.DzIter_pth_eq_deriv hsm.halfAn j hzpos hθ`;
* `LopIter_deriv_DzIter_eq_mixed hsm j i hz hθ` ↦ `HalfU.LopIter_deriv_DzIter_eq_mixed hsm.halfAn j i hzpos hθ`;
* `integrableOn_HkIntegrand_terms α k (pthIter 2 f) (hsm.pth.pth) hz …` ↦
  `HalfU.integrableOn_HkIntegrand_terms_half α k (pthIter 2 f) (hsm.halfAn.pthIter 2) hzpos …`;
* `Blocks.slice_data_integrable_of_HkIntegrand α k f hsm hzpos j hj …` ↦
  `HalfU.slice_data_integrable_of_HkIntegrand_half α k f hsm.halfAn hzpos j hj …`.

Everything else (`DzIter_boundary_zero hvan j`, `HkIntegrand_eq_slice_sum`, `sliceGroup`, `sliceA`,
`slicePhi`, `sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`, `integral_mono_of_nonneg`, the
`Sfun`/`Bdom` helpers and the arithmetic) is unchanged, and so is the `hC2` hypothesis verbatim.
-/

end Work.Blocks
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

/-- **The hypothesis package of the trace-class single-function interpolation.**  This is
verbatim the tuple of hypotheses of `InterpOpenTraceStmt` (for the datum `G`): smoothness on
the open quadrant, the two endpoint *values*, the four vanishing endpoint *traces* of `G` and
of `D_zG`, and slicewise honesty of the three right-hand-side slots. -/
def TraceClass (G : ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen G ∧
  (∀ z : ℝ, G z 0 = 0) ∧ (∀ z : ℝ, G z (Real.pi / 2) = 0) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
  Work.EllipticEst.Core.i0Aux.SliceHonestOpen G

/-- The four outer `z`-integrability hypotheses of `InterpOpenTraceStmt`, bundled. -/
def FourInts (G : ℝ → ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z) Work.Spaces.Iz

/-- **Strip-admissibility of the doubly-mollified datum**: `zmoll G δ ε` is smooth on the
half strip `(0,∞) × (-1, π/2+1)` (hence `C^∞` across both angular boundary lines) and vanishes
on the two boundary lines.  These are exactly the smoothness hypotheses of
`Work.EllipticEst.Core.i0Aux.InterpStrip`. -/
def StripAdm (G : ℝ → ℝ → ℝ) (δ ε : ℝ) : Prop :=
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) ∧
  (∀ z : ℝ, Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z 0 = 0) ∧
  (∀ z : ℝ, Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z (Real.pi / 2) = 0)

/-- The two-sided *validity window* of the mollification parameters. -/
def Params (δ ε : ℝ) : Prop := 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 / 2

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.WeakSlice

set_option autoImplicit false

/-! ## The `Q0` instances of the open-set Clairaut identities

The generic modules `ThetaU/OpenSliceAux/{pth_DzIter_eqOn_of_isOpen,DthIter_DzIter_eqOn_of_isOpen}`
prove the Clairaut identities on an *arbitrary* open set `V` carrying the regularity class
`∀ n, ContDiffOn ℝ n (uncurry g) V`.  The open-quadrant class `SmoothOpen` is exactly that class
at `V = Q0` (`Work.FTS.EllipticEst.smoothOpen_iff_forall`), so the identities instantiate at
once; what is left is to read them pointwise at an interior point and to iterate `∂_θ` once
more, exactly as in the half-strip version `ThetaU.OpenSliceIdents.pth_DzIter_open` /
`pthIter_two_DzIter_open`. -/

/-- **`∂_θ (D_z^j f) = D_z^j (∂_θ f)` for an open-quadrant datum.**  Pointwise form of
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen` specialised to `Q0`. -/
theorem pth_DzIter_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ := by
  have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 (fun n => hf.forall n) j
  exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- **The second `θ`-derivative commutes with `D_z^j` for an open-quadrant datum.**  Pointwise
form of `pthIter_two_DzIter_open` with `Q0` in place of the half-strip: `∂_θ` is compared
across `D_z^j` by `pth_DzIter_Q0` (applied to `∂_θ f`, which is again `SmoothOpen`), and the
two resulting functions agree on the open set `Q0`, so their `∂_θ` agree at the point
(`Work.Spaces.pth_congr_of_isOpen`). -/
theorem pthIter_two_DzIter_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 (fun n => hf.forall n) j
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hmem]
  exact pth_DzIter_Q0 hf.pth j hz hθ

/-
**The second `θ`-derivative of the slice `θ' ↦ D_z^j f z θ'` is the slice of `D_z^j (∂_θ² f)`.**

At an interior point `(z,θ) ∈ Q0 = (0,∞) × (0,π/2)` of an open-quadrant datum
(`SmoothOpen f`, i.e. `C^∞` on `Q0`):

  `deriv (deriv (fun θ' => D_z^j f z θ')) θ = D_z^j (pthIter 2 f) z θ`.

This is `Work.FTS.EllipticEst.ThetaU.sliceV_DzIter_open` with the hypothesis `SmoothOpenθ f`
(C^∞ on the half-strip `(0,∞) × (-1, π/2+1)`) weakened to `SmoothOpen f` (C^∞ only on the open
quadrant) and the angle restricted to the interior; equivalently it is
`pthIter_two_DzIter_open` (same file) at interior points.

Route: the identity `∂_θ² (D_z^j f) = D_z^j (∂_θ² f)` is a Clairaut/commutation statement for
`∂_θ` and `D_z = z ∂_z`, both of which are local.  Two generic (arbitrary open set `V`)
ingredients are already proved and are the natural building blocks:
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen` and
`...OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen` (Clairaut for `D_θ`/`D_z` on `V`, with
`∀ n, ContDiffOn ℝ n (uncurry g) V` as the regularity class), together with
`Work.Spaces.pth_congr_of_isOpen` / `Work.Spaces.pz_congr_of_isOpen` (comparison of two
derivatives at a point from their equality on an open set) and the API of
`Submission.Work.FTS.EllipticEst.OpenQDefs` (`SmoothOpen.DzIter`, `SmoothOpen.pth`,
`SmoothOpen.DzIter`, `isOpen_Q0`, `SmoothOpen.hasDerivAt_slice_DzIter`).  The proof of the
existing half-strip version (`ThetaU.OpenSliceIdents.sliceV_DzIter_open`,
`pthIter_two_DzIter_open`, `pth_DzIter_open`) can be followed verbatim with `Q0` in place of
`halfStrip`; nothing needs the angular smoothness beyond `0` and `π/2`.
-/
theorem sliceV_DzIter_smoothOpen {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  show deriv (deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')) θ = _
  rw [show deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')
      = fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ' from rfl]
  rw [show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ from rfl]
  exact pthIter_two_DzIter_Q0 hf j hz hθ

end Work.FTS.EllSol.WeakSlice
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-! ## 9. The reverse transfer -/

theorem lintegral_box_exp_rev {F : ℝ → ℝ → ℝ≥0∞}
    (hAE : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)))
    (hAE₂ : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)))
    {G : ℝ × ℝ → ℝ≥0∞}
    (hGF : G =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2))
    (h : ∫⁻ q in (Set.univ : Set ℝ) ×ˢ Iθ, G q < ⊤) :
    ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) < ⊤ := by
  have h' : ∫⁻ q, G q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ)
      (volume.restrict Iθ)) < ⊤ := by
    have hmeas : MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)
        = (volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ) := by
      rw [show (volume : Measure (ℝ × ℝ))
          = MeasureTheory.Measure.prod (volume : Measure ℝ) (volume : Measure ℝ) from
        Measure.volume_eq_prod ℝ ℝ]
      rw [← MeasureTheory.Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeas]
    exact h
  rw [lintegral_box_exp (F := fun z θ => F z θ) hAE hAE₂]
  refine lt_of_eq_of_lt ?_ h'
  exact (lintegral_congr_ae hGF).symm

/-! ## 10. The main theorem -/

theorem mixIntS_integrableOn_Ioi {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) (Set.Ioi (0 : ℝ)) := by
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  have hU' : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) := hU
  have hthEta : ∀ θ ∈ Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  -- ## slot 1 (f = Dz u)
  have hF1nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF1cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := hSm.Dz.continuousOn_HkIntegrand α 0
  have hg1 : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp p.1 * Work.Spaces.pz u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp continuous_fst).continuousOn
        (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))).mul
      (contOn_expComp hSm.pz.continuousOn)
  have hidg1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Real.exp t * Work.Spaces.pz u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz hSm hθ]
  have hid1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz u (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz u (Real.exp t) θ from rfl]
    ring
  have hslot1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF1nn (Phi_nonneg hidg1) hid1 hF1cont (continuousOn_Phi hg1 hidg1) hU'.1 hU'.2
  -- ## slot 3 (f = pthIter 2 u)
  have hF3nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF3cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hSm.pth.pth).continuousOn_HkIntegrand α 0
  have hg3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pthIter 2 u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.pth.pth).continuousOn
  have hidg3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.pthIter 2 u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pthIter]
  have hid3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pthIter, HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul]
    ring
  have hslot3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (Φ := fun t θ => (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF3nn (Phi_nonneg hidg3) hid3 hF3cont (continuousOn_Phi hg3 hidg3)
      hAe.memAng2.1 hAe.memAng2.2
  -- ## slot 2 (f = Dz (Dz u))
  have hF2nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hdom2 : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 < z →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    intro z θ hθ hz
    rw [HkIntegrand_zero, HkIntegrand_zero, HkIntegrand_zero]
    rw [show Work.Spaces.Dz (Work.Spaces.Dz u) z θ
        = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ from pb_DzDz hSm hz hθ]
    nlinarith [sq_nonneg (Work.Spaces.Dz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      - z ^ 2 * Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have hslices2 : ∀ z ∈ Work.Spaces.Iz, Integrable (fun θ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (MeasureTheory.volume.restrict Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      simp only [Work.Spaces.HkIntegrand_zero_z, Pi.zero_apply]
      exact MeasureTheory.integrable_zero ℝ ℝ _
    · refine MeasureTheory.Integrable.mono'
        (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
        (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ?_ ?_ ?_
      · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0) hpos
      · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
        rw [Real.norm_of_nonneg (hF2nn z θ)]
        exact hdom2 z θ hθIoo hpos
  have houter2 : Integrable (fun z => ∫ θ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hg : Integrable (fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine ((hU'.2.const_mul 2).add (hAe.memRad2.2.const_mul 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      show 2 * (∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          + 2 * (∫ θ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          = ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
              + 2 * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            ∂(MeasureTheory.volume.restrict Iθ)
      rw [MeasureTheory.integral_add ((hU'.1 z hz).const_mul 2)
          ((hAe.memRad2.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    refine MeasureTheory.Integrable.mono'
      (f := fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ))
      (g := fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) ?_ ?_ ?_
    · exact hg
    · exact (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)).integral_prod_right'
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · rw [← h0]
        simp only [Work.Spaces.HkIntegrand_zero_z]
        simp
      · rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae ?_)]
        swap
        · filter_upwards with θ
          exact hF2nn z θ
        refine MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Iθ)
          (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
          (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ) ?_ ?_ ?_
        · filter_upwards with θ; exact hF2nn z θ
        · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
        · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
          exact hdom2 z θ hθIoo hpos
  have hg2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.Dz.Dz).continuousOn
  have hidg2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz2 hSm hθ]
  have hid2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz2 hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.Dz u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ from rfl]
    ring
  have hslot2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2
        * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ)
      hF2nn (Phi_nonneg hidg2) hid2 ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)
      (continuousOn_Phi hg2 hidg2) hslices2 houter2
  -- ## the interface
  have hconcl := hOm (pb u) (pb_contDiff hAe.smooth 2)
    (fun t => hAe.dirZero (Real.exp t)) (fun t => hAe.dirPi (Real.exp t))
    hslot1 hslot2 hslot3
  -- ## the reverse transfer
  have hGcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
  have hidM : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pth_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.pth u) (Real.exp t) θ from rfl]
    ring
  have hGF : (fun q : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (pb u)) q.1 q.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw q.1
          * Work.FTS.EllipticEst.sEta q.2))
      =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp q.1) q.2)) := by
    filter_upwards [ae_strip_of hidM] with q hq
    rw [hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (MeasureTheory.volume.restrict Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)
      ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
    rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable)
  have hAEt : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
          (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp measurable_fst).aemeasurable)).mul ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((aesm_prod_univ_Iθ (f := fun t θ => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp t) θ) hGcont).aemeasurable)
  have hAEt' : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1
      * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine hAEt.congr ?_
    filter_upwards with q
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hfinT := lintegral_box_exp_rev (F := fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
    hAEz hAEt hGF hconcl
  -- ## conclude
  have hJnn : ∀ z, 0 ≤ ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hθ)] with θ hθ
    exact mul_nonneg (sq_nonneg _) (hthEta θ hθ)
  have hcmp : ∀ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
      ≤ ∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
          ∂(MeasureTheory.volume.restrict Iθ) := by
    intro z
    have hΦnn : ∀ θ ∈ Iθ, 0 ≤ (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ := fun θ hθ => mul_nonneg (sq_nonneg _) (hthEta θ hθ)
    have h1 : ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal (∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
      rw [Work.EllipticEst.Core.mixIntS, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    have h2 : ENNReal.ofReal (∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ ∫⁻ θ, ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ) := by
      by_cases h : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Iθ
      · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hΦnn)]
      · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
        exact bot_le
    have h3 : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ, ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ))
        = ∫⁻ θ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ∂(MeasureTheory.volume.restrict Iθ) :=
      (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [h1]
    refine le_trans (mul_le_mul (le_refl _) h2 zero_le zero_le) (le_of_eq ?_)
    rw [h3]
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hθ)] with θ hθ
    rw [HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hθ]
    rw [show (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) from by
      rw [show Work.FTS.EllipticEst.sEta = Work.FTS.EllipticEst.thEta from rfl]
      ring]
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hfinz : ∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS u z)
      ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hcmp) ?_
    rw [show (∫⁻ z, (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.Spaces.Dz (Work.Spaces.pth u)) z θ) ∂(MeasureTheory.volume.restrict Iθ))
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0)))
        = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            p.1 p.2) ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)
              |>.prod (MeasureTheory.volume.restrict Iθ)) from
      (MeasureTheory.lintegral_prod _ hAEz).symm]
    exact hfinT
  -- ## integrability
  have hAESM : AEStronglyMeasurable (Work.EllipticEst.Core.mixIntS u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)
          |>.prod (MeasureTheory.volume.restrict Iθ)) := by
      have hsinpos : ∀ p ∈ ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)),
          0 < Real.sin (2 * p.2) := by
        intro p hp
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos])
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          (Work.Spaces.Dz (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        refine ((hSm.pth.Dz).continuousOn.pow 2).mul ?_
        have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
            = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
          funext p; rfl
        rw [hfun]
        exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
          (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
      have h := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
      rwa [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
          = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    have h1 := hjoint.integral_prod_right'
    have h2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by funext z; rfl
      rw [hfun]
      exact (((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
    have hfun : ((fun z : ℝ => (Work.Spaces.w z) ^ 2) * (fun x : ℝ => ∫ y in Iθ,
        Work.Spaces.Dz (Work.Spaces.pth u) x y ^ 2 * Work.FTS.EllipticEst.thEta y))
        = Work.EllipticEst.Core.mixIntS u := by
      funext z
      simp only [Pi.mul_apply, Work.EllipticEst.Core.mixIntS]
    simpa only [hfun] using h2.mul h1
  rw [MeasureTheory.IntegrableOn]
  refine ⟨hAESM, ?_⟩
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun z => ?_) hfinz
  rw [Real.enorm_eq_ofReal (by
    rw [Work.EllipticEst.Core.mixIntS]
    exact mul_nonneg (sq_nonneg _) (hJnn z))]


end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `σ`-weighted slice self-form of `Lzero1`, with the positive `sec²θ`-slot** (honest
class).  There is `K > 0` such that for every `f` which is `C²` on `(0,π/2)`, `C¹` on `[0,π/2]`,
vanishes at both endpoints, and whose four `σ`-weighted integrands are honest,

  `((1-η)/2) ∫_θ (f/cos θ)² σ ≤ ∫_θ (Lzero1 f)·f·σ + K ∫_θ f² σ`. -/
theorem honSliceSigmaStrong :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 1 f (Work.Spaces.Iθ) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      ((1 - Work.Spaces.eta) / 2) * (∫ θ in Work.Spaces.Iθ,
          (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
          + K * (∫ θ in Work.Spaces.Iθ,
              (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨CH, hCH0, hHardyBase⟩ :=
    hardy_shift_two_same_weight Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  have hKpos : 0 < Work.Spaces.eta + 6 + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH := by
    have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
    have h2 : (0 : ℝ) < 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
    have h3 : (0 : ℝ) < 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) := mul_pos h2 h1
    have h4 : (0 : ℝ) < 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH := mul_pos h3 hCH0
    linarith [h4, Work.Spaces.eta_pos]
  refine ⟨Work.Spaces.eta + 6 + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * CH,
    hKpos, ?_⟩
  intro f hu2 hu1 h0 hπ hint_du hint_ddu hint_u hint_lz
  set η : ℝ := Work.Spaces.eta with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef, Work.Spaces.eta]; norm_num
  have hη1 : η < 1 := by rw [hηdef, Work.Spaces.eta]; norm_num
  obtain ⟨C, hC0, hbdIcc, hbdd⟩ := Work.Elliptic.contDiffOn_one_bounds hu1 h0 hπ
  have hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC0)
  have hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ) := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC0)
  have hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C := fun θ hθ => by
    rw [← Real.norm_eq_abs]
    exact hbdd θ hθ
  have hu_cont : ContinuousOn f Iθo := hu2.continuousOn
  have hlim : HonPrimTendstoProp η f :=
    HonPrimitiveTendsto η hη0 hη1 f C hC0 hb1 hb2 hb3
  obtain ⟨hcc, hhc⟩ := HonAuxIntegrable η hη0 hη1 f C hC0 hu_cont hb1 hb2
  have hfull : IntegrableOn (honFull η f) Iθo :=
    HonFullWeightIntegrable η hη0 hη1 f C hC0 hu_cont hb1 hb2
  have hid := honSliceIdentity η hη0 hη1 f hu2 hlim
    (hint_lz.mono_set Ioo_subset_Icc_self) hint_du hint_u hcc hhc
  -- the sharp Hardy bound on the full weight
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_of_Icc hθ
  have hAeq : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honDu η f θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honDu, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hBeq : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honU2 η f θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honU2, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hHardy' : (∫ θ in Work.Spaces.Iθ, honFull η f θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have h := hHardyBase f hu1 h0 hπ
    rw [show (1 : ℝ) / (η + 1) ^ 2 = 1 / (1 + η) ^ 2 by ring] at h
    rw [hAeq, hBeq] at h
    exact h
  have hHtG : (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honFull η f θ) := by
    have hhcI : IntegrableOn (honHc η f) Work.Spaces.Iθ :=
      hhc.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    have hfullI : IntegrableOn (honFull η f) Work.Spaces.Iθ :=
      hfull.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    refine MeasureTheory.integral_mono_of_nonneg ?_ hfullI ?_
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      have hs := sin_two_pos_of_Iθo hθ
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      exact honHc_le_honFull η f hθ
  have hHtBound : (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := le_trans hHtG hHardy'
  have hH2 : (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honHc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honDu η f θ)
        + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have hne : (1 + η) ^ 2 ≠ 0 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hHtBound (by positivity : (0 : ℝ) ≤ (1 + η) ^ 2)
    have he : (1 + η) ^ 2 * (1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          + CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ))
        = (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
      field_simp
    linarith [h1, he]
  have hDu0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, honDu η f θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos_of_Iθo hθ).le _)
  -- the pointwise identity `honCc = ((1-η)/2)·(f/cos)²σ`
  have honCc_eq_pt : ∀ θ : ℝ,
      honCc η f θ = ((1 - η) / 2) * ((f θ / Real.cos θ) ^ 2 * sig η θ) := by
    intro θ
    rw [honCc]
    by_cases h : Real.cos θ = 0
    · simp [h]
    · have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 h
      rw [div_pow,
        show (1 / 2 * (1 - η) / Real.cos θ ^ 2) = (1 - η) / 2 / Real.cos θ ^ 2 from by ring]
      field_simp
      try ring
  have hCcEq : (∫ θ in Work.Spaces.Iθ, honCc η f θ)
      = ((1 - η) / 2) * (∫ θ in Work.Spaces.Iθ,
          (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [show (∫ θ in Work.Spaces.Iθ, honCc η f θ)
        = ∫ θ in Work.Spaces.Iθ, ((1 - η) / 2) * ((f θ / Real.cos θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => honCc_eq_pt θ)]
    exact MeasureTheory.integral_const_mul _ _
  -- the final arithmetic
  have hne1 : (0 : ℝ) < 1 + η := by linarith
  rw [← hCcEq]
  have hgoal : (∫ θ in Work.Spaces.Iθ, honCc η f θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honLz η f θ)
        + (η + 6 + 2 * η * (1 + η) * CH)
          * (∫ θ in Work.Spaces.Iθ, honU2 η f θ) := by
    have hmul : (1 + η) * (∫ θ in Work.Spaces.Iθ, honCc η f θ)
        ≤ (1 + η) * ((∫ θ in Work.Spaces.Iθ, honLz η f θ)
          + (η + 6 + 2 * η * (1 + η) * CH)
            * (∫ θ in Work.Spaces.Iθ, honU2 η f θ)) := by
      have hstep1 : 2 * η * ((1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honHc η f θ))
          ≤ 2 * η * ((∫ θ in Work.Spaces.Iθ, honDu η f θ)
              + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η f θ)) :=
        mul_le_mul_of_nonneg_left hH2 (by linarith)
      have hstep2 : 2 * η * (∫ θ in Work.Spaces.Iθ, honDu η f θ)
          ≤ (1 + η) * (∫ θ in Work.Spaces.Iθ, honDu η f θ) :=
        mul_le_mul_of_nonneg_right (by linarith) hDu0
      nlinarith [hid, hstep1, hstep2]
    exact le_of_mul_le_mul_left hmul hne1
  exact hgoal

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.cut_slices_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false

/-! ## Outer integrability of the cut slices

For a `SmoothOpenθ` function `G` (smooth on the open strip `(0,∞) × (-1, π/2+1)`, in
particular on a neighbourhood of the closed box `[δ,R] × [0,π/2]`), the `z`-slices of the
mixed iterates `D_z^j ∂_θ^i G` are bounded on the box, so every product of two of them,
integrated in `θ` against the integrable weight `σ θ = sin(2θ)^{-η}`, is bounded on the
support `[1/k², k²]` of the logarithmic cut-off `ζ = zc φ k`.  Multiplying by the bounded
weight `w²` and by `ζ` (which vanishes off the compact support) gives an integrable function
of `z` on `Iz = [0,∞)`.

This is the variant of `integrable_outer_cut_mixed` (which handles the *un-scaled* angular
operator `D_θ = sin(2θ) ∂_θ`, i.e. `mixed j i G = D_z^j D_θ^i G`) needed for the *plain*
angular derivatives `∂_θ^i G` that occur in the slices of the interpolation estimate. -/



end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.zouter_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4


end Work.FTS.EllipticEst.Alpha4
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.absPzIter2SliceFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular profile `sinθcos²θ` is continuous. -/
private lemma continuous_sinCos2_ang : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `sinθcos²θ ≥ 0` on the angular domain. -/
private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

/-- The angular interval has finite Lebesgue measure (in the `≠ ⊤` form). -/
private lemma volume_Iθ_ne_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- A compact interval has finite Lebesgue measure (in the `≠ ⊤` form). -/
private lemma volume_Icc_ne_top (a b : ℝ) : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **Pointwise domination on the box.**

For `0 < a ≤ z` and `θ ∈ Iθ`,

  `|∂_z²u z θ| · |sinθcos²θ| ≤ a⁻⁴ · HkIntegrand α 0 (z² ∂_z²u) z θ + 1`.

This is `abs_mul_sinCos2_le_weighted` (absorbing the angular profile into the weighted square
`(∂_z²u · w/sin(2θ)^{η/2})²` plus `1`), followed by `sq_le_HkIntegrand_z` at `i = 0` for the
datum `z² ∂_z²u` (whose `i = 0` summand is `z⁴` times that square) and the trivial `z⁴ ≥ a⁴`. -/
private lemma pointwise_bound {α : ℝ} {u : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (ha : 0 < a) (hz : a ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1 := by
  have hzpos : 0 < z := lt_of_lt_of_le ha hz
  have h1 : |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
    have hh := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.pzIter 2 u z θ) hzpos hθ
    rwa [abs_mul] at hh
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [eq_inv_mul_iff_mul_eq₀ hz4]
    ring
  have h3 : ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ 0 (Nat.zero_le 0)
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 4)⁻¹ := by positivity
  have hzipow : (z ^ 4)⁻¹ ≤ (a ^ 4)⁻¹ := by
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < z ^ 4) (by positivity : (0 : ℝ) < a ^ 4)]
    exact pow_le_pow_left₀ ha.le hz 4
  have hX : (0 : ℝ) ≤ ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
  calc |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep := mul_le_mul_of_nonneg_right hzipow hX
        linarith
    _ ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1 := by
        have hstep := mul_le_mul_of_nonneg_left h3 hcinv
        linarith

/-- **The two slice facts on a fixed compact interval.** -/
private theorem slice_facts_aux {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
        (Set.Icc a b) := by
  have hu : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun x hx => by
    rw [Work.Spaces.Iz]; exact le_trans (le_of_lt ha) hx.1
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (((hu.pzIter 2).continuousOn).abs).mul
      (((continuous_sinCos2_ang.comp continuous_snd).continuousOn).abs)
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]; infer_instance
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  -- ## Angular slices: dominated by the level-`0` integrand of `z² ∂_z²u`
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    have hdom : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ + 1)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hmZ.1 s hsz).const_mul ((a ^ 4)⁻¹)).add (integrable_const 1)
    refine hdom.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
        hcont hspos
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact pointwise_bound ha hs.1 hθ
  -- ## The iterated angular integral
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc a b) := by
    have hJint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ)
        (Set.Icc a b) := hmZ.2.mono_set hsub
    have hDint : MeasureTheory.IntegrableOn (fun s : ℝ =>
        (a ^ 4)⁻¹ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ)
        + (∫ θ in Work.Spaces.Iθ, (1 : ℝ))) (Set.Icc a b) :=
      ((hJint.const_mul ((a ^ 4)⁻¹)).add
        (MeasureTheory.integrableOn_const (C := (∫ θ in Work.Spaces.Iθ, (1 : ℝ)))
          (volume_Icc_ne_top a b)))
    refine hDint.mono' ?_ ?_
    · have hprod : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
          ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha.le
      have h4 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ : ℝ,
          |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|
            ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict (Set.Ioc a b)) :=
        hprod.integral_prod_right'
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (a := a) (b := b))]
      exact h4
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun z hz => ?_)
      have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
      have hsz : z ∈ Work.Spaces.Iz := hsub hz
      have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ| := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [Real.norm_of_nonneg hFnn]
      have hdInt : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1)
          (volume.restrict Work.Spaces.Iθ) :=
        ((hmZ.1 z hsz).const_mul ((a ^ 4)⁻¹)).add (integrable_const 1)
      have hf1 : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmZ.1 z hsz).const_mul ((a ^ 4)⁻¹)
      have hf2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
        integrable_const 1
      have hmono : (∫ θ in Work.Spaces.Iθ,
            |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, ((a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1) :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          hdInt
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => pointwise_bound ha hz.1 hθ))
      calc (∫ θ in Work.Spaces.Iθ,
            |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, ((a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1) := hmono
        _ = (a ^ 4)⁻¹ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            + (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := by
            rw [MeasureTheory.integral_add hf1 hf2, MeasureTheory.integral_const_mul]
  refine ⟨?_, hint⟩
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hcont
    (fun z _ θ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hsl hint

theorem absPzIter2SliceFacts {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :
    (∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    ∧ (∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
        (Set.Icc a b)) := by
  constructor
  · intro a b ha hab
    exact (slice_facts_aux hsm hmZ ha hab).1
  · intro a b ha hab
    exact (slice_facts_aux hsm hmZ ha hab).2

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSin_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {F : ℝ → ℝ → ℝ}

/-! ## The moment relation for `B_j = F_*(D_z^j F)`

`Bmom F j z = ∫_θ D_z^j F(z,θ) sinθcos²θ dθ` is the `j`-th radial moment of `F`.  The single
analytic input of the estimate is that the moments form a *tower*: the `j`-th moment is a
primitive of `B_{j+1}(s)/s`.  This is `moment_relation` applied to `u = D_z^j F`, whose
`z`-derivative is `D_z^{j+1}F/s`. -/

/-- The `θ`-integral of `∂_z(D_z^j F)` against `sinθcos²θ` is `B_{j+1}(s)/s`. -/
theorem Bmom_deriv_integral (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = Bmom F (j + 1) s / s := by
  have hid : ∀ θ : ℝ, Work.Spaces.pz (Work.Spaces.DzIter j F) s θ
      = Work.Spaces.DzIter (j + 1) F s θ / s := by
    intro θ
    have h1 : Work.Spaces.DzIter (j + 1) F s θ
        = s * Work.Spaces.pz (Work.Spaces.DzIter j F) s θ := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    rw [h1, mul_div_cancel_left₀ _ hs.ne']
  rw [Bmom_eq_Fstar_DzIter, Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [hid θ])]
  rw [show (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => (1 / s) * (Work.Spaces.DzIter (j + 1) F s θ
          * Work.Elliptic.sinCos2 θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The moment tower.**  For `0 < a < b`,
`B_j(b) = B_j(a) + ∫_a^b B_{j+1}(s)/s ds`, whenever `j + 1 ≤ k`. -/
theorem BFstar_relation (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Bmom F j b = Bmom F j a + ∫ s in a..b, Bmom F (j + 1) s / s := by
  have hrel := moment_relation_layer (Work.Spaces.DzIter j F) (hF.DzIter j)
    (fun a b ha hab => boxIntegrable_DzIter_layer α k hF hmem j hj a b ha hab)
    (fun z hz => integrableOn_DzIter_mul_sinCos2 α k hF hmem j (by omega) hz)
    ha hab
  rw [Bmom_eq_Fstar_DzIter, Bmom_eq_Fstar_DzIter, hrel]
  congr 1
  rw [show (∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ))
      = ∫ s in Set.Icc a b, Bmom F (j + 1) s / s from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun s hs => Bmom_deriv_integral (F := F) j (lt_of_lt_of_le ha hs.1))]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

/-- **The moment tower, anchored at `c`.**  For every `y > 0`,
`B_j(y) = B_j(c) + ∫_c^y B_{j+1}(s)/s ds`. -/
theorem Bmom_eq_const_add_integral (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → Bmom F j y = Bmom F j c + ∫ s in c..y, Bmom F (j + 1) s / s := by
  intro y hy
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hrel := BFstar_relation α k hF hmem j hj hy hlt
    rw [hrel, intervalIntegral.integral_symm]
    ring
  · subst heq
    simp
  · exact BFstar_relation α k hF hmem j hj hc hgt

/-! ## Continuity of the moments -/

/-- The `j`-th moment is continuous on `(0,∞)`, for `j + 1 ≤ k`. -/
theorem continuousOn_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => Bmom F j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hb : a < z + a := by linarith
  have hg : IntegrableOn (fun s => Bmom F (j + 1) s / s) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le hb.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a (z + a) ha0 hb
  have hΦ : ContinuousOn (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hg
  have hnhds : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hb.le]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.Ioi 0) z :=
    (hΦ.continuousAt hnhds).continuousWithinAt
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j hj ha0 x hx
  have hz_e : Bmom F j z = Bmom F j a + ∫ s in a..z, Bmom F (j + 1) s / s :=
    Bmom_eq_const_add_integral α k hF hmem j hj ha0 z hz0
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## Differentiability of the moments -/

/-- The `j`-th moment is differentiable on `(0,∞)` with derivative `B_{j+1}(z)/z`, for
`j + 2 ≤ k`. -/
theorem hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Bmom F j z) (Bmom F (j + 1) z / z) z := by
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hcontOn : ContinuousOn (fun s : ℝ => Bmom F (j + 1) s / s) (Set.Ioi 0) :=
    (continuousOn_Bmom α k hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun s hs => by simpa using ne_of_gt hs)
  have hcont : ContinuousAt (fun s : ℝ => Bmom F (j + 1) s / s) z :=
    hcontOn.continuousAt (isOpen_Ioi.mem_nhds hz0)
  have hInt : IntervalIntegrable (fun s : ℝ => Bmom F (j + 1) s / s) volume a z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haz.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a z ha0 haz
  have hder := intervalIntegral.integral_hasDerivAt_right hInt
    (hcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz0) hcont
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝 z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j (by omega) ha0 x hx
  exact hev.hasDerivAt_iff.mpr (hder.const_add (Bmom F j a))

/-- **A.e. differentiability of the top moment.**  For `k ≥ 1`, for almost every `z > 0` the
moment `B_{k-1}` is differentiable at `z` with derivative `B_k(z)/z`. -/
theorem ae_hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      HasDerivAt (fun z => Bmom F (k - 1) z) (Bmom F k z / z) z := by
  set P : ℝ → Prop := fun x => HasDerivAt (fun x => Bmom F (k - 1) x) (Bmom F k x / x) x
    with hP
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      P x := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hle : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 2 := hlt.le
    have hInt : IntervalIntegrable (fun s : ℝ => Bmom F k s / s) volume
        (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact integrableOn_Bmom_div α k hF hmem k le_rfl _ _ hpos hlt
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [Set.uIcc_of_le hle] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
    have hder : HasDerivAt (fun y => ∫ t in (1 / ((n : ℝ) + 1))..y, Bmom F k t / t)
        (Bmom F k x / x) x :=
      hx hxmem (1 / ((n : ℝ) + 1)) ⟨le_rfl, hle⟩
    have hev : (fun y => Bmom F (k - 1) y) =ᶠ[𝓝 x]
        (fun y => Bmom F (k - 1) (1 / ((n : ℝ) + 1))
          + ∫ t in (1 / ((n : ℝ) + 1))..y, Bmom F k t / t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      have h := Bmom_eq_const_add_integral α k hF hmem (k - 1) (by omega) hpos y hy
      simpa [Nat.sub_add_cancel hk] using h
    exact hev.hasDerivAt_iff.mpr (hder.const_add _)
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ P x} = 0 := by
    intro n
    have h := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
    have hset : {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) ∧ ¬ P x}
        = {x | ¬ (x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) → P x)} := by
      ext x
      simp only [Set.mem_setOf_eq, not_imp]
    rw [hset]
    exact h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  have hx' : x ∈ Set.Ioi 0 ∧ ¬ P x := by
    simpa only [Set.mem_setOf_eq, not_imp] using hx
  obtain ⟨hx0, hxn⟩ := hx'
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hn1, hn2⟩, hxn⟩⟩

/-! ## The identity `(D_z^j F_*)(z) = B_j(z)` -/

/-- **The `D_z`-iterates of the angular moment are the moments.**  For `j + 1 ≤ k` and every
`z > 0`, `radIter (B_0) j z = B_j z`. -/
theorem radIter_Bmom_eq (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      radIter (fun z => Bmom F 0 z) j z = Bmom F j z := by
  intro j
  induction j with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hj z hz
      rw [radIter_succ]
      have hev : (radIter (fun z => Bmom F 0 z) n) =ᶠ[𝓝 z] (fun z => Bmom F n z) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      rw [hev.deriv_eq, (hasDerivAt_Bmom α k hF hmem n (by omega) hz).deriv]
      field_simp

/-- **The top `D_z`-iterate**, almost everywhere: for `k ≥ 1` and almost every `z > 0`,
`radIter (B_0) k z = B_k z`. -/
theorem ae_radIter_Bmom_eq_top (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
  have h1 := ae_hasDerivAt_Bmom α k hF hmem hk
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with z hzimp
  intro hzmem
  have hz0 : 0 < z := hzmem
  conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm, radIter_succ]
  have hev : (radIter (fun z => Bmom F 0 z) (k - 1)) =ᶠ[𝓝 z] (fun z => Bmom F (k - 1) z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
    exact radIter_Bmom_eq α k hF hmem (k - 1) (by omega) z' hz'
  rw [hev.deriv_eq, (hzimp hzmem).deriv]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hz0.ne']

/-! ## The slice estimate for `F_*(F)·sin 2θ` -/

/-- **Pointwise domination of the `H^k`-integrand of `F_*(F)·sin 2θ`**, almost everywhere in
`z`.  The `D_z`-summands are the squares of the moments `PsiInt F i z` times `sin 2θ`, and the
mixed summands are the moments times the angular profiles `D_θ^i (sin 2θ)`. -/
theorem HkIntegrand_fstarSin_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) := by
  have hid_lt : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ i < k,
      radIter (fun z => Bmom F 0 z) i z = Bmom F i z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz i hi
    exact radIter_Bmom_eq α k hF hmem i (by omega) z hz
  have hid_top : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      rfl
    · exact ae_radIter_Bmom_eq_top α k hF hmem hk
  filter_upwards [hid_lt, hid_top, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with z hlt htop hz
  intro θ hθ
  have hg : (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      = fun z θ => Bmom F 0 z * Real.sin (2 * θ) := by
    funext z θ
    rw [Bmom_zero]
  have hDz : ∀ i ≤ k, Work.Spaces.DzIter i
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F i z * Real.sin (2 * θ) := by
    intro i hi
    rw [hg, DzIter_fstarSin_eq]
    congr 1
    rcases lt_or_eq_of_le hi with h | h
    · exact hlt i h
    · subst h; exact htop
  have hmix : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F j z * sinProf i θ := by
    intro i j hi hij
    rw [hg, mixed_fstarSin_eq]
    congr 1
    exact hlt j (by omega)
  have hs0 : 0 ≤ Real.sin (2 * θ) := FstarHkOpen.sin_two_nonneg hθ
  have hγ1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hpos2η : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := Real.rpow_nonneg hs0 _
  have hπ2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hUj : ∀ i : ℕ, 0 ≤ FstarHkOpen.Uj F z i := fun i => FstarHkOpen.Uj_nonneg F z i
  have hle_K : ∀ i : ℕ, i ≤ k → FstarHkOpen.angK i ≤ FstarHkOpen.angKsum k := by
    intro i hi
    rw [FstarHkOpen.angKsum]
    exact Finset.single_le_sum (fun a _ => (FstarHkOpen.angK_pos a).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hCS : ∀ i ≤ k, (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * FstarHkOpen.Uj F z i := fun i hi =>
    PsiInt_sq_mul_w_le_open F hF i hz
      (integrableOn_zSummand α k hF hmem i hi (Set.mem_Ici.mpr hz.le))
  rw [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i
            (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hDz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      _ = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_congr rfl fun i _ => FstarHkOpen.zTerm_eq_on (PsiInt F i z) z θ hθ
      _ ≤ ∑ i ∈ Finset.range (k + 1), ((π / 2) * FstarHkOpen.Uj F z i)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_right
            (hCS i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) hpos2η
      _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  · calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i
              (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z * sinProf i θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc, hmix i j hc.1 hc.2]
          · rw [if_neg hc, if_neg hc]
      _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc]
            exact FstarHkOpen.mixedTerm_eq_on α (PsiInt F j z) z (sinProf i) θ hθ
          · rw [if_neg hc, if_neg hc]
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            have hi' : i ≤ k := by omega
            have hj' : j ≤ k := by omega
            have h1 : (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
                * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i :=
              mul_le_mul (hCS j hj')
                (FstarHkOpen.angK_bound i (Work.Spaces.gam α) hγ1 hγ2 hθ)
                (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))
                (mul_nonneg hπ2 (hUj j))
            have h2 : ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k :=
              mul_le_mul_of_nonneg_left (hle_K i hi') (mul_nonneg hπ2 (hUj j))
            exact le_trans h1 h2
          · rw [if_neg hc]
            exact mul_nonneg (mul_nonneg hπ2 (hUj j)) (FstarHkOpen.angKsum_nonneg k)
      _ = (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) := by
          have hrow : ∀ i : ℕ, (∑ j ∈ Finset.range (k + 1),
              ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k))
              = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k := by
            intro i
            rw [← Finset.sum_mul, Finset.mul_sum]
          refine (Finset.sum_congr rfl (fun i _ => hrow i)).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

set_option maxHeartbeats 3000000 in
/-- **The slice estimate.**  For almost every `z ∈ Iz`, the `θ`-integral of the `H^k`-integrand
of `F_*(F)·sin 2θ` is bounded by `hkConst k` times the `θ`-integral of the `H^k`-integrand
of `F`. -/
theorem slice_Hk_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ FstarHkOpen.hkConst k
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  have hmeas : (volume.restrict Work.Spaces.Iz) = volume.restrict (Set.Ioi 0) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  rw [hmeas]
  have hae_le : ∀ {f g : ℝ → ℝ}, (∀ θ ∈ Work.Spaces.Iθ, f θ ≤ g θ) →
      f ≤ᵐ[volume.restrict Work.Spaces.Iθ] g := by
    intro f g h
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), f θ ≤ g θ
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall h
  filter_upwards [HkIntegrand_fstarSin_le_open α k hF hα hα1 hmem,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hzmem.le
  have hsumU : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
    have hint : ∀ j ∈ Finset.range (k + 1), IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      fun j hj => integrableOn_zSummand α k hF hmem j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hzI
    have hsum : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        = ∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1), (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [FstarHkOpen.Uj]
      rw [← MeasureTheory.integral_finsetSum]
      exact hint
    rw [hsum]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (hmem.1 z hzI) (Eventually.of_forall fun θ => ?_)
    rw [Work.Spaces.HkIntegrand]
    exact le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k F z θ)
  have hcont1 : Continuous (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) := by
    refine Continuous.mul continuous_const ?_
    refine Continuous.rpow (by fun_prop) continuous_const (fun θ => Or.inr ?_)
    rw [Work.Spaces.eta]; norm_num
  have hBc : (0 : ℝ) ≤ (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k) :=
    mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j))
      (FstarHkOpen.angKsum_nonneg k))
  have hMint : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ :=
    (hcont1.add continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hZa : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ π / 2 := by
    have hle : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ (1 : ℝ) :=
      fun θ hθ => Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ)
        (FstarHkOpen.sin_two_le_one θ) (by rw [Work.Spaces.eta]; norm_num)
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (hae_le fun θ hθ =>
              Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)
            (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
              (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
            (hae_le hle)
      _ = π / 2 := FstarHkOpen.integral_Iθ_one
  have hZann : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact hae_le fun θ hθ => Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _
  have hIntM : ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k))
      = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := by
    have hInt1 : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact hcont1.continuousOn.integrableOn_compact isCompact_Icc
    have hInt2 : IntegrableOn (fun _ : ℝ => (k + 1) * ((π / 2)
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    rw [MeasureTheory.integral_add hInt1 hInt2]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    ring
  have hπ0 : (0 : ℝ) ≤ π / 2 := by positivity
  have hk0 : (0 : ℝ) ≤ (k + 1) := by positivity
  have hσ : 0 ≤ ∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j :=
    Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j
  have hK : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hfin : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2)
      ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have h1 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2) :=
      mul_le_mul_of_nonneg_left hZa (mul_nonneg hπ0 hσ)
    have h2 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) * (π / 2)
        ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
      have hAB : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
            * (1 + FstarHkOpen.angKsum k) := by
        have he : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
        rw [he]
        have hfac : 1 + (k + 1) * FstarHkOpen.angKsum k
            ≤ (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) := by
          nlinarith [hk0, hK, mul_nonneg hk0 hK]
        have hpos : (0 : ℝ) ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) :=
          mul_nonneg hπ0 hσ
        calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1) * FstarHkOpen.angKsum k)
            = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
          _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * ((1 + (k + 1)) * (1 + FstarHkOpen.angKsum k)) :=
              mul_le_mul_of_nonneg_left hfac hpos
          _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
                * (1 + FstarHkOpen.angKsum k) := by ring
      have h3 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
          ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
        have heq : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
            = ((π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k))
              * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
        rw [heq, FstarHkOpen.hkConst]
        have hc0 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith : (0:ℝ) ≤ 1 + (k + 1)))
            (by linarith : (0:ℝ) ≤ 1 + FstarHkOpen.angKsum k)
        nlinarith [hc0, hσ]
      calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) * (π / 2)
          = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k)) * (π / 2) := by ring
        _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
              * (1 + FstarHkOpen.angKsum k)) * (π / 2) := mul_le_mul_of_nonneg_right hAB hπ0
        _ ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := h3
        _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
            mul_le_mul_of_nonneg_left hsumU (FstarHkOpen.hkConst_pos k).le
    linarith [h1, h2]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
          FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k)) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
          hMint (hae_le fun θ hθ => hz θ hθ)
    _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := hIntM
    _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
        hfin

/-- **Lemma `HardyInequality4` for the angular moment** (Elgindi, §'Elliptic Regularity
Estimates'): for `0 < α ≤ 1` and `F` of class `C^∞` on the open quadrant with `F ∈ ℋ^k`, the
function `F_*(F)(z)·sin 2θ` is bounded in `ℋ^k` by a *universal* multiple (independent of `α`)
of `F`:

`|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`. -/
theorem Fstar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  classical
  refine ⟨FstarHkOpen.hkConst k + 1,
    by linarith [FstarHkOpen.hkConst_pos k], ?_⟩
  intro α F hα hα1 hsm hmem
  have hF : SmoothOpen F := smoothOpen_of_forall hsm
  have hslice := slice_Hk_le_open α k hF hα hα1 hmem
  have hsq : Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      ≤ (FstarHkOpen.hkConst k + 1) ^ 2 * Work.Spaces.HkSq α k F := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (hmem.2.const_mul ((FstarHkOpen.hkConst k + 1) ^ 2)) ?_
    filter_upwards [hslice] with z hz
    have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
    have h3 : FstarHkOpen.hkConst k ≤ (FstarHkOpen.hkConst k + 1) ^ 2 := by
      nlinarith [FstarHkOpen.hkConst_pos k]
    exact le_trans hz (mul_le_mul_of_nonneg_right h3 h2)
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith [FstarHkOpen.hkConst_pos k])]

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.SmoothOpBsll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.EllHyp_F_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst


end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Work.FTS.EllipticEst.H2W.AeW

/-! ## Auxiliary: `bslOp` preserves `C^∞` on the open quadrant -/

private lemma smoothOpen_bslOp {α : ℝ} {v : ℝ → ℝ → ℝ}
    (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α v) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Real.tan θ * v z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero v) := by
    refine Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hv 2))
        h1.pth)
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hv)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl ?_ ?_) h2
  · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2)
          Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl))
      (hv.pzIter 2)
  · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl)
      hv.pz

/-! ## Auxiliary: `Iz`-integrals of functions supported in a `z`-box -/

private lemma setIntegral_Iz_eq_Icc {f : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hvan : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → f z = 0) :
    ∫ z in Work.Spaces.Iz, f z = ∫ z in Set.Icc ε M, f z := by
  have hsubI : Set.Icc ε M ⊆ Set.Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le hε hx.1
  calc ∫ z in Work.Spaces.Iz, f z = ∫ z in Set.Ioi (0:ℝ), f z := by
        refine MeasureTheory.setIntegral_congr_set ?_
        exact (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    _ = ∫ z in Set.Icc ε M, f z :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubI
          (fun z hz => hvan z hz.1 hz.2)

/-- The same support reduction on `Ioi 0` (which is `Iz` up to the null set `{0}`). -/
private lemma setIntegral_Ioi_eq_Icc {f : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hvan : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → f z = 0) :
    ∫ z in Set.Ioi (0:ℝ), f z = ∫ z in Set.Icc ε M, f z := by
  have h1 : (∫ z in Set.Ioi (0:ℝ), f z) = ∫ z in Work.Spaces.Iz, f z := by
    refine MeasureTheory.setIntegral_congr_set ?_
    exact MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)
  rw [h1]
  exact setIntegral_Iz_eq_Icc hε hεM hvan

/-! ## Auxiliary: box integrability of `F² sin(2θ)^{-η}` from `HkMem α 0 F` -/

private lemma boxInt_HkZero {α : ℝ} {F : ℝ → ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hm : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) := by
  have ha : (0:ℝ) < ε := hε
  have hab : ε < M := hεM
  have hsub : Set.Icc ε M ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (F p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ((hF.continuousOn).pow 2) ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hnn : ∀ z ∈ Set.Icc ε M, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hsin2 θ hθ) _)
  have hdom : ∀ (z θ : ℝ), 0 < z → θ ∈ Work.Spaces.Iθ →
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ Work.Spaces.HkIntegrand α 0 F z θ := by
    intro z θ hz hθ
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
      nlinarith [hz]
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hs0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := Real.rpow_nonneg (hsin2 θ hθ) _
    have hF0 : 0 ≤ F z θ ^ 2 := sq_nonneg _
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α F z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq F z θ (hsin2 θ hθ)]
    have hs0' : 0 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := hs0
    have hstep : F z θ ^ 2 * 1 ≤ F z θ ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_left hw2 hF0
    have hstep2 := mul_le_mul_of_nonneg_right hstep hs0'
    calc F z θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        = F z θ ^ 2 * 1 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ F z θ ^ 2 * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
          hstep2
  have hsl : ∀ s ∈ Set.Icc ε M, Integrable (fun θ : ℝ =>
      (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hm.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact hdom s θ hspos hθ
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Icc ε M)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F s θ)
        (volume.restrict (Set.Icc ε M)) := hm.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · have hle : (volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (F p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
          ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc ε M))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc ε M) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
            with θ hθ
          exact hnn s hs θ hθ)
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
          with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
          with θ hθ
        exact hdom s θ hspos hθ
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

/-! ## Auxiliary: domination for box integrability -/

private lemma boxInt_mono {f g : ℝ → ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε)
    (hbig : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc ε M ×ˢ Work.Spaces.Iθ))
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hle : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)),
      ‖f p.1 p.2‖ ≤ g p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry f) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) := by
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hsub : Set.Icc ε M ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨Set.mem_Ici.mpr (le_trans hε.le hz.1), hθ⟩
  have hmle : ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ))
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [Measure.prod_restrict]
    exact Measure.restrict_mono hsub le_rfl
  have haesm : AEStronglyMeasurable (Function.uncurry f)
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hf).mono_measure hmle
  refine hbig.mono' haesm ?_
  filter_upwards [hle] with p hp
  obtain ⟨a, b⟩ := p
  simpa only [Function.uncurry_apply_pair] using hp

/-! ## Auxiliary: AM–GM with a positive weight -/

private lemma abs_mul_le_amgm (a b s : ℝ) (hs : 0 < s) :
    |a * b| ≤ (1 / 2) * (a ^ 2 * s + b ^ 2 / s) := by
  have h := two_mul_le_add_sq (|a| * Real.sqrt s) (|b| / Real.sqrt s)
  have h1 : (|a| * Real.sqrt s) ^ 2 = a ^ 2 * s := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hs.le]
  have h2 : (|b| / Real.sqrt s) ^ 2 = b ^ 2 / s := by
    rw [div_pow, sq_abs, Real.sq_sqrt hs.le]
  have h3 : 2 * (|a| * Real.sqrt s) * (|b| / Real.sqrt s) = 2 * |a * b| := by
    rw [abs_mul]; field_simp
  rw [h1, h2, h3] at h
  linarith

/-- The θ-wise AM–GM behind the marginal Cauchy–Schwarz:
`2|f g| ≤ HkIntegrand α 0 f + HkIntegrand α 0 g` on the box. -/
private lemma abs_mul_le_half_Hk {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    ‖f z θ * g z θ‖ ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 f z θ
      + Work.Spaces.HkIntegrand α 0 g z θ) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.Spaces.sin_two_nonneg_of_Iθ (Set.Ioo_subset_Icc_self hθ)
  have hs1 : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.EllipticEst.Honest.one_le_sEta hθ
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
    nlinarith [hz]
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hpos : 0 < (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hw1) 2)
      (lt_of_lt_of_le zero_lt_one hs1)
  have hb : 1 ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by nlinarith
  have h := abs_mul_le_amgm (f z θ) (g z θ)
    ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) hpos
  have h2 : (g z θ) ^ 2 / ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      ≤ (g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
    rw [div_le_iff₀ hpos]
    have hb2 : 1 ≤ ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) :=
      one_le_mul_of_one_le_of_one_le hb hb
    calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (g z θ) ^ 2 * (((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      _ = (g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by ring
  rw [Real.norm_eq_abs, abs_mul]
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α f z θ,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq f z θ hsin,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ hsin]
  rw [abs_mul] at h
  exact le_trans h (by linarith [h2])

/-- The square of a function vanishes on `(0,ε) ∪ (M,∞)` together with its first two
derivatives, when the function does. -/
private lemma deriv_deriv_eq_zero_of_supp {g : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M)
    (hleft : ∀ z, 0 < z → z < ε → g z = 0) (hright : ∀ z, M < z → g z = 0) :
    (∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → deriv g z = 0) ∧
      (∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → deriv (deriv g) z = 0) := by
  have hg : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → g =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
    intro z hz hz'
    have hz'' : z < ε ∨ M < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    rcases hz'' with hlt | hgt
    · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
      exact hleft w hw0 hw
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact hright w hw
  constructor
  · intro z hz hz'
    rw [Filter.EventuallyEq.deriv_eq (hg z hz hz')]
    simp
  · intro z hz hz'
    have h1 : deriv g =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      have hz'' : z < ε ∨ M < z := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        have h2 := Filter.EventuallyEq.deriv_eq (hg w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw))
        simpa using h2
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        have h2 := Filter.EventuallyEq.deriv_eq (hg w (lt_trans (lt_trans hε hεM) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw))
        simpa using h2
    rw [Filter.EventuallyEq.deriv_eq h1]
    simp

/-- Almost every point of the box `[ε,M] ×ˢ Iθ` has second coordinate in the open interval. -/
private lemma ae_mem_Ioo_snd {ε M : ℝ} (hε : 0 < ε) :
    ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Icc ε M ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [MeasureTheory.ae_restrict_iff' hboxm, MeasureTheory.ae_iff]
  refine measure_mono_null (t := Set.Icc ε M ×ˢ ({0} ∪ {Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq, not_imp] at hp
    obtain ⟨hpbox, hpne⟩ := hp
    refine ⟨hpbox.1, ?_⟩
    rcases eq_or_lt_of_le hpbox.2.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hpbox.2.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd ⟨h, h2⟩ hpne
  · have h1 : (volume : Measure (ℝ × ℝ)) (Set.Icc ε M ×ˢ ({0} ∪ {Real.pi / 2} : Set ℝ))
        = volume (Set.Icc ε M) * volume ({0} ∪ {Real.pi / 2} : Set ℝ) :=
      MeasureTheory.Measure.prod_prod _ _
    rw [h1, measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2)), mul_zero]

/-! ## Auxiliary: the fixed-θ radial integration by parts on the positive half-line -/

private lemma fixedThetaIBP (α : ℝ) (σ φ : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hσ : ContDiffOn ℝ 2 σ (Set.Ioi 0))
    (hσsupp : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b → σ z = 0)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) :
    (∫ z in Set.Ioi (0 : ℝ), σ z * (α ^ 2 * z ^ 2 * deriv (deriv φ) z
        + (α * (5 + α) * z) * deriv φ z) * φ z)
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), σ z * (z * deriv φ z) ^ 2)
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z => z ^ 2 * σ z)) z * (φ z) ^ 2)
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun z => z * σ z) z * (φ z) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hW_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (fun y : ℝ => y ^ 2 * σ y) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : (fun y : ℝ => y ^ 2 * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        rw [hσsupp w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)]
        ring
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        rw [hσsupp w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)]
        ring
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hddW_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : deriv (fun y : ℝ => y ^ 2 * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        exact hW_off w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        exact hW_off w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hzσ_off : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc a b →
      deriv (fun y : ℝ => y * σ y) z = 0 := by
    intro z hz hz'
    have hz'' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hev : (fun y : ℝ => y * σ y) =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hz'' with hlt | hgt
      · filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Iio.mem_nhds hlt] with w hw0 hw
        rw [hσsupp w hw0 (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)]
        ring
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        rw [hσsupp w (lt_trans (lt_trans ha hab) hw) (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)]
        ring
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  have hW2σ : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * σ y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hW2σ₁ : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * σ y)) (Set.Ioi 0) :=
    hW2σ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hW1σ : ContDiffOn ℝ 2 (fun y : ℝ => y * σ y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hσ
  have hφ₁ : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcontσ : ContinuousOn σ (Set.Icc a b) := hσ.continuousOn.mono hsub
  have hcontφ : ContinuousOn φ (Set.Icc a b) := hφ.continuousOn.mono hsub
  have hcontdφ : ContinuousOn (deriv φ) (Set.Icc a b) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddφ : ContinuousOn (deriv (deriv φ)) (Set.Icc a b) :=
    (hφ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdW : ContinuousOn (deriv (fun y : ℝ => y ^ 2 * σ y)) (Set.Icc a b) :=
    (hW2σ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddW : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * σ y))) (Set.Icc a b) :=
    (hW2σ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdzσ : ContinuousOn (deriv (fun y : ℝ => y * σ y)) (Set.Icc a b) :=
    (hW1σ.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * σ z * φ z * deriv (deriv φ) z)
      (Set.Ioi 0) :=
    ((((continuousOn_id.pow 2).mul hcontσ).mul hcontφ).mul hcontddφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * φ z * deriv φ z) (Set.Ioi 0) :=
    ((hcontdW.mul hcontφ).mul hcontdφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (fun y : ℝ => y ^ 2 * σ y) z * φ z * deriv φ z = 0
          rw [hW_off z hz.1 hz.2]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    (hcontσ.mul ((continuousOn_id.mul hcontdφ).pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show σ z * (z * deriv φ z) ^ 2 = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z * (φ z) ^ 2) (Set.Ioi 0) :=
    (hcontddW.mul (hcontφ.pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (deriv (fun y : ℝ => y ^ 2 * σ y)) z * (φ z) ^ 2 = 0
          rw [hddW_off z hz.1 hz.2]; ring)
  have hi1' : IntegrableOn (fun z : ℝ => σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      (Set.Ioi 0) :=
    hi1.congr_fun (fun z _ => by ring) measurableSet_Ioi
  have hIntB0 : IntegrableOn (fun z : ℝ => σ z * z * deriv φ z * φ z) (Set.Ioi 0) :=
    (((hcontσ.mul continuousOn_id).mul hcontdφ).mul hcontφ).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show σ z * z * deriv φ z * φ z = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hIntB1 : IntegrableOn (fun z : ℝ => (z * σ z) * (2 * φ z * deriv φ z)) (Set.Ioi 0) :=
    ((continuousOn_id.mul hcontσ).mul (((continuous_const.continuousOn).mul hcontφ).mul hcontdφ))
      |>.integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show (z * σ z) * (2 * φ z * deriv φ z) = 0
          rw [hσsupp z hz.1 hz.2]; ring)
  have hIntB2 : IntegrableOn (fun z : ℝ => deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2)
      (Set.Ioi 0) :=
    (hcontdzσ.mul (hcontφ.pow 2)).integrableOn_Icc
      |>.of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun z hz => by
          show deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2 = 0
          rw [hzσ_off z hz.1 hz.2]; ring)
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hσsupp z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hσsupp z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb3 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hW_off z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb4 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2)
      atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * σ y) z * (φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hW_off z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb5 : Tendsto (fun z : ℝ => (z * σ z) * (φ z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => (z * σ z) * (φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hσsupp z hz.1 (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb6 : Tendsto (fun z : ℝ => (z * σ z) * (φ z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => (z * σ z) * (φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hσsupp z (lt_trans (lt_trans ha hab) hz) (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hzvw : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * σ y) (deriv (fun y : ℝ => y * σ y) z) z := by
    intro z hz
    exact (hW1σ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hφ2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (φ y) ^ 2) (2 * φ z * deriv φ z) z := by
    intro z hz
    have hφz : HasDerivAt φ (deriv φ z) z :=
      (hφ.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
    convert hφz.pow 2 using 1
    simp [pow_one, mul_assoc]
  have key1 : (∫ z in Set.Ioi (0 : ℝ), σ z * z ^ 2 * deriv (deriv φ) z * φ z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2)
        - (∫ z in Set.Ioi (0 : ℝ), σ z * (z * deriv φ z) ^ 2) :=
    Work.FTS.EllipticEst.remov.ibpZZ σ φ hσ hφ hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  have hIBP2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun y : ℝ => y * σ y) (u' := fun y : ℝ => deriv (fun y : ℝ => y * σ y) y)
    (v := fun y : ℝ => (φ y) ^ 2) (v' := fun y : ℝ => 2 * φ y * deriv φ y)
    hzvw hφ2 hIntB1 hIntB2 hb5 hb6
  have hIBP2' : (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
      = -(∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2) := by
    simpa using hIBP2
  have key2 : (∫ z in Set.Ioi (0 : ℝ), σ z * z * deriv φ z * φ z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * σ y) z * (φ z) ^ 2) := by
    have hcongr : (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
        = 2 * (∫ z in Set.Ioi (0 : ℝ), σ z * z * deriv φ z * φ z) := by
      rw [show (∫ z in Set.Ioi (0 : ℝ), (z * σ z) * (2 * φ z * deriv φ z))
            = ∫ z in Set.Ioi (0 : ℝ), 2 * (σ z * z * deriv φ z * φ z) from
          setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
      rw [integral_const_mul]
    rw [hcongr] at hIBP2'
    linarith
  rw [show (∫ z in Set.Ioi (0 : ℝ), σ z * (α ^ 2 * z ^ 2 * deriv (deriv φ) z
          + (α * (5 + α) * z) * deriv φ z) * φ z)
        = ∫ z in Set.Ioi (0 : ℝ), α ^ 2 * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
            + (α * (5 + α)) * (σ z * z * deriv φ z * φ z) from
      setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [integral_add (hi1'.const_mul (α ^ 2)) (hIntB0.const_mul (α * (5 + α))),
    integral_const_mul, integral_const_mul, key1, key2]
  ring

end Work.FTS.EllipticEst.H2W.AeW

namespace Work.FTS.EllipticEst.H2W.AeW

set_option maxHeartbeats 6400000 in
theorem aeTruncWHon (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hmemU : Work.Spaces.HkMem α 0 u)
    (hmemGU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (hcpt : HasCompactSupport χ)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Icc (0:ℝ) ε, χ z = 0)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
            Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
              Work.Spaces.Iθ
          ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
  obtain ⟨hαpos, hα4, hbeq, hdir0, hdirpi, hsmA, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩ := h
  obtain ⟨ε, hεpos, hεχ⟩ := hε
  have hbdd : Bornology.IsBounded (tsupport χ) := hcpt.isCompact.isBounded
  obtain ⟨R, hRpos, hRle⟩ := hbdd.exists_pos_norm_le
  set M : ℝ := max R ε + 1 with hMdef
  have hmax1 : (0:ℝ) ≤ max R ε := le_trans (le_of_lt hεpos) (le_max_right R ε)
  have hεM : ε < M := by rw [hMdef]; have := le_max_right R ε; linarith
  have hRlt : R ≤ M := by rw [hMdef]; have := le_max_left R ε; linarith
  have hMpos : 0 < M := lt_trans hεpos hεM
  have hMχ : ∀ z, M < z → χ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hne)
    have h1 := hRle z hmem
    have h2 : ‖z‖ = z := by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h2] at h1
    linarith
  -- ## 0. abbreviations
  let Φ : ℝ → ℝ := fun z => χ z * (Work.Spaces.w z) ^ 2
  let W2 : ℝ → ℝ := deriv (deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2))
  let W1 : ℝ → ℝ := deriv (fun z => χ z * (Work.Spaces.w z) ^ 2 * z)
  let W2e : ℝ → ℝ := deriv (deriv (fun z => z ^ 2 * Φ z))
  let W1e : ℝ → ℝ := deriv (fun z => z * Φ z)
  let rad : ℝ → ℝ → ℝ := fun z θ =>
    -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ - (α * (5 + α) * z) * Work.Spaces.pz u z θ
  let Fr : ℝ → ℝ → ℝ := fun z θ => Φ z * (rad z θ * u z θ)
  let FL : ℝ → ℝ → ℝ := fun z θ => Φ z * (Work.Elliptic.Lzero u z θ * u z θ)
  let HH : ℝ → ℝ → ℝ := fun z θ => Φ z * (G z θ * u z θ)
  let G2 : ℝ → ℝ → ℝ := fun z θ => Φ z * (z * Work.Spaces.pz u z θ) ^ 2
  let GW2 : ℝ → ℝ → ℝ := fun z θ => W2e z * (u z θ) ^ 2
  let GW1 : ℝ → ℝ → ℝ := fun z θ => W1e z * (u z θ) ^ 2
  let Rad : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, rad z θ * u z θ
  let Lz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ
  let Dint : ℝ → ℝ → ℝ := fun z θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ
  let Eint : ℝ → ℝ → ℝ := fun z θ => (z * Work.Spaces.pz u z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ
  let Fint : ℝ → ℝ → ℝ := fun z θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  let Gint : ℝ → ℝ → ℝ := fun z θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  change (∫ z in Work.Spaces.Iz, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, Φ z
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, Φ z
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            W2 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            W1 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
  -- ## 1. support facts
  have hΦsupp : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → Φ z = 0 := by
    intro z hz hz'
    have hz'' : z < ε ∨ M < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz'
    have hχ0 : χ z = 0 := by
      rcases hz'' with hlt | hgt
      · exact hεχ z ⟨le_of_lt hz, le_of_lt hlt⟩
      · exact hMχ z hgt
    dsimp only [Φ]
    rw [hχ0]; ring
  have hΦL : ∀ z, 0 < z → z < ε → Φ z = 0 := fun z hz hlt =>
    hΦsupp z hz (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hlt)
  have hΦR : ∀ z, M < z → Φ z = 0 := fun z hgt =>
    hΦsupp z (lt_trans (lt_trans hεpos hεM) hgt)
      (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hgt)
  have hW2e0 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W2e z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM (g := fun z => z ^ 2 * Φ z)
      (fun z hz hlt => by rw [hΦL z hz hlt]; ring)
      (fun z hgt => by rw [hΦR z hgt]; ring)).2
  have hW1e0 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W1e z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM (g := fun z => z * Φ z)
      (fun z hz hlt => by rw [hΦL z hz hlt]; ring)
      (fun z hgt => by rw [hΦR z hgt]; ring)).1
  have hW20 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W2 z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM
      (g := fun z => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      (fun z hz hlt => by
        have h := hΦL z hz hlt
        dsimp only [Φ] at h
        rw [h]; ring)
      (fun z hgt => by
        have h := hΦR z hgt
        dsimp only [Φ] at h
        rw [h]; ring)).2
  have hW10 : ∀ z ∈ Set.Ioi (0:ℝ), z ∉ Set.Icc ε M → W1 z = 0 :=
    (deriv_deriv_eq_zero_of_supp hεpos hεM
      (g := fun z => χ z * (Work.Spaces.w z) ^ 2 * z)
      (fun z hz hlt => by
        have h := hΦL z hz hlt
        dsimp only [Φ] at h
        rw [h]; ring)
      (fun z hgt => by
        have h := hΦR z hgt
        dsimp only [Φ] at h
        rw [h]; ring)).1
  -- ## 2. the weight calculus
  have hw_cd : ContDiffOn ℝ 2 (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    show ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ContDiffOn.div ((contDiffOn_const.add contDiffOn_id).pow 2) (contDiffOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hw2_cd : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    simpa only [Pi.mul_apply, pow_two] using ContDiffOn.mul hw_cd hw_cd
  have hΦC2 : ContDiffOn ℝ 2 Φ (Set.Ioi 0) := by
    dsimp only [Φ]
    exact ContDiffOn.mul hχ.contDiffOn hw2_cd
  have hΦcont : ContinuousOn Φ (Set.Icc ε M) :=
    hΦC2.continuousOn.mono (fun x hx => lt_of_lt_of_le hεpos hx.1)
  obtain ⟨CΦ, hCΦ⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hΦcont
  have hCΦ0 : 0 ≤ CΦ := by
    have h1 := hCΦ ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (Φ ε)]
  have hW2e_cont : ContinuousOn W2e (Set.Ioi 0) := by
    dsimp only [W2e]
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * Φ z) (Set.Ioi 0) :=
      ContDiffOn.mul (contDiffOn_id.pow 2) hΦC2
    have h2 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * Φ z)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have h3 : ContDiffOn ℝ 0 (deriv (deriv (fun z : ℝ => z ^ 2 * Φ z))) (Set.Ioi 0) :=
      h2.deriv_of_isOpen isOpen_Ioi le_rfl
    exact h3.continuousOn
  have hW1e_cont : ContinuousOn W1e (Set.Ioi 0) := by
    dsimp only [W1e]
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => z * Φ z) (Set.Ioi 0) :=
      ContDiffOn.mul contDiffOn_id hΦC2
    have h2 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z * Φ z)) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h2.continuousOn
  obtain ⟨CW2, hCW2⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hW2e_cont.mono (fun x hx => lt_of_lt_of_le hεpos hx.1))
  obtain ⟨CW1, hCW1⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hW1e_cont.mono (fun x hx => lt_of_lt_of_le hεpos hx.1))
  have hCW20 : 0 ≤ CW2 := by
    have h1 := hCW2 ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (W2e ε)]
  have hCW10 : 0 ≤ CW1 := by
    have h1 := hCW1 ε ⟨le_rfl, le_of_lt hεM⟩
    linarith [norm_nonneg (W1e ε)]
  -- ## 3. box integrability
  have huSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hboxU : MeasureTheory.IntegrableOn (Function.uncurry Fint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM huSO hmemU
  have hgradSO : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
        Work.FTS.EllipticEst.Q0 := contDiffOn_fst
    have h2 := ContDiffOn.mul h1 huSO.pz
    have h3 : Function.uncurry (Work.FTS.EllipticEst.H2W.Ae.grad u)
        = fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2 := by funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, h3]
    exact h2
  have hboxD : MeasureTheory.IntegrableOn (Function.uncurry Eint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM hgradSO hmemGU
  have hrad2SO : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
        Work.FTS.EllipticEst.Q0 := contDiffOn_fst.pow 2
    have h2 := ContDiffOn.mul h1 (huSO.pzIter 2)
    have h3 : Function.uncurry (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2 := by funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, h3]
    exact h2
  have hboxZ : MeasureTheory.IntegrableOn (Function.uncurry Dint) (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    boxInt_HkZero hεpos hεM hrad2SO hmemRad2
  have hboxm : MeasurableSet (Set.Icc ε M ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ## 4. the four product integrabilities
  have hcontG2 : ContinuousOn (Function.uncurry G2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
      hΦC2.continuousOn.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul ((continuousOn_fst.mul huSO.pz.continuousOn).pow 2)
  have IntG2 : Integrable (Function.uncurry G2)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CΦ * Eint z θ) hεpos ?_ hcontG2 ?_
    · exact hboxD.const_mul CΦ
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hΦb : |Φ p.1| ≤ CΦ := by
        have h := hCΦ p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [G2]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
          ≤ (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (p.1 * Work.Spaces.pz u p.1 p.2)]
      have h3 : |(p.1 * Work.Spaces.pz u p.1 p.2) ^ 2|
          = (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hΦb h2 (sq_nonneg _) hCΦ0
  have hcontGW2 : ContinuousOn (Function.uncurry GW2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => W2e p.1) Work.FTS.EllipticEst.Q0 :=
      hW2e_cont.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul (huSO.continuousOn.pow 2)
  have IntGW2 : Integrable (Function.uncurry GW2)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CW2 * Fint z θ) hεpos ?_ hcontGW2 ?_
    · exact hboxU.const_mul CW2
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hWb : |W2e p.1| ≤ CW2 := by
        have h := hCW2 p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [GW2]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (u p.1 p.2) ^ 2 ≤ (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (u p.1 p.2)]
      have h3 : |(u p.1 p.2) ^ 2| = (u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hWb h2 (sq_nonneg _) hCW20
  have hcontGW1 : ContinuousOn (Function.uncurry GW1) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => W1e p.1) Work.FTS.EllipticEst.Q0 :=
      hW1e_cont.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h1.mul (huSO.continuousOn.pow 2)
  have IntGW1 : Integrable (Function.uncurry GW1)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (g := fun z θ => CW1 * Fint z θ) hεpos ?_ hcontGW1 ?_
    · exact hboxU.const_mul CW1
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have hz : p.1 ∈ Set.Icc ε M := hp.1
      have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta p.2 :=
        Work.FTS.EllipticEst.Honest.one_le_sEta hpq
      have hWb : |W1e p.1| ≤ CW1 := by
        have h := hCW1 p.1 hz
        rwa [Real.norm_eq_abs] at h
      dsimp only [GW1]
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : (u p.1 p.2) ^ 2 ≤ (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2 := by
        nlinarith [hs1, sq_nonneg (u p.1 p.2)]
      have h3 : |(u p.1 p.2) ^ 2| = (u p.1 p.2) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [h3]
      exact mul_le_mul hWb h2 (sq_nonneg _) hCW10
  have hcontFr : ContinuousOn (Function.uncurry Fr) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
      hΦC2.continuousOn.comp continuousOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    have hrad : ContinuousOn (fun p : ℝ × ℝ =>
        -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 u p.1 p.2
          - (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      ((((continuousOn_fst.pow 2).const_mul (α ^ 2)).neg).mul (huSO.pzIter 2).continuousOn).sub
        (((continuousOn_fst.const_mul (α * (5 + α))).mul huSO.pz.continuousOn))
    exact h1.mul (hrad.mul huSO.continuousOn)
  have hptFr : ∀ z ∈ Set.Icc ε M, ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), ‖Fr z θ‖ ≤
      CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint z θ
        + α * (5 + α) * M * (1 / ε ^ 2) * Eint z θ
        + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le hεpos hz.1
    have hzM : z ≤ M := hz.2
    have hzε : ε ≤ z := hz.1
    have hs1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
    have hs0 : 0 < Work.FTS.EllipticEst.sEta θ := lt_of_lt_of_le zero_lt_one hs1
    have hΦb : |Φ z| ≤ CΦ := by
      have h := hCΦ z hz
      rwa [Real.norm_eq_abs] at h
    -- the three key atom-bounds
    have hkey1 : (Work.Spaces.pzIter 2 u z θ) ^ 2
        ≤ (1 / ε ^ 4) * Dint z θ := by
      have hD : ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
          ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have h1 : ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2 := by
          have h2 : ε ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ hεpos.le hzε 4
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        have h3 : z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            = (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := by ring
        have h4 : (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          have h5 : (0:ℝ) ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := sq_nonneg _
          nlinarith [hs1, h5]
        calc ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2
            ≤ z ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2 := h1
          _ = (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 := h3
          _ ≤ (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := h4
      calc (Work.Spaces.pzIter 2 u z θ) ^ 2
          = (ε ^ 4)⁻¹ * (ε ^ 4 * (Work.Spaces.pzIter 2 u z θ) ^ 2) := by
            rw [inv_mul_cancel_left₀ (by positivity : (ε:ℝ) ^ 4 ≠ 0)]
        _ ≤ (ε ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (1 / ε ^ 4) * Dint z θ := by ring
    have hkey2 : (Work.Spaces.pz u z θ) ^ 2 ≤ (1 / ε ^ 2) * Eint z θ := by
      have hD : ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2
          ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have h1 : ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2
            ≤ z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := by
          have h2 : ε ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hεpos.le hzε 2
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        have h3 : z ^ 2 * (Work.Spaces.pz u z θ) ^ 2
            = (z * Work.Spaces.pz u z θ) ^ 2 := by ring
        have h4 : (z * Work.Spaces.pz u z θ) ^ 2
            ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          have h5 : (0:ℝ) ≤ (z * Work.Spaces.pz u z θ) ^ 2 := sq_nonneg _
          nlinarith [hs1, h5]
        calc ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2 ≤ z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 := h1
          _ = (z * Work.Spaces.pz u z θ) ^ 2 := h3
          _ ≤ (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := h4
      calc (Work.Spaces.pz u z θ) ^ 2
          = (ε ^ 2)⁻¹ * (ε ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by
            rw [inv_mul_cancel_left₀ (by positivity : (ε:ℝ) ^ 2 ≠ 0)]
        _ ≤ (ε ^ 2)⁻¹ * ((z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
        _ = (1 / ε ^ 2) * Eint z θ := by ring
    have hkey3 : (u z θ) ^ 2 ≤ Fint z θ := by
      have h5 : (0:ℝ) ≤ (u z θ) ^ 2 := sq_nonneg _
      nlinarith [hs1, h5]
    -- the two AM–GM steps
    have hc1 : 0 ≤ α ^ 2 * M ^ 2 := by nlinarith [hαpos, hMpos]
    have hc2 : 0 ≤ α * (5 + α) * M := by nlinarith [hαpos, hMpos]
    have hAB : |Work.Spaces.pzIter 2 u z θ| * |u z θ|
        ≤ ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2 := by
      have h := abs_mul_le_amgm (Work.Spaces.pzIter 2 u z θ) (u z θ) 1 one_pos
      rw [abs_mul, mul_one, div_one] at h
      linarith [h]
    have hBB : |Work.Spaces.pz u z θ| * |u z θ|
        ≤ ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2 := by
      have h := abs_mul_le_amgm (Work.Spaces.pz u z θ) (u z θ) 1 one_pos
      rw [abs_mul, mul_one, div_one] at h
      linarith [h]
    have e1 : α ^ 2 * M ^ 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
        ≤ α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by
      have hh : (Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2
          ≤ (1 / ε ^ 4) * Dint z θ + Fint z θ := add_le_add hkey1 hkey3
      have hc : (0:ℝ) ≤ α ^ 2 * M ^ 2 / 2 := by nlinarith [hαpos, hMpos]
      calc α ^ 2 * M ^ 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
          = α ^ 2 * M ^ 2 / 2 * ((Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) := by ring
        _ ≤ α ^ 2 * M ^ 2 / 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) :=
            mul_le_mul_of_nonneg_left hh hc
        _ = α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by ring
    have e2 : α * (5 + α) * M * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2
        ≤ α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by
      have hh : (Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2
          ≤ (1 / ε ^ 2) * Eint z θ + Fint z θ := add_le_add hkey2 hkey3
      have hc : (0:ℝ) ≤ α * (5 + α) * M / 2 := by nlinarith [hαpos, hMpos]
      calc α * (5 + α) * M * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2
          = α * (5 + α) * M / 2 * ((Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) := by ring
        _ ≤ α * (5 + α) * M / 2 * ((1 / ε ^ 2) * Eint z θ + Fint z θ) :=
            mul_le_mul_of_nonneg_left hh hc
        _ = α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by ring
    have hAB' : α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
        ≤ α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2 := by
      have h := mul_le_mul_of_nonneg_left hAB hc1
      linarith [h, e1]
    have hBB' : α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|)
        ≤ α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2 := by
      have h := mul_le_mul_of_nonneg_left hBB hc2
      linarith [h, e2]
    -- the bound on `rad`
    have hradb : |rad z θ| ≤ (α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
        + (α * (5 + α) * M) * |Work.Spaces.pz u z θ| := by
      have h1 : |rad z θ| ≤ (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * z) * |Work.Spaces.pz u z θ| := by
        have h := abs_add_le ((-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 u z θ)
          (-((α * (5 + α) * z) * Work.Spaces.pz u z θ))
        rw [abs_neg] at h
        have h2 : |(-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 u z θ|
            = (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ| := by
          rw [abs_mul, abs_neg, abs_of_nonneg (by nlinarith [hαpos, hz0])]
        have h3 : |(α * (5 + α) * z) * Work.Spaces.pz u z θ|
            = (α * (5 + α) * z) * |Work.Spaces.pz u z θ| := by
          rw [abs_mul, abs_of_nonneg (by nlinarith [hαpos, hz0])]
        rw [h2, h3] at h
        dsimp only [rad]
        exact h
      have hz2 : z ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hz0.le hzM 2
      have h4 : (α ^ 2 * z ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          ≤ (α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 (sq_nonneg α))
          (abs_nonneg _)
      have h5 : (α * (5 + α) * z) * |Work.Spaces.pz u z θ|
          ≤ (α * (5 + α) * M) * |Work.Spaces.pz u z θ| := by
        have hc0 : (0:ℝ) ≤ α * (5 + α) := by nlinarith [hαpos]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzM hc0) (abs_nonneg _)
      exact le_trans h1 (add_le_add h4 h5)
    -- assemble
    have hFr1 : ‖Fr z θ‖ = |Φ z| * |rad z θ| * |u z θ| := by
      dsimp only [Fr]
      rw [Real.norm_eq_abs]
      simp only [abs_mul]
      ring
    rw [hFr1]
    have hstep : |rad z θ| * |u z θ| ≤ ((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ| :=
      mul_le_mul_of_nonneg_right hradb (abs_nonneg _)
    have hdist : ((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
          + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ|
        = α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|) := by ring
    calc |Φ z| * |rad z θ| * |u z θ|
        ≤ CΦ * |rad z θ| * |u z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΦb (abs_nonneg _))
            (abs_nonneg _)
      _ = CΦ * (|rad z θ| * |u z θ|) := by ring
      _ ≤ CΦ * (((α ^ 2 * M ^ 2) * |Work.Spaces.pzIter 2 u z θ|
            + (α * (5 + α) * M) * |Work.Spaces.pz u z θ|) * |u z θ|) :=
          mul_le_mul_of_nonneg_left hstep hCΦ0
      _ = CΦ * (α ^ 2 * M ^ 2 * (|Work.Spaces.pzIter 2 u z θ| * |u z θ|)
            + α * (5 + α) * M * (|Work.Spaces.pz u z θ| * |u z θ|)) := by
          rw [hdist]
      _ ≤ CΦ * (α ^ 2 * M ^ 2 * ((1 / ε ^ 4) * Dint z θ + Fint z θ) / 2
            + α * (5 + α) * M * ((1 / ε ^ 2) * Eint z θ + Fint z θ) / 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hAB' hBB') hCΦ0
      _ = CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint z θ
            + α * (5 + α) * M * (1 / ε ^ 2) * Eint z θ
            + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) := by ring
  have IntFr : Integrable (Function.uncurry Fr)
      ((volume.restrict (Set.Icc ε M)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Work.FTS.EllipticEst.volume_restrict_box ε M]
    refine boxInt_mono (f := Fr)
      (g := fun z θ => CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)) * Dint z θ
        + CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2)) * Eint z θ
        + CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint z θ) hεpos ?_ hcontFr ?_
    · exact ((hboxZ.const_mul (CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)))).add
        (hboxD.const_mul (CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2))))).add
        (hboxU.const_mul (CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M)))
    · filter_upwards [ae_restrict_mem hboxm,
        ae_mem_Ioo_snd (ε := ε) (M := M) hεpos] with p hp hpq
      have h := hptFr p.1 hp.1 p.2 hpq
      calc ‖Fr p.1 p.2‖ ≤ CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4) * Dint p.1 p.2
            + α * (5 + α) * M * (1 / ε ^ 2) * Eint p.1 p.2
            + (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint p.1 p.2) := h
        _ = CΦ / 2 * (α ^ 2 * M ^ 2 * (1 / ε ^ 4)) * Dint p.1 p.2
            + CΦ / 2 * (α * (5 + α) * M * (1 / ε ^ 2)) * Eint p.1 p.2
            + CΦ / 2 * (α ^ 2 * M ^ 2 + α * (5 + α) * M) * Fint p.1 p.2 := by ring
  -- ## 5. the LHS honesty and reduction to the `G`-integral  (step (6a))
  have hvol0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by rw [MeasureTheory.ae_iff]; simp
  have hvolpi : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simp
  have hIoo_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hvol0, hvolpi] with θ hθ0 hθpi hmem
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hθ0), lt_of_le_of_ne hmem.2 hθpi⟩
  have hIθ_mem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  have hslice' : ∀ᵐ z ∂(volume.restrict (Set.Icc ε M)),
      (MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ
        ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ) :=
    ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_of_lt_of_le hεpos hx.1) hslice
  have hHkG : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 G z θ
        = (G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α G z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq G z θ (Work.Spaces.sin_two_nonneg_of_Iθ hθ),
      Work.FTS.EllipticEst.sEta]
  have hHkU : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 u z θ
        = (u z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α u z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq u z θ (Work.Spaces.sin_two_nonneg_of_Iθ hθ),
      Work.FTS.EllipticEst.sEta]
  -- the θ-Cauchy–Schwarz bound, with the (junk) non-integrable case handled by `integral_undef`
  have hGu_bound : ∀ z ∈ Set.Icc ε M,
      ‖∫ θ in Work.Spaces.Iθ, G z θ * u z θ‖
        ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hεpos hz.1
    have hziz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hzpos)
    have hKG : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (volume.restrict Work.Spaces.Iθ) := hmemG.1 z hziz
    have hKU : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
        (volume.restrict Work.Spaces.Iθ) := hmemU.1 z hziz
    have hw1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
      nlinarith [hzpos]
    by_cases hInt : Integrable (fun θ => G z θ * u z θ) (volume.restrict Work.Spaces.Iθ)
    · rw [Real.norm_eq_abs]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs (f := fun θ => G z θ * u z θ)
        (μ := volume.restrict Work.Spaces.Iθ)) ?_
      have hmono : ∫ θ in Work.Spaces.Iθ, ‖G z θ * u z θ‖
          ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) := by
        refine MeasureTheory.integral_mono_ae hInt.norm ((hKG.add hKU).const_mul (1/2)) ?_
        filter_upwards [hIoo_ae] with θ hθ
        exact abs_mul_le_half_Hk hzpos hθ
      have heq : ∫ θ in Work.Spaces.Iθ, (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
            + Work.Spaces.HkIntegrand α 0 u z θ)
          = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hKG hKU]
      simp only [Real.norm_eq_abs] at hmono
      linarith [hmono, heq]
    · rw [MeasureTheory.integral_undef hInt, norm_zero]
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ :=
        integral_nonneg (fun θ => Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 G z θ)
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ :=
        integral_nonneg (fun θ => Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 u z θ)
      exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  -- `∫_θ bslOp u · u = ∫_θ G · u` for every `z ∈ Icc ε M`
  have hBslG : ∀ z ∈ Set.Icc ε M,
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
        = ∫ θ in Work.Spaces.Iθ, G z θ * u z θ := by
    intro z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hIoo_ae] with θ hθ
    rw [hbeq z (lt_of_lt_of_le hεpos hz.1) θ hθ.1 hθ.2]
  -- the honesty of the target's LHS
  have hLHSint : Integrable
      (fun z => Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      (volume.restrict (Set.Icc ε M)) := by
    have hsubI : Set.Icc ε M ⊆ Work.Spaces.Iz :=
      fun x hx => Set.mem_Ici.mpr (le_trans hεpos.le hx.1)
    have hmono : Integrable (fun z => CΦ / 2 *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
        (volume.restrict (Set.Icc ε M)) :=
      ((hmemG.2.mono_set hsubI).add (hmemU.2.mono_set hsubI)).const_mul (CΦ / 2)
    refine Integrable.mono' hmono ?_ ?_
    · have hjoint : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Φ p.1 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
        have hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) Work.FTS.EllipticEst.Q0 :=
          hΦC2.continuousOn.comp continuousOn_fst
            (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
        exact hΦc.mul ((smoothOpen_bslOp huSO).continuousOn.mul huSO.continuousOn)
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z * (Work.Elliptic.bslOp α u z θ * u z θ)) (volume.restrict Work.Spaces.Iz) :=
        hjoint.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z * (Work.Elliptic.bslOp α u z θ * u z θ))
          (volume.restrict (Set.Icc ε M)) :=
        h1.mono_measure (Measure.restrict_mono hsubI le_rfl)
      exact h2.congr (Filter.Eventually.of_forall (fun z =>
        (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) (Φ z)
          (fun θ => Work.Elliptic.bslOp α u z θ * u z θ))))
    · filter_upwards [hslice', ae_restrict_mem measurableSet_Icc] with z hzsl hzmem
      rw [hBslG z hzmem]
      have hΦb : |Φ z| ≤ CΦ := by
        have h := hCΦ z hzmem
        rwa [Real.norm_eq_abs] at h
      calc ‖Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ)‖
          = |Φ z| * ‖∫ θ in Work.Spaces.Iθ, G z θ * u z θ‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        _ ≤ CΦ * ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)) :=
            mul_le_mul hΦb (hGu_bound z hzmem) (norm_nonneg _) hCΦ0
        _ = CΦ / 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 G z θ)
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by ring
  have hLHSa : (∫ z in Work.Spaces.Iz, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ) :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by rw [hΦsupp z hz hz']; ring)
  have hLHSb : (∫ z in Set.Icc ε M, Φ z
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) := by
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards with z hz
    rw [hBslG z hz]
  have hLHSc : (∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
      = ∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, HH z θ :=
    setIntegral_congr_fun measurableSet_Icc (fun z _ => by
      dsimp only [HH]
      rw [MeasureTheory.integral_const_mul])
  -- ## 6. the assembly
  -- (6a) the marginal integrabilities and the a.e. splitting `HH = Φ·Rad + Φ·Lz`
  have hIntFrMarg : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Fr z θ)
      (volume.restrict (Set.Icc ε M)) := Integrable.integral_prod_left IntFr
  have hIntPhiRad : Integrable (fun z => Φ z * Rad z) (volume.restrict (Set.Icc ε M)) := by
    refine hIntFrMarg.congr ?_
    filter_upwards with z
    dsimp only [Rad]
    exact MeasureTheory.integral_const_mul (Φ z) (fun θ => rad z θ * u z θ)
  have hIntHH : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, HH z θ)
      (volume.restrict (Set.Icc ε M)) := by
    refine hLHSint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hzmem
    dsimp only [HH]
    rw [MeasureTheory.integral_const_mul, hBslG z hzmem]
  have haeSplit : ∀ᵐ z ∂(volume.restrict (Set.Icc ε M)),
      (∫ θ in Work.Spaces.Iθ, HH z θ) = Φ z * Rad z + Φ z * Lz z := by
    filter_upwards [hslice', ae_restrict_mem measurableSet_Icc] with z hzsl hzmem
    obtain ⟨hI1, hI2, -, -, -, -⟩ := hzsl
    have h1 : Integrable (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
        (volume.restrict Work.Spaces.Iθ) := hI1
    have h2 : Integrable (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
        (volume.restrict Work.Spaces.Iθ) := hI2
    have hIrad : Integrable (fun θ => rad z θ * u z θ) (volume.restrict Work.Spaces.Iθ) := by
      refine (h1.sub h2).congr ?_
      filter_upwards with θ
      show Work.Elliptic.bslOp α u z θ * u z θ - Work.Elliptic.Lzero u z θ * u z θ
        = rad z θ * u z θ
      rw [Work.Elliptic.bslOp_apply]
      dsimp only [rad]
      ring
    have hb : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
        = (∫ θ in Work.Spaces.Iθ, rad z θ * u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ) := by
      have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
          = ∫ θ in Work.Spaces.Iθ,
              (rad z θ * u z θ + Work.Elliptic.Lzero u z θ * u z θ) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
        show Work.Elliptic.bslOp α u z θ * u z θ
          = rad z θ * u z θ + Work.Elliptic.Lzero u z θ * u z θ
        rw [Work.Elliptic.bslOp_apply]
        dsimp only [rad]
        ring
      rw [hcongr, MeasureTheory.integral_add hIrad h2]
    calc (∫ θ in Work.Spaces.Iθ, HH z θ)
        = Φ z * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) := by
          dsimp only [HH]
          rw [MeasureTheory.integral_const_mul]
      _ = Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ) := by
          rw [hBslG z hzmem]
      _ = Φ z * (∫ θ in Work.Spaces.Iθ, rad z θ * u z θ)
            + Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ) := by
          rw [hb]; ring
      _ = Φ z * Rad z + Φ z * Lz z := rfl
  have hIntPhiLz : Integrable (fun z => Φ z * Lz z) (volume.restrict (Set.Icc ε M)) := by
    refine (hIntHH.sub hIntPhiRad).congr ?_
    filter_upwards [haeSplit] with z hz
    show (∫ θ in Work.Spaces.Iθ, HH z θ) - Φ z * Rad z = Φ z * Lz z
    rw [hz]; ring
  have hLHSsplit : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, HH z θ)
      = (∫ z in Set.Icc ε M, Φ z * Rad z)
        + (∫ z in Set.Icc ε M, Φ z * Lz z) :=
    (MeasureTheory.integral_congr_ae haeSplit).trans
      (MeasureTheory.integral_add hIntPhiRad hIntPhiLz)
  -- (6b) the `θ`-marginals of the three smooth weighted pieces
  have hX : Integrable (fun θ => ∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntG2
  have hY : Integrable (fun θ => ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntGW2
  have hZ : Integrable (fun θ => ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := Integrable.integral_prod_right IntGW1
  -- (6c) the radial integration by parts, `θ` by `θ`
  have hIBPθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (∫ z in Set.Icc ε M, Fr z θ)
        = α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2) := by
    filter_upwards [hIoo_ae] with θ hθ
    have hφ : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) :=
      (huSO.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    have hIBP := fixedThetaIBP α Φ (fun z : ℝ => u z θ) hεpos hεM hΦC2 hΦsupp hφ
    have hsupp1 : (∫ z in Set.Icc ε M, Fr z θ) = ∫ z in Set.Ioi (0:ℝ), Fr z θ :=
      (setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        dsimp only [Fr]; rw [hΦsupp z hz hz']; ring)).symm
    have hW2eb : (∫ z in Set.Ioi (0:ℝ),
          deriv (deriv (fun z : ℝ => z ^ 2 * Φ z)) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      rfl
    have hW1eb : (∫ z in Set.Ioi (0:ℝ), deriv (fun z : ℝ => z * Φ z) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      rfl
    have hneg : (∫ z in Set.Ioi (0:ℝ), Fr z θ)
        = α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
              Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2) := by
      have hfun : (fun z : ℝ => Fr z θ) = fun z : ℝ =>
          - (Φ z * (α ^ 2 * z ^ 2 * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) := by
        funext z
        have hpz2 : Work.Spaces.pzIter 2 u z θ = deriv (deriv (fun z' : ℝ => u z' θ)) z := rfl
        have hpz1 : Work.Spaces.pz u z θ = deriv (fun z' : ℝ => u z' θ) z := rfl
        dsimp only [Fr, rad]
        rw [hpz2, hpz1]
        ring
      have hstep : -(∫ z in Set.Ioi (0:ℝ), Φ z * (α ^ 2 * z ^ 2
            * deriv (deriv (fun z' : ℝ => u z' θ)) z
            + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ)
          = -(-α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
                Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
              + (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ),
                  deriv (deriv (fun z : ℝ => z ^ 2 * Φ z)) z * (u z θ) ^ 2)
              - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0:ℝ),
                  deriv (fun z : ℝ => z * Φ z) z * (u z θ) ^ 2)) :=
        congrArg Neg.neg hIBP
      calc (∫ z in Set.Ioi (0:ℝ), Fr z θ)
          = ∫ z in Set.Ioi (0:ℝ), - (Φ z * (α ^ 2 * z ^ 2
              * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) := by
            rw [hfun]
        _ = -(∫ z in Set.Ioi (0:ℝ), Φ z * (α ^ 2 * z ^ 2
              * deriv (deriv (fun z' : ℝ => u z' θ)) z
              + (α * (5 + α) * z) * deriv (fun z' : ℝ => u z' θ) z) * u z θ) :=
            MeasureTheory.integral_neg _
        _ = α ^ 2 * (∫ z in Set.Ioi (0:ℝ),
                Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
              - (α ^ 2 / 2) * (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
              + ((α * (5 + α)) / 2) * (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2) := by
            rw [hstep, hW2eb, hW1eb]
            ring
    have hIoi1 : (∫ z in Set.Ioi (0:ℝ), Φ z * (z * deriv (fun z' : ℝ => u z' θ) z) ^ 2)
        = ∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hΦsupp z hz hz']; ring)
    have hIoi2 : (∫ z in Set.Ioi (0:ℝ), W2e z * (u z θ) ^ 2)
        = ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hW2e0 z hz hz']; ring)
    have hIoi3 : (∫ z in Set.Ioi (0:ℝ), W1e z * (u z θ) ^ 2)
        = ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2 :=
      setIntegral_Ioi_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
        rw [hW1e0 z hz hz']; ring)
    first
      | (rw [hsupp1, hneg, hIoi1, hIoi2, hIoi3]; ring)
      | rw [hsupp1, hneg, hIoi1, hIoi2, hIoi3]
  have hIBPlin : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, Fr z θ)
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W2e z * (u z θ) ^ 2)
        + ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W1e z * (u z θ) ^ 2) := by
    have h1 : Integrable (fun θ => α ^ 2 * (∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) :=
      hX.const_mul _
    have h2 : Integrable (fun θ => (α ^ 2 / 2) * (∫ z in Set.Icc ε M,
        W2e z * (u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) := hY.const_mul _
    have h3 : Integrable (fun θ => ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M,
        W1e z * (u z θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) := hZ.const_mul _
    have h12 : Integrable (fun θ => α ^ 2 * (∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2))
        (volume.restrict Work.Spaces.Iθ) := by
      refine (h1.sub h2).congr ?_
      filter_upwards with θ
      rfl
    refine (MeasureTheory.integral_congr_ae hIBPθ).trans ?_
    show (∫ θ in Work.Spaces.Iθ,
        (α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
          - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
          + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)))
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W2e z * (u z θ) ^ 2)
        + ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            W1e z * (u z θ) ^ 2)
    first
      | (rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_sub h1 h2,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
         ring)
      | rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_sub h1 h2,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
  have hA : (∫ z in Set.Icc ε M, Φ z * Rad z)
      = ∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, Fr z θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only [Rad]
    exact (MeasureTheory.integral_const_mul (Φ z) (fun θ => rad z θ * u z θ)).symm
  have hAswap : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, Fr z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, Fr z θ :=
    MeasureTheory.integral_integral_swap IntFr
  have hD1 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
        Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ,
          Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M,
            Φ z * (z * Work.Spaces.pz u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntG2
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, Φ z * (z * Work.Spaces.pz u z θ) ^ 2)
        = Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (Φ z) (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
  have hD2 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, W2e z * (u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W2e z * (u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntGW2
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, W2e z * (u z θ) ^ 2)
        = W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (W2e z) (fun θ => (u z θ) ^ 2)
  have hD3 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2)
      = ∫ z in Set.Icc ε M, W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    have hsw : (∫ z in Set.Icc ε M, ∫ θ in Work.Spaces.Iθ, W1e z * (u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Icc ε M, W1e z * (u z θ) ^ 2 :=
      MeasureTheory.integral_integral_swap IntGW1
    rw [← hsw]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, W1e z * (u z θ) ^ 2)
        = W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
    exact MeasureTheory.integral_const_mul (W1e z) (fun θ => (u z θ) ^ 2)
  have hIBPfinal : (∫ z in Set.Icc ε M, Φ z * Rad z)
      = α ^ 2 * (∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz u z θ) ^ 2))
        - (α ^ 2 / 2) * (∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Set.Icc ε M, W1e z
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
    first
      | (rw [hA, hAswap, hIBPlin, hD1, hD2, hD3]; ring)
      | rw [hA, hAswap, hIBPlin, hD1, hD2, hD3]
  -- (6d) the support reductions on the `Iz`-side, `W2e = W2`, `W1e = W1`, and the final algebra
  have hW2e_eq : W2e = W2 := by
    have hfun : (fun z : ℝ => z ^ 2 * Φ z)
        = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z ^ 2 := by
      funext z
      dsimp only [Φ]
      ring
    dsimp only [W2e, W2]
    rw [hfun]
  have hW1e_eq : W1e = W1 := by
    have hfun : (fun z : ℝ => z * Φ z) = fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2 * z := by
      funext z
      dsimp only [Φ]
      ring
    dsimp only [W1e, W1]
    rw [hfun]
  have hR1 : (∫ z in Work.Spaces.Iz,
        Φ z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, Φ z * (∫ θ in Work.Spaces.Iθ,
          (z * Work.Spaces.pz u z θ) ^ 2) :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hΦsupp z hz hz']; ring)
  have hR2 : (∫ z in Work.Spaces.Iz,
        Φ z * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
      = ∫ z in Set.Icc ε M, Φ z * Lz z :=
    setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hΦsupp z hz hz']; ring)
  have hR3 : (∫ z in Work.Spaces.Iz, W2 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, W2e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    rw [← hW2e_eq]
    exact setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hW2e0 z hz hz']; ring)
  have hR4 : (∫ z in Work.Spaces.Iz, W1 z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = ∫ z in Set.Icc ε M, W1e z * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    rw [← hW1e_eq]
    exact setIntegral_Iz_eq_Icc hεpos (le_of_lt hεM) (fun z hz hz' => by
      rw [hW1e0 z hz hz']; ring)
  rw [hLHSa, hLHSb, hLHSc, hR1, hR2, hR3, hR4, hLHSsplit, hIBPfinal]
  ring

end Work.FTS.EllipticEst.H2W.AeW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **`ℋ^k` is closed under addition for data smooth on the open quadrant.**

If `f` and `g` are `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (`SmoothOpen`) and both lie in
the weighted space `ℋ^k` (`Work.Spaces.HkMem`), then so does `f + g`.

Proof.  `f + g` is again `C^∞` on the open quadrant (`smoothOpen_add`), so its `ℋ^k`-integrand is
continuous there (`SmoothOpen.continuousOn_HkIntegrand`) — which is the only regularity needed
for the two iterated integrals.  The weighted derivatives are additive on the open quadrant
(`SmoothOpen.DzIter_add`, `SmoothOpen.mixed_add`), so termwise `(a+b)² ≤ 2a² + 2b²` gives the
pointwise domination

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`

on `Iz ×ˢ Iθ` (`HkIntegrand_add_le_open`; the two boundary lines are trivial).  Since the
integrand is a sum of squares, it is nonnegative, so the domination of the values is a
domination of the absolutely-integrable majorant, and `HkMem α k f`, `HkMem α k g` supply the
integrability of its two pieces.  This is exactly the shape of
`Work.FTS.LocData.HkMem_of_majorant`, which assembles the two `HkMem` clauses (on each angular
slice and after integration in `z`) from the continuity and the pointwise domination. -/
theorem HkMem_add_smoothOpen (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hsum : SmoothOpen (fun z θ => f z θ + g z θ) := smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hsum.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable: those of `f` and of `g` are
    intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · -- the `z`-integral of the `θ`-slices: split it into the two known integrals
    have hknown : MeasureTheory.IntegrableOn
        (fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
        Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine hknown.congr_fun ?_ measurableSet_Ici
    intro z hz
    simp only []
    rw [integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      integral_const_mul, integral_const_mul]
  · -- the pointwise domination on the closed quadrant
    intro z hz θ hθ
    exact HkIntegrand_add_le_open α k hf hg hz hθ

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HonMemU

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Helper lemmas -/

/-- The level-`0` `HkIntegrand` vanishes at the left angular boundary. -/
private lemma hki_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  simp [Work.Spaces.eta]

/-- The level-`0` `HkIntegrand` vanishes at the right angular boundary. -/
private lemma hki_pi (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  rw [hs]
  simp [Work.Spaces.eta]

/-- The five-term Cauchy–Schwarz inequality, with the common factor `c` factored out. -/
private lemma sq_sum_five (a1 a2 a3 a4 a5 c : ℝ) :
    ((a1 + a2 + a3 + a4 + a5) * c) ^ 2
      ≤ 5 * ((a1 * c) ^ 2 + (a2 * c) ^ 2 + (a3 * c) ^ 2 + (a4 * c) ^ 2 + (a5 * c) ^ 2) := by
  have h1 : (a1 + a2 + a3 + a4 + a5) ^ 2 ≤ 5 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 + a5 ^ 2) := by
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a1 - a4),
      sq_nonneg (a1 - a5), sq_nonneg (a2 - a3), sq_nonneg (a2 - a4), sq_nonneg (a2 - a5),
      sq_nonneg (a3 - a4), sq_nonneg (a3 - a5), sq_nonneg (a4 - a5)]
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg c)
  nlinarith [h2]

/-- Integrability on `Iz` of the `θ`-integral of a pointwise sum of two functions, given the
integrability of the angular slices and of the two `θ`-integrals. -/
private theorem integrableOn_integral_add {f g : ℝ → ℝ → ℝ}
    (hf : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hg : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hF : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) Work.Spaces.Iz)
    (hG : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ) Work.Spaces.Iz) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ + g z θ) Work.Spaces.Iz := by
  refine (hF.add hG).congr ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  exact (MeasureTheory.integral_add (hf z hz) (hg z hz)).symm

/-- The pointwise majorant of the level-`0` `HkIntegrand` of `∂_θ(tan θ · Ψ)` used below: it
is the sum of the five summands appearing in the rearranged equation, each dominating term
weighted by the Cauchy–Schwarz constant `5`. -/
private def Mj (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 F z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)

/-- **The pointwise domination.**  If `u = g₁ + ⋯ + g₅` on the open quadrant then the
level-`0` `HkIntegrand` of `u` is dominated on the closed quadrant by `5` times the sum of the
`HkIntegrand`s of the `gᵢ`.

On the open quadrant this is the five-term Cauchy–Schwarz inequality
(`sq_sum_five`); on the boundary it is trivial because the angular weight vanishies there
(`HkIntegrand_zero_z`, `hki_zero`, `hki_pi`). -/
private theorem hki_le_five {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      u z θ = g1 z θ + g2 z θ + g3 z θ + g4 z θ + g5 z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ
      + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
      + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
    intro z θ
    have e1 := Work.Spaces.HkIntegrand_nonneg α 0 g1 z θ
    have e2 := Work.Spaces.HkIntegrand_nonneg α 0 g2 z θ
    have e3 := Work.Spaces.HkIntegrand_nonneg α 0 g3 z θ
    have e4 := Work.Spaces.HkIntegrand_nonneg α 0 g4 z θ
    have e5 := Work.Spaces.HkIntegrand_nonneg α 0 g5 z θ
    linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, Work.Spaces.HkIntegrand_zero_z]
    exact hnn 0 θ
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · rw [← hθ0, hki_zero]
      exact hnn z 0
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · rw [hθ2, hki_pi]
        exact hnn z (Real.pi / 2)
      · simp only [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, h z hzpos θ hθpos hθlt]
        exact sq_sum_five _ _ _ _ _ _

/-! ## The main lemma -/


end Work.FTS.EllipticEst.Honest.HonMemU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonZBoxPsiBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonZSecondSwapSigma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter


end

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.PthCore.HalfSharpHardyCosTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.PthCore

open scoped Real Topology
open MeasureTheory Set Filter

/-! # Sharp Hardy on `(0, π/4)` with a `cos²(2θ)`-weight and absolute constants

`Work.Elliptic.half_sharp_hardy` proves

`∫_0^{π/4} f² sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_0^{π/4} (f')² sin(2θ)^{-η} + C ∫_0^{π/4} f² sin(2θ)^{-η}`

with an *existential* constant `C`; inspecting its proof one sees that `C = 2` always works
(the comparison `Work.Elliptic.sin_pow_compare` is proved with the very constant `2`).  This
file records that explicit form (`half_sharp_hardy_two`) and then adds the `cos²(2θ) ≤ 1`
step of `Work.FTS.EllipticEst.Honest.HalfSharpHardyCos` to obtain `HalfSharpHardyCosTwo`
with both constants absolute: `(1+η)^{-2}` and `2`. -/




end Work.FTS.EllipticEst.Honest.PthCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.honLintegralSliceBridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Helpers: the level-`0` slice and its `∫⁻`-form -/







end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TopSlotTwoFts.AHalfInfra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The open quadrant. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Qd {z θ : ℝ} : (z, θ) ∈ Qd ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- The `A`-function of the top slot: `A Ψ = z² ∂_z² Ψ`. -/
def Aft (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-! ## Smoothness on the open quadrant -/

theorem smoothOpen_Dz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz f) := hf.pz
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p) Qd :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder) (s := Qd)).mul h1
  refine h2.congr (fun p _ => ?_)
  rfl

theorem smoothOpen_DzIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j f) := by
  induction j with
  | zero => simpa using hf
  | succ k ih =>
      rw [Work.Spaces.DzIter_succ]
      exact smoothOpen_Dz ih

theorem smoothOpen_Aft {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Aft Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter 2 Ψ) := hΨ.pzIter 2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2 * Function.uncurry (Work.Spaces.pzIter 2 Ψ) p) Qd :=
    ((contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder) (s := Qd)).pow 2).mul h1
  refine h2.congr (fun p _ => ?_)
  rfl

theorem smoothOpen_slices {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z : ℝ} (hz : 0 < z) : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => f z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  exact contDiffOn_iff_forall_nat_le.mp (hf.curry_θ hz) n le_top

/-! ## Continuity of the two integrands on the open quadrant -/

theorem continuousOn_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2)
      Qd :=
  ((smoothOpen_DzIter hΨ j).pth.pth).continuousOn

theorem continuousOn_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) Qd :=
  ((smoothOpen_Aft hΨ).pth.pth).continuousOn

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hnum : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Qd :=
    (continuous_const.continuousOn.add continuous_fst.continuousOn).pow 2
  have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Qd := continuous_fst.continuousOn.pow 2
  have hne : ∀ p ∈ Qd, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
  exact hnum.div hden hne

theorem continuousOn_sEta_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
    Qd := by
  obtain ⟨-, -, -, -, hwcont⟩ := Work.FTS.EllipticEst.H2W.SliceEtaFacts
  have hc : ContinuousOn Work.FTS.EllipticEst.sEta (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hwcont θ hθ).continuousWithinAt
  exact hc.comp continuous_snd.continuousOn (fun p hp => hp.2)

/-- The first integrand: `(∂_θ²(D_z^jΨ))² sEta w²`. -/
theorem continuousOn_F1 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.w p.1) ^ 2) Qd := by
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      ((fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2) p)
        * ((fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) p
            * (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) p)) Qd :=
    ((continuousOn_pthIter2_DzIter hΨ j).pow 2).mul
      (continuousOn_sEta_Qd.mul (continuousOn_w_Qd.pow 2))
  exact h.congr (fun p _ => by ring)

/-- The second integrand: `(∂_θ²(AΨ))² sEta w²`. -/
theorem continuousOn_F2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.w p.1) ^ 2) Qd := by
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      ((fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) ^ 2) p)
        * ((fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) p
            * (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) p)) Qd :=
    ((continuousOn_pthIter2_Aft hΨ).pow 2).mul
      (continuousOn_sEta_Qd.mul (continuousOn_w_Qd.pow 2))
  exact h.congr (fun p _ => by ring)

/-! ## A.e. strong measurability -/

theorem aesm_slice_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_F1 hΨ j) hz

theorem aesm_slice_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_F2 hΨ) hz

theorem aesm_int_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_F1 hΨ j)).integral_prod_right'

theorem aesm_int_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_F2 hΨ)).integral_prod_right'

/-! ## Pointwise domination by the honest level-`2` integrand of `∂_θθΨ` -/


end

end Work.FTS.EllipticEst.TopSlotTwoFts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.DzIter_one_Psi_estimate_sound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The reusable core estimate and its `θ`-measure-theoretic helpers

These are placed in the sub-namespace `DzIterOneSound` so that importing this module together
with `remov.DzIter_one_Psi_estimate` (which carries the same helper names) cannot produce a name
clash. -/

namespace DzIterOneSound

/-! ## Small general helpers -/

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
lemma sinCos2_nonneg_Iθ_est {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

/-- An `Iθ`-integral of `|f|·sinθcos²θ` is nonnegative. -/
lemma integral_abs_mul_sinCos2_nonneg_est (f : ℝ → ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ_est hθ)

/-- **Slice integrability of an interval integral.** -/
lemma integrable_Iθ_intervalIntegral_of_integrable_prod_est {h : ℝ → ℝ → ℝ} {a z₁ : ℝ}
    (hab : a ≤ z₁)
    (hint : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc a z₁) :
    MeasureTheory.Integrable (fun θ : ℝ => ∫ s in a..ρ, h s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hρa : a ≤ ρ := hρ.1
  have hρz : ρ ≤ z₁ := hρ.2
  have hdom : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ s in Set.uIoc a z₁, ‖h s θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := hint.integral_norm_prod_right
    simpa only [Function.uncurry_apply_pair] using h
  have hslice : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun s : ℝ => h s θ) (Set.uIoc a z₁) := by
    have h := hint.prod_left_ae
    filter_upwards [h] with θ hθ
    simpa only [Function.uncurry_apply_pair, MeasureTheory.IntegrableOn] using hθ
  have hsub : Set.uIoc a ρ ⊆ Set.uIoc a z₁ := by
    rw [Set.uIoc_of_le hρa, Set.uIoc_of_le hab]
    exact Set.Ioc_subset_Ioc le_rfl hρz
  have hsmall : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a ρ)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint.mono_measure
      (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ s in a..ρ, h s θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hsw : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ × ℝ => h z.2 z.1)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.uIoc a ρ))) :=
      hsmall.aestronglyMeasurable.prod_swap
    have h2 := hsw.integral_prod_right'
    refine h2.congr ?_
    filter_upwards with θ
    rw [intervalIntegral.integral_of_le hρa, ← Set.uIoc_of_le hρa]
  refine hdom.mono' hmeas ?_
  filter_upwards [hslice] with θ hθ
  rw [Real.norm_eq_abs, intervalIntegral.integral_of_le hρa]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc a ρ)) (fun s => h s θ)) ?_
  exact MeasureTheory.setIntegral_mono_set hθ.norm
    (Filter.Eventually.of_forall fun s => norm_nonneg _)
    (Filter.Eventually.of_forall fun s hs =>
      hsub (by simpa only [Set.uIoc_of_le hρa] using hs))

/-- **The `θ`–`s` swap for the interval integral.** -/
lemma intervalIntegral_swap_right_est {h : ℝ → ℝ → ℝ} {a z₁ ρ : ℝ}
    (hint : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hρ : ρ ∈ Set.Icc a z₁) :
    (∫ θ in Work.Spaces.Iθ, ∫ s in a..ρ, h s θ)
      = ∫ s in a..ρ, ∫ θ in Work.Spaces.Iθ, h s θ := by
  have hρa : a ≤ ρ := hρ.1
  have hsub : Set.uIoc a ρ ⊆ Set.uIoc a z₁ := by
    rw [Set.uIoc_of_le hρa, Set.uIoc_of_le (le_trans hρa hρ.2)]
    exact Set.Ioc_subset_Ioc le_rfl hρ.2
  have h' : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a ρ)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint.mono_measure
      (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl)
  exact (MeasureTheory.intervalIntegral_integral_swap h').symm

/-- **Interval integrability of the primitive.** -/
lemma intervalIntegrable_primitive_of_integrableOn_est {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MeasureTheory.IntegrableOn f (Set.Icc a b)) :
    IntervalIntegrable (fun ρ : ℝ => ∫ s in a..ρ, f s) MeasureTheory.volume a b := by
  have hcont : ContinuousOn (fun ρ : ℝ => ∫ s in a..ρ, f s) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le hab])
  exact hcont.intervalIntegrable

/-- **Cauchy–Schwarz for an interval integral**: `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
lemma sq_intervalIntegral_le_est {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfae : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hf : MeasureTheory.IntegrableOn (fun x => f x ^ 2) (Set.uIoc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * (∫ x in a..b, (f x) ^ 2) := by
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top⟩
  have hmem1 : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := MeasureTheory.memLp_const 1
  have hmem2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hfae]
    exact hf
  have hcs := Work.Spaces.cs_integral hmem1 hmem2
  simp only [one_mul, one_pow] at hcs
  have hconv : (∫ x in a..b, f x) = ∫ x in Set.uIoc a b, f x := by
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  have hconv2 : (∫ x in a..b, (f x) ^ 2) = ∫ x in Set.uIoc a b, (f x) ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  rw [hconv, hconv2]
  have hconst : (∫ x in Set.uIoc a b, (1 : ℝ)) = b - a := by
    rw [Set.uIoc_of_le hab, MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hconst] at hcs
  exact hcs

/-! ## The core estimate -/

/-- **The core estimate.** -/
theorem coreBound {Ψ : ℝ → ℝ → ℝ} {z₀ hh : ℝ}
    (hz₀ : 0 < z₀) (hhpos : 0 < hh) (hhlt : hh < z₀)
    (hB : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hQJ : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz)
    (hCs : ∀ z ∈ Set.Icc z₀ (z₀ + hh), ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
    (hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ (z₀ + hh)))
    (hrectAbs : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hFtc : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
        IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
          MeasureTheory.volume z₀ ρ ∧
        (∫ s in z₀..ρ, Work.Spaces.pzIter 2 Ψ s θ)
          = Work.Spaces.pz Ψ ρ θ - Work.Spaces.pz Ψ z₀ θ)
    (hrect : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hswap : (∫ z in z₀..(z₀ + hh), (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, ∫ z in z₀..(z₀ + hh),
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
    (hzero : (∫ θ in Work.Spaces.Iθ, ∫ z in z₀..(z₀ + hh),
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ|
      ≤ ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh := by
  have hzle : z₀ ≤ z₀ + hh := by linarith
  set Q : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hQdef
  set Fint : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ with hFdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
    with hBdef
  have hQJ' : MeasureTheory.IntegrableOn Q Work.Spaces.Iz := by
    simpa only [hQdef] using hQJ
  have hFint' : MeasureTheory.IntegrableOn Fint (Set.Icc z₀ (z₀ + hh)) := by
    simpa only [hFdef] using hFint
  have hCs' : ∀ z ∈ Set.Icc z₀ (z₀ + hh), Fint z
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q z) := by
    intro z hz
    simpa only [hFdef, hQdef] using hCs z hz
  have hQnn : ∀ z : ℝ, 0 ≤ Q z := fun z => by
    rw [hQdef]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hFnn : ∀ s : ℝ, 0 ≤ Fint s := by
    intro s; rw [hFdef]; exact integral_abs_mul_sinCos2_nonneg_est _
  -- ### Step 1: the a.e. pointwise bound
  have hpt : ∀ᵐ ρ ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
      |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ s in z₀..ρ, Fint s := by
    filter_upwards [hrect.prod_right_ae,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with ρ hρint hρmem
    have hρIcc : ρ ∈ Set.Icc z₀ (z₀ + hh) := ⟨le_of_lt hρmem.1, hρmem.2⟩
    have hle : z₀ ≤ ρ := le_of_lt hρmem.1
    have hρint' : MeasureTheory.Integrable
        (fun θ : ℝ => Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simpa only [Function.uncurry_apply_pair] using hρint
    have hA : B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
            * Work.Elliptic.sinCos2 θ := by
      rw [hBdef, ← MeasureTheory.integral_sub hB hρint']
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hA]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
        * Work.Elliptic.sinCos2 θ)) ?_
    simp only [Real.norm_eq_abs]
    have hptθ : (fun θ : ℝ => |(Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
          * Work.Elliptic.sinCos2 θ|)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|)
          * Work.Elliptic.sinCos2 θ) := by
      filter_upwards [hFtc, MeasureTheory.ae_restrict_mem measurableSet_Icc]
        with θ hθftc hθmem
      obtain ⟨-, heq⟩ := hθftc ρ hρIcc
      have hσ := sinCos2_nonneg_Iθ_est hθmem
      have h1 : Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ
          = -(∫ s in z₀..ρ, Work.Spaces.pzIter 2 Ψ s θ) := by linarith
      rw [h1, abs_mul, abs_neg, abs_of_nonneg hσ]
      exact mul_le_mul_of_nonneg_right
        (intervalIntegral.abs_integral_le_integral_abs hle) hσ
    have hRint : MeasureTheory.Integrable
        (fun θ : ℝ => (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|)
          * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h0 := integrable_Iθ_intervalIntegral_of_integrable_prod_est hzle hrectAbs hρIcc
      refine h0.congr ?_
      filter_upwards with θ
      rw [intervalIntegral.integral_mul_const]
    have hLint : MeasureTheory.Integrable
        (fun θ : ℝ => |(Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
          * Work.Elliptic.sinCos2 θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine hRint.mono' ?_ ?_
      · have h1 : MeasureTheory.AEStronglyMeasurable
            (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
              - Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          hB.aestronglyMeasurable.sub hρint'.aestronglyMeasurable
        have h2 : MeasureTheory.AEStronglyMeasurable
            (fun θ : ℝ => (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
              * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          h1.congr (Filter.Eventually.of_forall fun θ => by ring)
        simpa only [Real.norm_eq_abs] using h2.norm
      · filter_upwards [hptθ] with θ hθ
        simpa only [Real.norm_eq_abs, abs_abs] using hθ
    have hmono := MeasureTheory.integral_mono_ae hLint hRint hptθ
    have hswapR : (∫ θ in Work.Spaces.Iθ,
          (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|) * Work.Elliptic.sinCos2 θ)
        = ∫ s in z₀..ρ, Fint s := by
      have h0 := intervalIntegral_swap_right_est (h := fun s θ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) hrectAbs hρIcc
      rw [← h0]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with θ
      rw [intervalIntegral.integral_mul_const]
    rw [hswapR] at hmono
    exact hmono
  -- ### Step 2: the average identity
  have hBint : IntervalIntegrable
      (fun ρ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ) MeasureTheory.volume z₀ (z₀ + hh) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzle]
    have habs : MeasureTheory.Integrable
        (Function.uncurry (fun z θ : ℝ => |Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine hrect.abs.congr ?_
      rw [MeasureTheory.Measure.prod_restrict]
      refine MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ioc.prod measurableSet_Icc) ?_
      rintro ⟨z, θ⟩ ⟨-, hθ⟩
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]
    have hdom := habs.integral_norm_prod_left
    have hdom' : MeasureTheory.Integrable
        (fun ρ : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pz Ψ ρ θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))) := by
      refine hdom.congr ?_
      filter_upwards with ρ
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      simp only [Real.norm_eq_abs, Function.uncurry_apply_pair]
      rw [abs_mul, abs_of_nonneg (abs_nonneg _), abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]
    refine hdom'.mono' ?_ ?_
    · exact (hrect.aestronglyMeasurable.integral_prod_right')
    · filter_upwards with ρ
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) ?_
      simp only [Real.norm_eq_abs]
      exact le_of_eq (MeasureTheory.integral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        simp only [abs_mul, abs_of_nonneg (abs_nonneg _),
          abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]))
  have havg : hh * B = ∫ ρ in z₀..(z₀ + hh),
      (B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) := by
    have hzero' : (∫ ρ in z₀..(z₀ + hh),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) = 0 := by
      rw [hswap, hzero]
    have hconst : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume z₀ (z₀ + hh) :=
      intervalIntegrable_const
    have h1 : (∫ ρ in z₀..(z₀ + hh),
          (B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)))
        = (∫ ρ in z₀..(z₀ + hh), B)
          - (∫ ρ in z₀..(z₀ + hh),
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) :=
      intervalIntegral.integral_sub hconst hBint
    rw [h1, hzero', sub_zero, intervalIntegral.integral_const]
    ring
  -- the pointwise bound on `(Fint s)²`
  have hFint2bd : ∀ s ∈ Set.Icc z₀ (z₀ + hh),
      (Fint s) ^ 2 ≤ (Real.pi / 2) / z₀ ^ 4 * Q s := by
    intro s hs
    have hs1 : 0 < s := lt_of_lt_of_le hz₀ hs.1
    have hs4 : 0 < s ^ 4 := by positivity
    have hz4 : 0 < z₀ ^ 4 := by positivity
    have hle : 1 / s ^ 4 ≤ 1 / z₀ ^ 4 :=
      one_div_le_one_div_of_le hz4 (pow_le_pow_left₀ (le_of_lt hz₀) hs.1 4)
    have hb := hCs' s hs
    have hsqrt : 0 ≤ Real.sqrt (Q s) := Real.sqrt_nonneg _
    have h1 : (Fint s) ^ 2 ≤ ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2 :=
      pow_le_pow_left₀ (hFnn s) hb 2
    have h2 : ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2
        = (1 / s ^ 4) * (Real.pi / 2) * Q s := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hQnn s),
        div_pow, one_pow]
      ring
    have h3 : (1 / s ^ 4) * (Real.pi / 2) * Q s ≤ (1 / z₀ ^ 4) * (Real.pi / 2) * Q s := by
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ Real.pi / 2)
      exact mul_le_mul_of_nonneg_right this (hQnn s)
    calc (Fint s) ^ 2 ≤ ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2 := h1
      _ = (1 / s ^ 4) * (Real.pi / 2) * Q s := h2
      _ ≤ (1 / z₀ ^ 4) * (Real.pi / 2) * Q s := h3
      _ = (Real.pi / 2) / z₀ ^ 4 * Q s := by ring
  -- ### Step 3: Cauchy–Schwarz in `s`
  have hCS : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      (∫ s in z₀..ρ, Fint s) ^ 2 ≤ (ρ - z₀) * (∫ s in z₀..ρ, (Fint s) ^ 2) := by
    intro ρ hρ
    have hle : z₀ ≤ ρ := hρ.1
    have hsub : Set.uIoc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      exact ⟨le_of_lt hx.1, le_trans hx.2 hρ.2⟩
    have hae : MeasureTheory.AEStronglyMeasurable Fint
        (MeasureTheory.volume.restrict (Set.uIoc z₀ ρ)) :=
      hFint'.aestronglyMeasurable.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
    have hf2 : MeasureTheory.IntegrableOn (fun x => (Fint x) ^ 2) (Set.uIoc z₀ ρ) := by
      have hQsub : MeasureTheory.IntegrableOn Q (Set.uIoc z₀ ρ) :=
        hQJ'.mono_set (fun x hx => by
          rw [Set.uIoc_of_le hle] at hx
          exact le_trans (le_of_lt hz₀) (le_of_lt hx.1))
      have hdom : MeasureTheory.IntegrableOn (fun x => (Real.pi / 2) / z₀ ^ 4 * Q x) (Set.uIoc z₀ ρ) :=
        hQsub.const_mul _
      refine hdom.mono' ?_ ?_
      · exact hae.pow 2
      · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_uIoc)] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFint2bd x (hsub hx)
    exact sq_intervalIntegral_le_est hle hae hf2
  -- ### Step 4: the `L²` bound over the interval
  have hF2 : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      (∫ s in z₀..ρ, (Fint s) ^ 2)
        ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by
    intro ρ hρ
    have hle : z₀ ≤ ρ := hρ.1
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have hsub : Set.uIoc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      exact ⟨le_of_lt hx.1, le_trans hx.2 hρ.2⟩
    have hsub2 : Set.Icc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := fun x hx => ⟨hx.1, le_trans hx.2 hρ.2⟩
    have hf2 : IntervalIntegrable (fun x => (Fint x) ^ 2) MeasureTheory.volume z₀ ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      have hQsub : MeasureTheory.IntegrableOn Q (Set.Ioc z₀ ρ) :=
        hQJ'.mono_set (fun x hx => le_trans (le_of_lt hz₀) (le_of_lt hx.1))
      refine (hQsub.const_mul ((Real.pi / 2) / z₀ ^ 4)).mono' ?_ ?_
      · have hae' : MeasureTheory.AEStronglyMeasurable Fint
            (MeasureTheory.volume.restrict (Set.Ioc z₀ ρ)) :=
          hFint'.aestronglyMeasurable.mono_measure
            (MeasureTheory.Measure.restrict_mono (Set.Ioc_subset_uIoc.trans hsub) le_rfl)
        exact hae'.pow 2
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFint2bd x (hsub (Set.Ioc_subset_uIoc hx))
    have hQint : IntervalIntegrable Q MeasureTheory.volume z₀ ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact hQJ'.mono_set (fun x hx => le_trans (le_of_lt hz₀) (le_of_lt hx.1))
    have h1 : (∫ s in z₀..ρ, (Fint s) ^ 2) ≤ ∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s := by
      refine intervalIntegral.integral_mono_on hle hf2 (hQint.const_mul _) ?_
      intro s hs
      exact hFint2bd s (hsub2 hs)
    have h2 : (∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s)
        = (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s) :=
      intervalIntegral.integral_const_mul _ _
    have h3 : (∫ s in z₀..ρ, Q s) ≤ ∫ z in Work.Spaces.Iz, Q z := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hQJ' (Filter.Eventually.of_forall hQnn) ?_
      filter_upwards with x hx
      exact le_trans (le_of_lt hz₀) (le_of_lt hx.1)
    have h4 : (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s)
        ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc (∫ s in z₀..ρ, (Fint s) ^ 2)
        ≤ ∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s := h1
      _ = (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s) := h2
      _ ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := h4
  -- ### Step 5: the `√hh` bound
  have hstep5 : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      ∫ s in z₀..ρ, Fint s
        ≤ Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    intro ρ hρ
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have h4 : 0 ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by positivity
    have h1 : (∫ s in z₀..ρ, Fint s) ^ 2
        ≤ hh * ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
      have hc := hCS ρ hρ
      have h2 := hF2 ρ hρ
      have h3 : ρ - z₀ ≤ hh := by linarith [hρ.2]
      have h5 : 0 ≤ ρ - z₀ := sub_nonneg.mpr hρ.1
      have h6 : 0 ≤ ∫ s in z₀..ρ, (Fint s) ^ 2 :=
        intervalIntegral.integral_nonneg hρ.1 (fun s _ => sq_nonneg _)
      have h7 := mul_le_mul h3 h2 h6 (le_of_lt hhpos)
      linarith [hc, h7, h4]
    have h5 : 0 ≤ ∫ s in z₀..ρ, Fint s :=
      intervalIntegral.integral_nonneg hρ.1 (fun s _ => hFnn s)
    calc ∫ s in z₀..ρ, Fint s = Real.sqrt ((∫ s in z₀..ρ, Fint s) ^ 2) :=
          (Real.sqrt_sq h5).symm
      _ ≤ Real.sqrt (hh * ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) :=
          Real.sqrt_mul (le_of_lt hhpos) _
  -- ### Step 6
  have hmain : |hh * B| ≤ hh * Real.sqrt hh
      * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    have h1 : |hh * B| ≤ ∫ ρ in z₀..(z₀ + hh),
        |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)| := by
      rw [havg]
      exact intervalIntegral.abs_integral_le_integral_abs hzle
    have h2 : (∫ ρ in z₀..(z₀ + hh),
          |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)|)
        ≤ ∫ ρ in z₀..(z₀ + hh), (∫ s in z₀..ρ, Fint s) := by
      rw [intervalIntegral.integral_of_le hzle, intervalIntegral.integral_of_le hzle]
      refine MeasureTheory.integral_mono_ae ?_ ?_ hpt
      · have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioc z₀ (z₀ + hh)) :=
          MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        have h' : MeasureTheory.IntegrableOn
            (fun ρ : ℝ => B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ))
            (Set.Ioc z₀ (z₀ + hh)) := hc.sub hBint.1
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using h'.abs
      · exact (intervalIntegrable_primitive_of_integrableOn_est hzle hFint').1
    have h3 : (∫ ρ in z₀..(z₀ + hh), (∫ s in z₀..ρ, Fint s))
        ≤ ∫ ρ in z₀..(z₀ + hh),
            (Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by
      refine intervalIntegral.integral_mono_on hzle
        (intervalIntegrable_primitive_of_integrableOn_est hzle hFint') intervalIntegrable_const ?_
      intro ρ hρ
      exact hstep5 ρ hρ
    have h4 : (∫ ρ in z₀..(z₀ + hh),
          (Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))))
        = hh * Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
      rw [intervalIntegral.integral_const]
      ring
    linarith [h1, h2, h3, le_of_eq h4]
  -- ### Step 7: divide by `hh` and apply AM–GM
  have hBbound : |B| ≤ Real.sqrt hh
      * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    have h := hmain
    rw [abs_mul, abs_of_pos hhpos] at h
    have h' : hh * |B| ≤ hh * (Real.sqrt hh
        * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by
      calc hh * |B| ≤ hh * Real.sqrt hh
            * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := h
        _ = hh * (Real.sqrt hh
            * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by ring
    exact le_of_mul_le_mul_left h' hhpos
  have hAMGM : Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))
      ≤ (∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2 := by
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have hz4 : 0 < z₀ ^ 4 := by positivity
    have harg : 0 ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by positivity
    have hRnn : 0 ≤ (∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2 := by positivity
    have hsq : (Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) ^ 2
        ≤ ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) ^ 2 := by
      rw [Real.sq_sqrt harg]
      set T := ∫ z in Work.Spaces.Iz, Q z with hTdef
      have ha : (Real.pi / 2) / z₀ ^ 4 * T = (T / z₀ ^ 4) * (Real.pi / 2) := by ring
      have hb : (T / z₀ ^ 4 + Real.pi / 2) ^ 2
          = (T / z₀ ^ 4) ^ 2 + 2 * (T / z₀ ^ 4) * (Real.pi / 2) + (Real.pi / 2) ^ 2 := by ring
      rw [ha, hb]
      nlinarith [sq_nonneg (T / z₀ ^ 4), sq_nonneg (Real.pi / 2), hTnn, hz4]
    have := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hRnn] at this
  have hgoal : |B| ≤ ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh :=
    calc |B| ≤ Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) :=
          hBbound
      _ ≤ Real.sqrt hh * ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hAMGM (Real.sqrt_nonneg _)
      _ = ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh := by ring
  rw [hBdef] at hgoal ⊢
  rw [hQdef] at hgoal
  simpa only [hQdef] using hgoal

end DzIterOneSound

theorem DzIter_one_Psi_estimate_sound {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hPsi : ∀ z, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (z₀ : ℝ) (hz₀ : 0 < z₀)
    (hB : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∀ hh ∈ Set.Ioo (0 : ℝ) z₀,
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ|
        ≤ ((∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
              / z₀ ^ 4
            + Real.pi / 2) * Real.sqrt hh := by
  intro hh hhh
  obtain ⟨hhpos, hhlt⟩ := hhh
  have hzlt : z₀ < z₀ + hh := by linarith
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the `ℋ⁰`-integrability of the weighted `z²∂_z²Ψ`
  have hA := hkMemW0L2 hk h
  have hQJ : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := hA.2.1
  have hCsall := hA.2.2
  -- the absolute-value integrability package
  have hF := hkMemSliceAbsIntegrable hk h hz₀ hzlt
  have hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ (z₀ + hh)) :=
    hF.2.1
  have hrectAbs : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hF.2.2.1
  -- the fundamental theorem of calculus along the slices
  have hFtc := aeSliceFtcPzIter2 hk h hz₀ (le_of_lt hzlt)
  -- the restricted data
  have hCs : ∀ z ∈ Set.Icc z₀ (z₀ + hh), ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
    fun z hz => hCsall z (lt_of_lt_of_le hz₀ hz.1)
  have hsl : ∀ z ∈ Set.Icc z₀ (z₀ + hh), MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    fun z hz => hF.1 z (lt_of_lt_of_le hz₀ hz.1)
  -- the joint integrability on the rectangle
  have hrect := pzSinCos2_rectIntegrable hsm hz₀ hzlt hB hsl hFint
  -- Fubini and the vanishing of the average
  have hfub := pzSliceFubiniZero hsm hz₀ hzlt (hPsi z₀ hz₀)
    (hPsi (z₀ + hh) (by linarith)) (h.orthPsi z₀ hz₀) (h.orthPsi (z₀ + hh) (by linarith))
    hrect
  exact DzIterOneSound.coreBound hz₀ hhpos hhlt hB hQJ hCs hFint hrectAbs hFtc hrect hfub.1 hfub.2

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Lzero1` commutes with `∂_z` on slices

`Lzero1PzComm`: the angular operator `Lzero1` of `Work.FTS.EllipticEst.StraightDefs`
commutes with the radial derivative `∂_z` on the slices of a function `C^∞` on the open
quadrant.  The proof is the slice-level analogue of the `Lzero`-commutation
`pz_Lzero_eq` of `sliceShiftedDecomposition.lean`: `Lzero1` applied to the `z`-slice of
`Φ` is (definitionally) `Work.Elliptic.Lzero Φ` evaluated at the same point
(`Lzero1_slice_eq`), and `∂_z` commutes with each of the three summands of `Lzero` — the
pure angular term by iterated Clairaut (`pz_pthIter_two_eq`), the `tan θ·Φ` term by
Clairaut for the smooth function `tan θ·Φ` (`pz_pth_tanMulS_eq`), and the identity term
trivially.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Auxiliary vocabulary and elementary facts -/

/-- `tan θ · g` as a two-variable function: the angular factor of `Work.Elliptic.Lzero`. -/
private def tanMulS (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.tan θ * g z θ

/-- `∂_z` commutes with multiplication by `tan θ`. -/
private lemma pz_tanMulS (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (tanMulS g) = tanMulS (Work.Spaces.pz g) := by
  funext z θ
  simp only [tanMulS, Work.Spaces.pz]
  rw [deriv_const_mul_field]

/-- `ContDiffAt`-form of `SmoothOpen` at an interior point of the open quadrant. -/
private lemma smoothOpen_contDiffAt_two'' {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hf.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- `SmoothOpen` of `(z,θ) ↦ tan θ · Ψ z θ` (the angular factor `tan` is smooth on the
open quadrant). -/
private lemma smoothOpen_tanMulS {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (tanMulS Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (tanMulS Ψ))
    Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (tanMulS Ψ)
      = fun p : ℝ × ℝ => Real.tan p.2 * Ψ p.1 p.2 from rfl]
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have hs : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_sin.comp_contDiffOn contDiffOn_snd
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_cos.comp_contDiffOn contDiffOn_snd
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h1], h2⟩)
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      hs.div hc hne
    refine hdiv.congr (fun p _ => ?_)
    rw [Real.tan_eq_sin_div_cos]
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := hΨ
  exact htan.mul hΨ'

/-! ## Commutation of `∂_z` with the summands of `Lzero` -/

/-- `∂_z ∂_θ² Φ = ∂_θ² ∂_z Φ` on the open quadrant (two instances of Clairaut). -/
private lemma pz_pthIter_two_eq {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Φ) z θ := by
  have hV : IsOpen (Work.FTS.EllipticEst.Q0) := Work.FTS.EllipticEst.isOpen_Q0
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Φ)) z θ :=
    Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two'' hΦ.pth hz hθ)
  have heqon : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Φ)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz Φ))) Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
    exact Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two'' hΦ hz' ⟨hθ'1, hθ'2⟩)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Φ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV heqon hp
  show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Φ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Φ)) z θ
  rw [h1, h2]

/-- `∂_z ∂_θ(tan θ · Φ) = ∂_θ ∂_z(tan θ · Φ)` on the open quadrant. -/
private lemma pz_pth_tanMulS_eq {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ
      = Work.Spaces.pth (tanMulS (Work.Spaces.pz Φ)) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hC2 : ContDiffAt ℝ 2 (Function.uncurry (tanMulS Φ)) (z, θ) :=
    ((smoothOpen_tanMulS hΦ).forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.Spaces.pz_pth_comm hC2, pz_tanMulS]

/-! ## The commutation theorem -/

/-- **`Lzero1` commutes with `∂_z` on slices.**

Let `Φ : ℝ → ℝ → ℝ` be `C^∞` on the open quadrant, `z > 0`, `0 < θ < π/2`.  Then the angular
operator `Lzero1 u = -u'' + (tan·u)' - 6u` applied to the `z`-derivative of the slice equals the
`z`-derivative of `Lzero1` applied to the slice:

`Lzero1 (fun t => pz Φ z t) θ = deriv (fun z' => Lzero1 (fun t => Φ z' t) θ) z`.

Note for the prover: the same identity (with the two sides swapped and `Lzero` on a slice in
place of `Lzero1`) is ALREADY proved in `remov/SourceBound/sliceShiftedDecomposition.lean`, as the
private helper `pz_Lzero_eq` (line 159, with `hasDerivAt_Lzero_slice` at line 131) under the
hypothesis `hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ` and `hz : 0 < z`, `hθ ∈ Ioo 0 (π/2)`; that
file is axiom-clean, so the present statement can be obtained by adapting that proof (only the
`rfl`-identification `Lzero Ψ z x = Lzero1 (fun t => Ψ z t) x` and the swapped sides are needed),
using `Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth`.  Alternatively, redo the Clairaut
argument directly with `Work.Spaces.pz_pth_comm`. -/
theorem Lzero1PzComm {Φ : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ
      = deriv (fun z' => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z' t) θ) z := by
  have hΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  have htanmul : Work.FTS.EllipticEst.SmoothOpen (tanMulS Φ) := smoothOpen_tanMulS hΦ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Φ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ) z :=
    (hΦ.pth.pth).hasDerivAt_slice hθm hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (tanMulS Φ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) z :=
    htanmul.pth.hasDerivAt_slice hθm hz
  have hd3 : HasDerivAt (fun z' => Φ z' θ) (Work.Spaces.pz Φ z θ) z :=
    hΦ.hasDerivAt_slice hθm hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Φ z' θ)
        + Work.Spaces.pth (tanMulS Φ) z' θ - 6 * Φ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) - 6 * Work.Spaces.pz Φ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have hval : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMulS Φ)) z θ) - 6 * Work.Spaces.pz Φ z θ)
      = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ := by
    rw [pz_pthIter_two_eq hΦ hz hθm, pz_pth_tanMulS_eq hΦ hz hθm, Lzero1_slice_eq]
    rfl
  rw [hval] at hsum
  have hmain : HasDerivAt (fun z' => Work.Elliptic.Lzero Φ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ) z :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => rfl))
  have hmain2 : HasDerivAt (fun z' => Work.FTS.EllipticEst.Lzero1 (fun t => Φ z' t) θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Φ z t) θ) z :=
    hmain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z' => (Lzero1_slice_eq Φ z' θ).symm))
  exact hmain2.deriv.symm

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

set_option autoImplicit false

/-- **Subtraction companion of `Work.FTS.LocData.L12_add_mul`.**  Under the *same* four
integrability hypotheses as the additivity half of `L12_add_mul` (the `θ`-slices of `a` and of
`b` integrable on `Iθ` for every `s > z`, and the two densities integrable on `(z,∞)`), the
`L₁₂`-integral of the difference splits:

`L₁₂(a - b)(z) = L₁₂ a(z) - L₁₂ b(z)`.

The point is that `L12_add_mul` already provides both linearity identities it is stated with —
additivity of `a + ·` and homogeneity in a constant `c` *of its first argument* — so
`a - b = a + (-1)·b` splits as `L₁₂ a + L₁₂ ((-1)·b)`, and the second summand is
`(-1)·L₁₂ b`.  No hypothesis beyond the four integrability inputs is needed: the two auxiliary
integrability statements for the rescaled datum `(-1)·b` are obtained from those of `b` by
`Integrable.const_mul` together with the pointwise homogeneity of the density
(`Work.FTS.LocData.L12dens_const_mul`). -/
theorem L12_sub_of_integrable {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  -- the `θ`-slice of the rescaled datum `(-1)·b` is integrable (the slices of `b` are)
  have hslice_nb : ∀ s ∈ Set.Ioi z,
      IntegrableOn (fun θ => Work.Spaces.K θ * ((-1) * b s θ) / s) Work.Spaces.Iθ := by
    intro s hs
    refine IntegrableOn.congr_fun
      (Integrable.const_mul (h2 s hs) (-1)) (fun θ _ => ?_) measurableSet_Icc
    ring
  -- and so is its density, by pointwise homogeneity of the density
  have hdens_nb : IntegrableOn
      (Work.Construction.L12dens (fun z θ => (-1) * b z θ)) (Set.Ioi z) := by
    refine IntegrableOn.congr_fun
      (Integrable.const_mul h4 (-1)) (fun s _ => ?_) measurableSet_Ioi
    exact (Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s).symm
  -- additivity of `L₁₂` applied to the pair `(a, (-1)·b)`
  obtain ⟨hadd, -⟩ :=
    Work.FTS.LocData.L12_add_mul (c := -1) h1 hslice_nb h3 hdens_nb
  -- homogeneity of `L₁₂` at `c = -1`, applied to `b`
  have hhom : Work.Construction.L12 (fun z θ => (-1) * b z θ) z
      = (-1) * Work.Construction.L12 b z :=
    (Work.FTS.LocData.L12_add_mul (c := -1) (a := b) (b := b) h2 h2 h4 h4).2
  have heq : (fun z θ => a z θ - b z θ) = fun z θ => a z θ + (-1) * b z θ := by
    funext z θ
    ring
  rw [heq, hadd, hhom]
  ring

/-- **Additivity of `L₁₂` on the honest `ℋ⁴`-class, on the half-line `z ∈ Iz`.**  With `a`, `b`
of class `SmoothOpen` and honest weighted `ℋ⁴`-size, `z ↦ L₁₂(a - b)(z)` splits as
`L₁₂ a - L₁₂ b` for every `z ∈ Iz`.

The restriction `z ∈ Iz = [0,∞)` is essential and is the correction of a review: for `z < 0` the
density is integrated over `(z,∞) ⊃ (z,0)`, where `SmoothOpen`/`HkMem` give no control at all and
the Bochner integral is the junk value `0` (`integral_undef`), so additivity genuinely fails there.
For `z ≥ 0` every `s > z` satisfies `s > 0`, so the slice integrability required by the proved
`Work.FTS.LocData.L12_add_mul` (`Submission/Work/FTS/LocData/L12_add_mul.lean`) follows from
`HkMem α 4 a`/`HkMem α 4 b` (the proved `integrableOn_slice_of_SmoothOpen_HkMem` /
`integrableOn_L12dens_of_SmoothOpen_HkMem`), and `IntegrableOn.mono_set` transfers the density
integrability from `Ioi 0` to `Ioi z`.  The `z = 0` case is the proved
`Work.FTS.GalBasis.cc.L12_add_of_HkMem` (`Submission/Work/FTS/GalBasis/cc/L12_add_of_HkMem.lean`);
subtraction is the homogeneity case `c = -1`.

*Proof.*  The uniform argument `L12_sub_of_integrable` (above) covers every `z ∈ Iz` at once: for
`s > z ≥ 0` the slice integrability is `integrableOn_slice_of_SmoothOpen_HkMem`, and
`IntegrableOn.mono_set` along `Ioi z ⊆ Ioi 0` (from `0 ≤ z`) gives the two density
integrability statements; `a - b = a + (-1)·b` then splits by `L12_add_mul`. -/
theorem L12_sub_HkMem {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z ∈ Work.Spaces.Iz, Work.Construction.L12 (fun z θ => a z θ - b z θ) z
      = Work.Construction.L12 a z - Work.Construction.L12 b z := by
  intro z hz
  have hz0 : 0 ≤ z := hz
  -- for `s > z ≥ 0` the `θ`-slice of `K · f s · / s` is integrable, from `HkMem α 4 f`
  have hslt : ∀ s ∈ Set.Ioi z, 0 < s := fun s hs => lt_of_le_of_lt hz0 (Set.mem_Ioi.mp hs)
  refine L12_sub_of_integrable (z := z) ?_ ?_ ?_ ?_
  · intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma (hslt s hs)
  · intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb (hslt s hs)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem ha hma).mono_set
      (Set.Ioi_subset_Ioi hz0)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hb hmb).mono_set
      (Set.Ioi_subset_Ioi hz0)

end Work.FTS.StrongEps.EComparison
end
