import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.L12.linPart_tendsto
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.smoothOpen_slice_of_epsRHSP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXA1.abs_mixed_le_HkNorm_C4_proved
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllSol.VthAuxC.certC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAuxC

/-- **The `ℋ⁴`-certificate of the orthogonalised source and of the layer `Ḡ·sin 2θ`.**

For every profile `g` of the linear class `C` (`Work.FTS.EllSol.ClassC α g`) and every
`α ∈ (0,1]` the two objects feeding the `V^{th}` slot of the elliptic package,
`orthSource g = g - (15/4)·sin 2θ·F_*(g)` and `Ḡ(α,g)·sin 2θ`, are `C^∞` on the open quadrant and
honestly in `ℋ⁴`, with `ℋ⁴`-norms bounded by a universal constant times `|g|_{ℋ⁴}`; the constant
is *independent of `α ∈ (0,1]`*.

Route (verbatim from `Work.FTS.EllSol.orthSource_HkNorm_le` and
`Work.FTS.EllipticEst.Cert.GbarSin_layer`, with `EllClassO` replaced by the class fields):

* `orthSource g = g + (-(15/4))·Φ` with `Φ = F_*(g)·sin 2θ`, so the `C^∞`-part is the sum of
  `h.reg` and the separated product `SmoothOpen.sep_mul h.fsm (fun_prop)` (via
  `EllExist.smoothOpen_orthSource_of_Fstar_smooth`), and the `ℋ⁴`-norm bound is the triangle
  inequality `HkNorm_add_le` plus `HkNorm_const_mul` together with the certificate
  `Cert.Fstar_Hk_le_open 4` for `Φ`;
* the same triangle inequality gives the membership
  (`EllExist.hkMem_orthSource_of_Fstar_smooth` at level `7`, descended to level `4` by
  `HkMem_mono_open`);
* `Ḡ(α,g) ∈ C^∞(0,∞)` is `Cert.Gbar_contDiffOn_Ioi` (it uses `F_*(g) ∈ C^∞(0,∞)`, i.e. `h.fsm`,
  and the integrability of `F_*(g)(r)/r`), so `Ḡ·sin 2θ` is `SmoothOpen.sep_mul` of the two;
  membership and norm bound are the layer certificate
  `GbarLayer.layer_{HkMem_target_of_smoothOpen, Gbar_HkNorm_le_SmoothOpen}`. -/
theorem certC : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllSol.ClassC α g →
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α 4 g ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
    Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
    Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
      ≤ C * Work.Spaces.HkNorm α 4 g := by
  -- the two `α`-uniform certificates
  obtain ⟨Cf, hCfpos, hFle⟩ := Work.FTS.EllipticEst.Cert.Fstar_Hk_le_open 4
  obtain ⟨Cg, hCgpos, hGle⟩ :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen 4
  refine ⟨max (Real.sqrt 2 * (1 + (15 / 4) * Cf)) Cg, ?_, ?_⟩
  · have hpos : (0 : ℝ) < Real.sqrt 2 * (1 + (15 / 4) * Cf) := by positivity
    exact lt_of_lt_of_le hpos (le_max_left _ _)
  · intro α g hα hα1 h
    -- ## the standing facts about the class-`C` profile
    have hreg : Work.FTS.EllipticEst.SmoothOpen g := h.reg
    have hfsm : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0) :=
      h.fsm
    have hmem7 : Work.Spaces.HkMem α 7 g := h.mem
    have hmem4 : Work.Spaces.HkMem α 4 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
    have hgram : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hreg
    -- ## `orthSource g`: smoothness
    have hOrthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) :=
      Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth hreg h.fsm
    -- ## `orthSource g`: membership (level `7`, descended to level `4`)
    have hOrthMem : Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) :=
      Work.FTS.OpenPkg.HkMem_mono_open hOrthSm 4 (by norm_num)
        (Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth hα hα1 hreg hmem7 h.fsm)
    -- ## the angular-moment term `Φ = F_*(g)·sin 2θ`
    have hΦsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hfsm (by fun_prop)
    have hΦraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hΦsm
    have hΦmem : Work.Spaces.HkMem α 4
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      have h := Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α 4 g hα hα1 hreg hmem4
      simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
    -- ## the scaled term `-(15/4)·Φ`
    have hSsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      hΦsm.const_mul' (-(15 / 4))
    have hSraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry
          (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSsm
    have hSmem : Work.Spaces.HkMem α 4
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-(15 / 4)) hΦmem
    -- ## `orthSource g` as the sum of the two summands
    have horth : Work.Elliptic.orthSource g
        = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Elliptic.orthSource]
      ring
    -- ## the norm bound for `orthSource g` (triangle inequality + `Cert.Fstar_Hk_le_open 4`)
    have hsum := Work.FTS.EllipticEst.HkNorm_add_le α 4 hgram hSraw hmem4 hSmem
    have hcm := Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-(15 / 4)) hΦraw
    have hPhi := hFle α g hα hα1 hgram hmem4
    have hOrthLe : Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
        ≤ (Real.sqrt 2 * (1 + (15 / 4) * Cf)) * Work.Spaces.HkNorm α 4 g := by
      rw [horth]
      calc Work.Spaces.HkNorm α 4
            (fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
          ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + Work.Spaces.HkNorm α 4 (fun z θ => (-(15 / 4))
                  * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))) := hsum
        _ = Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + (15 / 4) * Work.Spaces.HkNorm α 4
                  (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
            rw [hcm, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4)]
        _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 g
              + (15 / 4) * (Cf * Work.Spaces.HkNorm α 4 g)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
            have h1 : (15 / 4) * Work.Spaces.HkNorm α 4
                  (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))
                ≤ (15 / 4) * (Cf * Work.Spaces.HkNorm α 4 g) :=
              mul_le_mul_of_nonneg_left hPhi (by norm_num)
            linarith
        _ = (Real.sqrt 2 * (1 + (15 / 4) * Cf)) * Work.Spaces.HkNorm α 4 g := by ring
    -- ## the layer `Ḡ(α,g)·sin 2θ`
    have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
        (Set.Ioi 0) :=
      Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem7
    have hGbsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm hFint
    have hGbsinSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hGbsm (by fun_prop)
    have hGbsinMem : Work.Spaces.HkMem α 4
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 4 g hreg
        hmem4
    have hGbsinLe : Work.Spaces.HkNorm α 4
        (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        ≤ Cg * Work.Spaces.HkNorm α 4 g :=
      hGle α g hα hα1 hreg hmem4
    -- ## assembling the two bounds into the common constant
    refine ⟨hOrthSm, hOrthMem, ?_, hGbsinSm, hGbsinMem, ?_⟩
    · exact le_trans hOrthLe
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.HkNorm_nonneg α 4 g))
    · exact le_trans hGbsinLe
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Work.Spaces.HkNorm_nonneg α 4 g))

end Work.FTS.EllSol.VthAuxC
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAuxC.poinC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAuxC

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# `poinC` — the level-`4` angular Poincaré estimate for `ellShift α g Φg`

The target is the angular Poincaré estimate for the straightened unknown
`U = ellShift α g Φg` of a datum whose *weak* elliptic class is part of the hypotheses:

`EllWeakPos α 4 (orthSource g) U` supplies the equation, the Dirichlet data, the smoothness on the
open quadrant and the honesty `HkMem α 4 (∂_θ²U)`; the level-`4` angular Poincaré then gives
`HkMem α 4 U`, `HkMem α 4 (∂_θU)` and the two norm comparisons.

## Route

Apply the (proved) `Work.FTS.EllSol.ropPoincareAe`, which needs, besides the weak class, the two
endpoint *traces* of the radial iterates of the slices:

* for `j ≤ 3` at every `z > 0` (pointwise),
* for `j = 4` for almost every `z > 0`,

and the endpoint *values* `D_z^j U z 0 = D_z^j U z (π/2) = 0` for `j ≤ 4`.

The values come from the Dirichlet data (`VanishTheta`, transported by `D_z^j`, which differentiates
only in `z`).  The traces come from slice continuity plus those values; and slice continuity is
read off the weak class by *shifting it down*:

* `EllWeakPos_DzIter_one_shift_of_two_le` gives
  `EllWeakPos α 3 (D_z F) (D_z U)`, `EllWeakPos α 2 (D_z²F) (D_z²U)`, `EllWeakPos α 1 (D_z³F) (D_z³U)`;
* `AeClean.sliceContinuous_of_weakPos_fts` turns each of those into the pointwise continuity of
  the corresponding slice — this covers `j ≤ 3`;
* `H2W.weakSliceZContinuousAe` applied to the level-`2` shift gives the continuity of
  `D_z²(D_z²U) = D_z⁴U` on a conull set of `z` — this covers `j = 4`.

Neither the class `ClassC α g` nor the positivity of the solution nor the smoothness of `Φg` is
needed for this step; the weak class of the straightened unknown is exactly the honest budget.
-/

/-! ## Glue I: a slice which is continuous on `Iθ` and vanishes at an endpoint has limit `0` there

(Local copies of `tendsto_zero_of_continuousOn_Iθ_left/right`.) -/

theorem pc_tendsto_zero_left {u : ℝ → ℝ} (hc : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) :
    Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : ContinuousWithinAt u Work.Spaces.Iθ 0 :=
    hc.continuousWithinAt (by rw [Work.Spaces.Iθ]; exact ⟨le_refl 0, by positivity⟩)
  have h2 : Tendsto u (nhdsWithin (0 : ℝ) Work.Spaces.Iθ) (nhds 0) := by
    simpa [h0] using h1.tendsto
  have hmem : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio (Real.pi / 2), ?_, ?_⟩
    · exact isOpen_Iio.mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
    · intro x hx
      exact hx.1
  have heq : nhdsWithin (0 : ℝ) (Set.Iio (Real.pi / 2) ∩ Set.Ioi 0)
      = nhdsWithin (0 : ℝ) (Set.Ioi 0) := nhdsWithin_inter_of_mem hmem
  refine h2.mono_left ?_
  rw [← heq]
  exact nhdsWithin_mono 0 (fun θ hθ => ⟨le_of_lt hθ.2, le_of_lt hθ.1⟩)

theorem pc_tendsto_zero_right {u : ℝ → ℝ} (hc : ContinuousOn u Work.Spaces.Iθ)
    (h0 : u (Real.pi / 2) = 0) :
    Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : ContinuousWithinAt u Work.Spaces.Iθ (Real.pi / 2) :=
    hc.continuousWithinAt (by rw [Work.Spaces.Iθ]; exact ⟨by positivity, le_refl _⟩)
  have h2 : Tendsto u (nhdsWithin (Real.pi / 2) Work.Spaces.Iθ) (nhds 0) := by
    simpa [h0] using h1.tendsto
  have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (0 : ℝ), ?_, ?_⟩
    · exact isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
    · intro x hx
      exact hx.1
  have heq : nhdsWithin (Real.pi / 2) (Set.Ioi 0 ∩ Set.Iio (Real.pi / 2))
      = nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := nhdsWithin_inter_of_mem hmem
  refine h2.mono_left ?_
  rw [← heq]
  exact nhdsWithin_mono (Real.pi / 2) (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-! ## Glue II: the endpoint values of the radial iterates -/

theorem pc_dzIter_value_zero {f : ℝ → ℝ → ℝ} (hvan : Work.Spaces.VanishTheta f) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z 0 = 0
  | 0, z => hvan.1 z
  | j + 1, z => by
    show z * deriv (fun z' => Work.Spaces.DzIter j f z' 0) z = 0
    have h0 : (fun z' => Work.Spaces.DzIter j f z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => pc_dzIter_value_zero hvan j z'
    rw [h0]
    simp

theorem pc_dzIter_value_pi_half {f : ℝ → ℝ → ℝ} (hvan : Work.Spaces.VanishTheta f) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z (Real.pi / 2) = 0
  | 0, z => hvan.2 z
  | j + 1, z => by
    show z * deriv (fun z' => Work.Spaces.DzIter j f z' (Real.pi / 2)) z = 0
    have h0 : (fun z' => Work.Spaces.DzIter j f z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => pc_dzIter_value_pi_half hvan j z'
    rw [h0]
    simp

/-! ## The slice continuity of the radial iterates of a level-`4` weak datum -/

/-- **Pointwise slice continuity, `j ≤ 3`.**  For a datum of the weak class at level `4`, the
slices `θ ↦ D_z^jΨ z θ` are continuous on `Iθ` at *every* `z > 0`, for `j ≤ 3`.  (`D_z^j` is
differentiated only in the radial variable, so `D_z^jΨ` is again of the weak class at level
`4 - j ≥ 1`, and `sliceContinuous_of_weakPos_fts` applies.) -/
theorem pc_slice_continuous_le_three {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ)
    (j : ℕ) (hj : j ≤ 3) (z : ℝ) (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ) Work.Spaces.Iθ := by
  have h3 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 4) (by norm_num) h
  have h2 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 3) (by norm_num) h3
  have h1 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 2) (by norm_num) h2
  interval_cases j
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 4 (by norm_num) α F Ψ hα h z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 3 (by norm_num) α
        (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα h3 z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 2 (by norm_num) α
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F))
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ)) hα h2 z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 1 (by norm_num) α
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F)))
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ))) hα h1 z hz

/-- A.e. statements on `Iz` which hold at every `z > 0` transfer to `Ioi 0` (the two sets differ
by the null set `{0}`). -/
theorem pc_ae_Ioi_of_ae_Iz {p : ℝ → Prop}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), p z := by
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 < z → p z :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioi_subset_Ici_self h
  filter_upwards [h1, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzmem
  exact hz (Set.mem_Ioi.mp hzmem)

/-- **Almost-everywhere slice continuity, `j = 4`.**  For a datum of the weak class at level `4`
(with `α ≤ 1/4`), the slice `θ ↦ D_z⁴Ψ z θ` is continuous on `Iθ` for almost every `z > 0`: the
level-`2` shift of the class has its second radial iterate controlled by
`H2W.weakSliceZContinuousAe`, and `D_z²(D_z²Ψ) = D_z⁴Ψ`. -/
theorem pc_slice_continuous_four_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ) Work.Spaces.Iθ := by
  have h3 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 4) (by norm_num) h
  have h2 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 3) (by norm_num) h3
  have h4 := Work.H2W.weakSliceZContinuousAe α
    (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F))
    (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ)) hα hα4 h2
  refine pc_ae_Ioi_of_ae_Iz ?_
  filter_upwards [h4] with z hz
  intro hzpos
  have h4z := (hz hzpos).2
  simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h4z

/-- **The endpoint traces of a level-`4` weak datum.**  The `j ≤ 3` traces hold at every `z > 0`
and the `j = 4` trace almost everywhere. -/
theorem pc_traces {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ) :
    (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hvan : Work.Spaces.VanishTheta Ψ := ⟨h.zero, h.pi_half⟩
  refine ⟨fun j hj z hz => ?_, ?_⟩
  · exact ⟨pc_tendsto_zero_left (pc_slice_continuous_le_three hα h j hj z hz)
        (pc_dzIter_value_zero hvan j z),
      pc_tendsto_zero_right (pc_slice_continuous_le_three hα h j hj z hz)
        (pc_dzIter_value_pi_half hvan j z)⟩
  · filter_upwards [pc_slice_continuous_four_ae hα hα4 h] with z hz
    exact ⟨pc_tendsto_zero_left hz (pc_dzIter_value_zero hvan 4 z),
      pc_tendsto_zero_right hz (pc_dzIter_value_pi_half hvan 4 z)⟩

/-! ## The target -/


end

end Work.FTS.EllSol.VthAuxC
end
-- ===== merged: Submission.Work.FTS.Open2.Fields2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Apriori
open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.OpenPkg
open Work.FTS.OpenPkg.AprioriOpen
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000



end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstHkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAlt

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem hkMem_err (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (F : ℝ → ℝ → ℝ) (n : ℕ), 3 ≤ n → Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α k F → (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
        Work.FTS.PhiStar.ThetaTraces α k F →
          Work.Spaces.HkMem α k (Work.FTS.PhiStar.Honesty.CptApp.err n F) := by
  intro F n hn hsm hF hFs htr
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Ccrux, hCcruxpos, hcrux⟩ := theta_lintegral_le k α hα hα1
  have hCcrux : 0 ≤ Ccrux := hCcruxpos.le
  obtain ⟨RPb, hRPb0, hRPbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le k α
  obtain ⟨Cm, hCm0, hmom⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le (k := k) hsm hF hFs
  -- finiteness of `RP`
  have hvolI : (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    norm_num
  have hRPfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) < ⊤ := by
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := RPb * (Real.pi / 2)))
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal RPb :=
          lintegral_mono_ae (hRPbd.mono fun θ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal RPb * volume Work.Spaces.Iθ := by
          rw [lintegral_const]
          congr 1
          exact Measure.restrict_apply_univ Work.Spaces.Iθ
      _ = ENNReal.ofReal RPb * ENNReal.ofReal (Real.pi / 2) := by rw [hvolI]
      _ = ENNReal.ofReal (RPb * (Real.pi / 2)) := (ENNReal.ofReal_mul hRPb0).symm
  -- finiteness of the `Ω_n`-part
  have hPfin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ)) < ⊤ := fun z hz =>
    lt_of_le_of_lt (lintegral_ofReal_omegaPart_le hF hz) ENNReal.ofReal_lt_top
  -- finiteness of the moment factor (over `Ioi 0`, hence over `Iz`)
  have hQfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)) < ⊤ := by
    have hI : (volume.restrict (Set.Ioi (0 : ℝ))) = volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.restrict_Ioi_eq_restrict_Ici
    rw [← hI]
    exact lt_of_le_of_lt (hmom n hn2) ENNReal.ofReal_lt_top
  -- the per-`z` bound
  have hz : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ)) < ⊤ := by
    intro z hz'
    refine lt_of_le_of_lt (hcrux n F hn hsm htr z hz') ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨hPfin z hz',
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRPfin⟩)
  -- the angular slices of `omegaPart` are integrable in `θ`
  have hPfin2 : (∫⁻ z in Work.Spaces.Iz,
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Ici (fun z hz' => lintegral_ofReal_omegaPart_le hF hz'))) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact ENNReal.ofReal_lt_top
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) z θ) Work.Spaces.Iθ := by
    intro z hz'
    have hzge : (0 : ℝ) ≤ z := hz'
    rcases eq_or_lt_of_le hzge with h0 | hpos
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) 0 θ) = fun _ => 0 := by
        funext θ
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      rw [hzero]
      exact integrableOn_zero
    · have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k (err n F) z θ)
          (Set.Ioo 0 (π / 2)) :=
        ((EstAux.smoothOpen_err hsm hn1).continuousOn_HkIntegrand α k).comp
          (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => ⟨hpos, hθ⟩)
      refine ⟨(aemeasurable_restrict_Iθ hcont).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)]
      exact hz z hz'
  refine ⟨hsliceInt, ?_⟩
  refine ⟨(aemeasurable_integral_HkIntegrand (α := α) (k := k)
    (EstAux.smoothOpen_err hsm hn1)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)]
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (err n F) z θ)
        = ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz' =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsliceInt z hz')
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
  rw [lintegral_congr_ae hae]
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal Ccrux
          * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
            + ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                * ∑ m ∈ Finset.range (k + 1),
                    (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
        refine lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_)
        intro z hz'
        exact hcrux n F hn hsm htr z hz'
    _ = ENNReal.ofReal Ccrux
          * ((∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
            + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                * ∑ m ∈ Finset.range (k + 1),
                    (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_add_left'
          (aemeasurable_lintegral_omegaPart (α := α) (k := k) n hsm)]
        congr 1
        exact lintegral_mul_const' _ _ hRPfin.ne
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine ENNReal.add_lt_top.mpr ⟨hPfin2, ENNReal.mul_lt_top hQfin hRPfin⟩

end Work.FTS.PhiStar.Honesty.CptApp.EstAlt
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.FstarJepsSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux

set_option autoImplicit false

theorem FstarJepsSmooth {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} {W : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0) := by
  intro m
  -- the `s`-smoothness of the parametric integral
  have hsmooth : ContDiff ℝ m (fun s => ∫ x, Phi ρ ε W 0 s x * Work.Elliptic.sinCos2 x.1
      ∂(Jmu ε)) := by
    refine Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ParamIntegral
      (Φ := fun k s x => Phi ρ ε W k s x * Work.Elliptic.sinCos2 x.1) ?_ ?_ ?_ m
    · -- a.e. strong measurability
      intro k s
      have h1 : MeasureTheory.AEStronglyMeasurable (fun x : ℝ × ℝ => Phi ρ ε W k s x)
          (Jmu ε) := by
        change MeasureTheory.AEStronglyMeasurable
          (fun x : ℝ × ℝ => ∫ p₁ : ℝ, Work.Spaces.pzIter k
            (fun a b => Work.FTS.StrongEps.Jker ρ ε (a, b)) p₁ x.2
              * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε)
        exact Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.PhiAEStronglyMeasurable
          hρ hε hsm k s
      have h2 : Continuous (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1) := by
        rw [show (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1)
            = (fun x : ℝ × ℝ => Real.sin x.1 * Real.cos x.1 ^ 2) from rfl]
        fun_prop
      exact h1.mul h2.aestronglyMeasurable
    · -- the `s`-derivative
      intro k
      refine Filter.Eventually.mono ae_mem_Ioo_Jmu fun x hx => ?_
      intro s
      exact (hasDerivAt_Phi hρ hε hsm k s hx).mul_const _
    · -- the domination
      intro k s₀
      obtain ⟨G, hGint, hGdom⟩ :=
        Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem
          (a := Real.exp (s₀ - 1 - ε)) (b := Real.exp (s₀ + 1 + ε))
          (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))
      have hGnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G θ := fun θ hθ =>
        le_trans (abs_nonneg _) (hGdom _ ⟨le_refl _, Real.exp_le_exp.mpr (by linarith)⟩ θ hθ)
      have hinter : MeasureTheory.Integrable (fun x : ℝ × ℝ =>
          Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) :=
        integrable_sinCos2_mul_shift_of_integrableOn hGint
      refine ⟨fun x => (2 * ε * Classical.choose (exists_kernBound hρ hε k))
          * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)),
        hinter.const_mul _, ?_⟩
      refine Filter.Eventually.mono ae_mem_Ioo_Jmu fun x hx => ?_
      intro s hs
      have hsrange : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε →
          Real.exp (s - p₁) ∈ Set.Icc (Real.exp (s₀ - 1 - ε)) (Real.exp (s₀ + 1 + ε)) := by
        intro p₁ hp
        refine ⟨Real.exp_le_exp.mpr (by linarith [hs.1, hp.2]),
          Real.exp_le_exp.mpr (by linarith [hs.2, hp.1])⟩
      have h1 := abs_Phi_le hρ hε hsm hGnn hGdom hsrange k hx
      have hsin : 0 ≤ Work.Elliptic.sinCos2 x.1 := by
        rw [Work.Elliptic.sinCos2]
        exact mul_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
          (sq_nonneg _)
      have h2 : |Phi ρ ε W k s x * Work.Elliptic.sinCos2 x.1|
          = |Phi ρ ε W k s x| * Work.Elliptic.sinCos2 x.1 := by
        rw [abs_mul, abs_of_nonneg hsin]
      rw [h2]
      calc |Phi ρ ε W k s x| * Work.Elliptic.sinCos2 x.1
          ≤ ((2 * ε * Classical.choose (exists_kernBound hρ hε k))
              * G (Work.FTS.StrongEps.thShift x.1 x.2)) * Work.Elliptic.sinCos2 x.1 :=
            mul_le_mul_of_nonneg_right h1 hsin
        _ = (2 * ε * Classical.choose (exists_kernBound hρ hε k))
              * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
            ring
  -- the identification of the angular moment with the `s`-integral (Fubini swap)
  have hid : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) z
      = ∫ x, Phi ρ ε W 0 (Real.log z) x * Work.Elliptic.sinCos2 x.1 ∂(Jmu ε) := by
    intro z hz
    obtain ⟨G, hGint, hGdom⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.ZSliceDomination hsm hmem
        (a := Real.exp (Real.log z - ε)) (b := Real.exp (Real.log z + ε))
        (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))
    have hinter : MeasureTheory.Integrable (fun x : ℝ × ℝ =>
        Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) (Jmu ε) :=
      integrable_sinCos2_mul_shift_of_integrableOn hGint
    have hsrange : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε →
        Real.exp (Real.log z - p₁)
          ∈ Set.Icc (Real.exp (Real.log z - ε)) (Real.exp (Real.log z + ε)) := by
      intro p₁ hp
      exact ⟨Real.exp_le_exp.mpr (by linarith [hp.2]),
        Real.exp_le_exp.mpr (by linarith [hp.1])⟩
    have hswap := Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap hρ.moll hε hsm hGdom hinter (Real.log z) hsrange
    rw [Real.exp_log hz] at hswap
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Work.Elliptic.sinCos2 x.1 * (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)
        * W (Real.exp (Real.log z - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
      = Phi ρ ε W 0 (Real.log z) x * Work.Elliptic.sinCos2 x.1
    rw [show Phi ρ ε W 0 (Real.log z) x = (∫ p₁ : ℝ,
        Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)
          * W (Real.exp (Real.log z - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) from rfl]
    ring
  -- transfer `s`-smoothness back to the variable `z = e^s`
  have hlog : ContDiffOn ℝ m Real.log (Set.Ioi (0 : ℝ)) := fun x hx =>
    (Real.contDiffAt_log.mpr (ne_of_gt hx)).contDiffWithinAt
  exact (hsmooth.comp_contDiffOn hlog).congr (fun z hz => hid z hz)

end Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.linPart_tendsto_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 1000000




end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv5_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.LocUnif

/-- **The level-5 extraction.**  From the uniform convergence of all the slots `D_z^jD_θ^i` with
`j + i ≤ 4` (together with the uniform `H⁶` bound and the `C⁴` regularity of the limit `f`) there
is a further strictly increasing subsequence `φ'` along which every level-5 slot
`D_z^jD_θ^i` (`j + i = 5`) converges to the corresponding slot of `f` almost everywhere on the
open quadrant.

Each level-5 slot is one derivative (in `z` when `j ≥ 1`, in `θ` when `j = 0`) of a level-4 slot;
the extraction is done one slot at a time (`D5.round_slot`), each round using the exhaustion
`Q0 = ⋃ m, eBox m` of the quadrant by compact boxes and a diagonal subsequence argument. -/
theorem exists_subseq_deriv5_ae {α B : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv0 : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G (φ n) p.1 p.2) (fun p => f p.1 p.2)
        Filter.atTop K)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ (j i : ℕ), j + i = 5 →
        ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))),
          Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (φ' n))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  classical
  have hsm' : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n) :=
    fun n => Work.FTS.EllipticEst.smoothOpen_of_forall (hsm n)
  obtain ⟨Φ₀, hΦ₀, H₀⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 5) (i := 0) (by norm_num) (τ := id) strictMono_id
  obtain ⟨Φ₁, hΦ₁, H₁⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 4) (i := 1) (by norm_num) (τ := Φ₀) hΦ₀
  obtain ⟨Φ₂, hΦ₂, H₂⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 3) (i := 2) (by norm_num) (τ := Φ₀ ∘ Φ₁) (hΦ₀.comp hΦ₁)
  obtain ⟨Φ₃, hΦ₃, H₃⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 2) (i := 3) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂)
    (hΦ₀.comp (hΦ₁.comp hΦ₂))
  obtain ⟨Φ₄, hΦ₄, H₄⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 1) (i := 4) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃)
    (hΦ₀.comp (hΦ₁.comp (hΦ₂.comp hΦ₃)))
  obtain ⟨Φ₅, hΦ₅, H₅⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 0) (i := 5) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄)
    (hΦ₀.comp (hΦ₁.comp (hΦ₂.comp (hΦ₃.comp hΦ₄))))
  -- the tails of the tower
  have htail₅ : StrictMono (Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) :=
    hΦ₁.comp (hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅)))
  have htail₄ : StrictMono (Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) := hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅))
  have htail₃ : StrictMono (Φ₃ ∘ Φ₄ ∘ Φ₅) := hΦ₃.comp (hΦ₄.comp hΦ₅)
  have htail₂ : StrictMono (Φ₄ ∘ Φ₅) := hΦ₄.comp hΦ₅
  have htail₁ : StrictMono Φ₅ := hΦ₅
  set Φf : ℕ → ℕ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅ with hΦf
  have hΦf_mono : StrictMono Φf := by
    rw [hΦf]
    exact hΦ₀.comp (hΦ₁.comp (hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅))))
  -- the six slots, re-indexed by the full tower
  have hfin₀ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 5 0 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 5 0 f p.1 p.2)) := fun m => by
    filter_upwards [H₀ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 5 0 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 5 0 (G (φ (id (Φ₀ n)))) p.1 p.2)
          ∘ (Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf, id_eq]]
    exact (hp hm).comp htail₅.tendsto_atTop
  have hfin₁ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 4 1 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 4 1 f p.1 p.2)) := fun m => by
    filter_upwards [H₁ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 4 1 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 4 1 (G (φ (Φ₀ (Φ₁ n)))) p.1 p.2)
          ∘ (Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₄.tendsto_atTop
  have hfin₂ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 3 2 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 3 2 f p.1 p.2)) := fun m => by
    filter_upwards [H₂ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 3 2 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 3 2 (G (φ ((Φ₀ ∘ Φ₁) (Φ₂ n)))) p.1 p.2)
          ∘ (Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₃.tendsto_atTop
  have hfin₃ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 2 3 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 2 3 f p.1 p.2)) := fun m => by
    filter_upwards [H₃ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 2 3 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 2 3 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂) (Φ₃ n)))) p.1 p.2)
          ∘ (Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₂.tendsto_atTop
  have hfin₄ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 1 4 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 1 4 f p.1 p.2)) := fun m => by
    filter_upwards [H₄ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 1 4 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 1 4 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃) (Φ₄ n)))) p.1 p.2)
          ∘ Φ₅ from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₁.tendsto_atTop
  have hfin₅ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 0 5 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 0 5 f p.1 p.2)) := fun m => by
    filter_upwards [H₅ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 0 5 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 0 5 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄) (Φ₅ n))))
            p.1 p.2) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact hp hm
  refine ⟨Φf, hΦf_mono, ?_⟩
  intro j i hji
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · -- the slot `(0, 5)`
    have hi : i = 5 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₅
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(1, 4)`
    have hi : i = 4 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₄
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(2, 3)`
    have hi : i = 3 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₃
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(3, 2)`
    have hi : i = 2 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₂
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(4, 1)`
    have hi : i = 1 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₁
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(5, 0)`
    have hi : i = 0 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₀
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem mixed_JfamP_tendsto {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α B : ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    {τ : ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B
      (fun n => Work.FTS.Galerkin.slice (G n) τ) (Work.FTS.Galerkin.slice g τ))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0)
      Filter.atTop (nhds 0))
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) τ) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) := by
  -- **(1)** The slots of the *mollified* family converge: this is `E1` plus the peak estimate.
  have hJ : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) :=
    Work.FTS.StrongEps.mixed_Jeps_tendsto hρ.moll hsm hconv hεpos hε0 hp hji
  -- **(2)** The `P₀`-coefficients vanish in the limit.
  have hL : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
    have := hl12.div_const pzNorm
    simpa using this
  have hc : Filter.Tendsto
      (fun n : ℕ => (Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
        * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
      Filter.atTop (nhds 0) := by
    have := hL.mul_const (Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
    simpa using this
  -- **(3)** The slot of the projected family is the slot of the mollified profile minus the
  -- rank-one correction, pointwise in `n` (`PZeroAux.mixed_Pz`).
  have hmain : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2
        - (Work.Construction.L12
            (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) := by
    simpa using hJ.sub hc
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hmain
  have hloc : MeasureTheory.LocallyIntegrable
      (logPull (Work.FTS.Galerkin.slice (G n) τ)) MeasureTheory.volume :=
    locallyIntegrable_logPull_of_forall_contDiffOn (fun k => hsm n k)
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
      (fun k => Jeps_contDiffOn ρ hρ (hεpos n) hloc k)
  show Work.Spaces.mixed j i
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2
      - (Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
        * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2
    = Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) τ) p.1 p.2
  rw [slice_JfamP]
  exact (Work.FTS.StrongEps.PZeroAux.mixed_Pz hsmJ hp.1 hp.2 j i).symm

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The pointwise majorant of the `ℋ⁶`-integrand of a product** (the `C^6` shift of
`Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6`): summing the at most seven radial
slots and the at most forty-nine mixed slots of `HkIntegrand α 6 (f·g)` gives
`HkIntegrand α 6 (f·g) ≤ (7 Cz + 49 Cm) |f|²_{𝒲^{6,∞}} GmajW6 α g`. -/
theorem prod_majorant_cd6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f)
    (hgsm : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_nonneg hα g hθ
  have hbase : 0 ≤ (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [Work.Blocks.Half.HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : Work.Spaces.HkIntegrand α 6 g z θ
          ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand_le_GmajW6 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (6 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1),
              (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (6 + 1), (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi6 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
                (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 6
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (6 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            + 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
    · have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand6_eq_zero_of_sin_two_eq_zero
        (α := α) (F := fun z θ => f z θ * g z θ) (z := z) (θ := θ)
        (by rw [Work.Spaces.gam]; linarith) hsin]
      exact hbase

/-- **The `𝒲^{6,∞}`-priced product rule with `C^6` data.**  If `f` is `C^6` on the open
quadrant and of class `𝒲^{6,∞}`, and `g` is `C^6` on the open quadrant and of class `ℋ⁶`, then
`f·g` is of class `ℋ⁶`. -/
theorem HkMem_mul_of_WlInf6_cd6 {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfw : Work.Spaces.WlInfMem α 6 f)
    (hgs : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g) :
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) := by
  obtain ⟨CB, _hCBpos, hCBmean⟩ := Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cz, hCz, hZ⟩ := Cd6.zslot_le_winf6_cd6
  obtain ⟨Cm, hCm, hMx⟩ := Cd6.mslot_le_winf6_cd6 CB
  have hmaj := prod_majorant_cd6 hα hα1 hfs hfw hgs hgm hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' =>
        hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)
  set K : ℝ := 7 * Cz + 49 * Cm with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKg
  have hKgpos : 0 < Kg := by
    rw [hKg]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  -- the product is `C^6` on the open quadrant, so its integrand is continuous there
  have hfg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ * g z θ))
      Work.FTS.EllipticEst.Q0 := Cd6.contDiffOn_uncurry_mul_cd6 hfs hgs
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Cd6.continuousOn_HkIntegrand_cd6 (le_refl 6) hfg
  -- the pointwise majorant
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro z hz θ hθ
    rw [hK]
    exact hmaj z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6
      (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul
          (K * (Work.Spaces.WlInf α 6 f) ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (Cd6.continuousOn_HkIntegrand_cd6 (le_refl 6) hfg) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 6 f) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      simpa only [hKg] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := g)
          hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
      _ = (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by ring
  -- the dominating function of the `z`-integral
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) Work.Spaces.Iz :=
    hgm.2.const_mul _
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      hcont).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
    exact hbdd z hz
  exact ⟨hslice, hzg⟩

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork
end
