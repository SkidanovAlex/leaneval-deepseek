import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.HkMem_FstarSin_open
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set

theorem interval_sq_le_Itheta {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, h x ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  -- `[a,b] ⊆ (0,π/2) ⊆ Iθ`, since `0 < a` and `b < π/2`.
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt (ha.trans hx.1), le_of_lt (hx.2.trans_lt hb)⟩
  -- Rewrite the interval integral as a set integral over `(a,b]`.
  rw [intervalIntegral.integral_of_le hab]
  -- On `(a,b]` the weight satisfies `thEta ≥ 1`, so `h² ≤ h²·thEta` there.
  have hstep2 : ∫ x in Set.Ioc a b, h x ^ 2
      ≤ ∫ x in Set.Ioc a b, h x ^ 2 * Work.FTS.EllipticEst.thEta x := by
    refine setIntegral_mono_of_nonneg (fun x _ => sq_nonneg (h x)) (fun x hx => ?_)
      (hint.mono_set hsub)
    exact le_mul_of_one_le_right (sq_nonneg (h x))
      (one_le_thEta_of_mem_Ioo ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)
  -- Enlarge the set of integration from `(a,b]` to `Iθ`, using that the integrand is
  -- nonnegative on `Iθ`.
  have hstep3 : ∫ x in Set.Ioc a b, h x ^ 2 * Work.FTS.EllipticEst.thEta x
      ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · exact Filter.Eventually.of_forall fun x hx => hsub hx
  exact hstep2.trans hstep3

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false

/-- The one-variable logarithmic Schur operator of the kernel `sKerd δ`:

  `zSchur δ g z = ∫ t, sKerd δ (log z - t) * g (exp t)`.

It is the operator obtained by moving the `D_z`-derivative of the `z`-mollification onto the
kernel, applied to a single angular slice `g` (i.e. `g w = G w s` for a fixed `s`). -/
def zSchur (δ : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * g (Real.exp t)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c (Qext Qext_of_mem)

set_option autoImplicit false

/-! ## The three branches of the doubly-odd extension `Qext`

`Qext u z s` equals `u z s` for `s ∈ [0, π/2]`, `-u z (-s)` for `s < 0` and
`-u z (π - s)` for `s > π/2`.  The two lemmas below record the two *reflected* branches,
which are the ones used when the argument leaves the closed interval `[0, π/2]`. -/

/-- The branch of the doubly-odd extension `Qext` on the left of the origin. -/
theorem Qext_of_lt_zero (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Qext u z s = -u z (-s) := by
  rw [Qext, if_neg (fun h => (not_le.mpr hs) h.1), if_pos hs]

/-- The branch of the doubly-odd extension `Qext` beyond `π/2`. -/
theorem Qext_of_pihalf_lt (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Qext u z s = -u z (Real.pi - s) := by
  have h0s : (0 : ℝ) < s := by linarith [Real.pi_pos, hs]
  rw [Qext, if_neg (fun h => (not_le.mpr hs) h.2), if_neg (not_lt.mpr h0s.le)]

/-- **Continuity of the doubly-odd extension on `(-1, π/2 + 1)`.**

For a trace-class datum `G` (`TraceClass G`) and a radius `w > 0`, the angular slice
`s ↦ Qext G w s` is continuous on `(-1, π/2 + 1)`.  On the interval `(-1, π/2 + 1)` every
reflected argument `-s` (for `s < 0`) or `π - s` (for `s > π/2`) lies in the open quadrant
interval `(0, π/2)`, where the slice is continuous by `SmoothOpen`; the two junctions
`s = 0` and `s = π/2` are handled by the vanishing traces of `TraceClass`, which make the
two one-sided limits agree with the value there. -/
theorem qext_continuousOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G w s)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, -, -, -⟩ := hT
  set Q : ℝ → ℝ := fun s => Qext G w s with hQ
  -- ## The angular slice of `G` at radius `w` and its two one-sided traces
  have hslice : ContinuousOn (fun θ : ℝ => G w θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).continuousOn
  have hL0 : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) 0 := by
    simpa [ContinuousWithinAt, h0 w] using htr0 w hw
  have hLpi : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    simpa [ContinuousWithinAt, hpi w] using htrpi w hw
  -- ## The three branches of `Q`
  have hQneg : Set.EqOn Q (fun s : ℝ => -G w (-s)) (Set.Iio 0) := fun s hs => by
    simp only [hQ]; exact Qext_of_lt_zero G w s hs
  have hQmid : Set.EqOn Q (fun s : ℝ => G w s) (Set.Ioo 0 (Real.pi / 2)) := fun s hs => by
    simp only [hQ]; exact Qext_of_mem G w s ⟨hs.1.le, hs.2.le⟩
  have hQgt : Set.EqOn Q (fun s : ℝ => -G w (Real.pi - s)) (Set.Ioi (Real.pi / 2)) :=
    fun s hs => by
      simp only [hQ]; exact Qext_of_pihalf_lt G w s hs
  have hQ0 : Q 0 = G w 0 := by
    simp only [hQ]; exact Qext_of_mem G w 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hQpi : Q (Real.pi / 2) = G w (Real.pi / 2) := by
    simp only [hQ]
    exact Qext_of_mem G w (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
  -- ## Continuity on the three open pieces
  have hA : ContinuousOn Q (Set.Ioo (-1) 0) := by
    have hmap : MapsTo (fun s : ℝ => -s) (Set.Ioo (-1) 0) (Set.Ioo 0 (Real.pi / 2)) :=
      fun s hs => by
        simp only [Set.mem_Ioo] at hs ⊢
        exact ⟨by linarith [hs.2], by linarith [hs.1, Real.pi_gt_three]⟩
    have hcomp : ContinuousOn (fun s : ℝ => -G w (-s)) (Set.Ioo (-1) 0) :=
      (hslice.comp continuous_neg.continuousOn hmap).neg
    exact hcomp.congr (fun s hs => hQneg hs.2)
  have hB : ContinuousOn Q (Set.Ioo 0 (Real.pi / 2)) := hslice.congr hQmid
  have hC : ContinuousOn Q (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) := by
    have hmap : MapsTo (fun s : ℝ => Real.pi - s) (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1))
        (Set.Ioo 0 (Real.pi / 2)) := fun s hs => by
      simp only [Set.mem_Ioo] at hs ⊢
      exact ⟨by linarith [hs.2, Real.pi_gt_three], by linarith [hs.1]⟩
    have hcont : ContinuousOn (fun s : ℝ => Real.pi - s)
        (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) := by fun_prop
    have hcomp : ContinuousOn (fun s : ℝ => -G w (Real.pi - s))
        (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) :=
      (hslice.comp hcont hmap).neg
    exact hcomp.congr (fun s hs => hQgt hs.1)
  -- ## The two junctions
  have hj0L : ContinuousWithinAt Q (Set.Iio 0) 0 := by
    have hmap : MapsTo (fun s : ℝ => -s) (Set.Iio 0) (Set.Ioi 0) := fun s hs => by
      simp only [Set.mem_Iio] at hs
      simp only [Set.mem_Ioi]
      linarith
    have h' : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) (-0) := by
      simpa using hL0
    have hcomp : ContinuousWithinAt (fun s : ℝ => -G w (-s)) (Set.Iio 0) 0 :=
      (h'.comp continuous_neg.continuousWithinAt hmap).neg
    refine hcomp.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hQneg) ?_
    simp [hQ0, h0 w]
  have hj0R : ContinuousWithinAt Q (Set.Ioi 0) 0 := by
    have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝[Set.Ioi 0] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hEq : Q =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)] (fun s : ℝ => G w s) :=
      Filter.eventually_of_mem hmem (fun s hs => hQmid hs)
    exact hL0.congr_of_eventuallyEq hEq hQ0
  have hj0 : ContinuousAt Q 0 :=
    continuousAt_iff_continuous_left'_right'.mpr ⟨hj0L, hj0R⟩
  have hjpiL : ContinuousWithinAt Q (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2) :=
      Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hEq : Q =ᶠ[𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)] (fun s : ℝ => G w s) :=
      Filter.eventually_of_mem hmem (fun s hs => hQmid hs)
    exact hLpi.congr_of_eventuallyEq hEq hQpi
  have hjpiR : ContinuousWithinAt Q (Set.Ioi (Real.pi / 2)) (Real.pi / 2) := by
    have hmap : MapsTo (fun s : ℝ => Real.pi - s) (Set.Ioi (Real.pi / 2))
        (Set.Iio (Real.pi / 2)) := fun s hs => by
      simp only [Set.mem_Ioi] at hs
      simp only [Set.mem_Iio]
      linarith
    have htr : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2))
        (Real.pi - Real.pi / 2) := by
      rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      exact hLpi
    have hcont : ContinuousWithinAt (fun s : ℝ => Real.pi - s) (Set.Ioi (Real.pi / 2))
        (Real.pi / 2) := by fun_prop
    have hcomp : ContinuousWithinAt (fun s : ℝ => -G w (Real.pi - s)) (Set.Ioi (Real.pi / 2))
        (Real.pi / 2) := (htr.comp hcont hmap).neg
    refine hcomp.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hQgt) ?_
    rw [hQpi, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, hpi w, neg_zero]
  have hjpi : ContinuousAt Q (Real.pi / 2) :=
    continuousAt_iff_continuous_left'_right'.mpr ⟨hjpiL, hjpiR⟩
  -- ## Assembly
  refine continuousOn_of_forall_continuousAt fun s hs => ?_
  rcases lt_trichotomy s 0 with h | rfl | h
  · exact hA.continuousAt (isOpen_Ioo.mem_nhds ⟨hs.1, h⟩)
  · exact hj0
  · rcases lt_trichotomy s (Real.pi / 2) with h2 | rfl | h2
    · exact hB.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)
    · exact hjpi
    · exact hC.continuousAt (isOpen_Ioo.mem_nhds ⟨h2, hs.2⟩)

end Work.FTS.EllSol.EllPkgAux.MollDzAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- `sKer ε` is smooth, hence its derivative `sKerd ε` is continuous. -/
theorem continuous_sKerd (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)
  simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using h.continuous_deriv_one

/-- The derivative kernel `sKerd ε = (sKer ε)'` vanishes outside the support `[-ε, ε]` of
`sKer ε`. -/
theorem sKerd_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε < |t|) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    show ∀ᶠ y in 𝓝 t, Work.FTS.EllSol.PkgK5.K5c.sKer ε y = 0
    rw [Metric.eventually_nhds_iff]
    refine ⟨(|t| - ε) / 2, by linarith, ?_⟩
    intro y hy
    have h1 : |y - t| < (|t| - ε) / 2 := by simpa [Real.dist_eq] using hy
    have h2 : ε < |y| := by
      have h3 : |t| ≤ |y| + |y - t| := by
        simpa [abs_sub_comm] using abs_sub_le y 0 (y - t)
      linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (le_of_lt h2)
  rw [Work.FTS.EllSol.EllPkgAux.sKerd, hev.deriv_eq, deriv_const]

theorem thMoll_hasDerivAt {Q : ℝ → ℝ} (hQ : ContinuousOn Q (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    {ε M θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    HasDerivAt (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s) θ := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  -- The interval `[a, b]` on which everything happens.
  set a : ℝ := θ - 5 / 8 with ha
  set b : ℝ := θ + 5 / 8 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have ha1 : -1 < a := by rw [ha]; linarith
  have hb1 : b < Real.pi / 2 + 1 := by rw [hb]; linarith
  have hsubIoc : Set.Ioc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsubuIoc : Set.uIoc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    rw [uIoc_of_le hab]; exact hsubIoc
  have hsubIcc : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hQ_Icc : ContinuousOn Q (Set.Icc a b) := hQ.mono hsubIcc
  have hQ_uIoc : ContinuousOn Q (Set.uIoc a b) := hQ.mono hsubuIoc
  have hsm : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
  have hder : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := continuous_sKerd ε
  -- The main differentiation under the integral sign, on the fixed interval `[a, b]`.
  have key : HasDerivAt
      (fun x : ℝ => ∫ t in a..b, Work.FTS.EllSol.PkgK5.K5c.sKer ε (x - t) * Q t)
      (∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - t) * Q t) θ := by
    have hF_int : IntervalIntegrable
        (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - t) * Q t) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      have h1 : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - t))
          (Set.Icc a b) :=
        (hsm.comp (continuous_const.sub continuous_id)).continuousOn
      exact h1.mul hQ_Icc
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - t) * Q t)
        (volume.restrict (Set.uIoc a b)) :=
      (((hder.comp (continuous_const.sub continuous_id)).continuousOn).mul hQ_uIoc).aestronglyMeasurable
        measurableSet_uIoc
    have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8),
        ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t‖ ≤ M * |Q t| := by
      refine Eventually.of_forall fun t _ x _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM (x - t)) (abs_nonneg _)
    have hbound_int : IntervalIntegrable (fun t : ℝ => M * |Q t|) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact hQ_Icc.abs.const_mul M
    have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8),
        HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - t) * Q t)
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t) x := by
      refine Eventually.of_forall fun t _ x _ => ?_
      have hderiv : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer ε)
          (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) (x - t)) (x - t) :=
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (x - t)).hasDerivAt
      have hcomp : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - t))
          (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) (x - t)) x := by
        have := hderiv.comp x ((hasDerivAt_id x).sub_const t)
        simpa [Function.comp_def] using this
      have := hcomp.mul_const (Q t)
      simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using this
    have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := a) (b := b)
      (bound := fun t : ℝ => M * |Q t|)
      (F := fun x t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (x - t) * Q t)
      (F' := fun x t : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x - t) * Q t)
      (x₀ := θ) (s := Set.Ioo (θ - 1 / 8) (θ + 1 / 8))
      (Ioo_mem_nhds (by linarith) (by linarith))
      (by
        refine Eventually.of_forall fun x => ?_
        exact (((hsm.comp (continuous_const.sub continuous_id)).continuousOn).mul hQ_uIoc).aestronglyMeasurable
          measurableSet_uIoc)
      hF_int hF'_meas hbound hbound_int hdiff
    exact hmain.2
  -- Transfer the function to the integral over `ℝ` …
  have hcong1 : (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      =ᶠ[𝓝 θ] (fun θ' : ℝ => ∫ s in a..b, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s) := by
    filter_upwards [Ioo_mem_nhds (show θ - 1 / 8 < θ by linarith)
      (show θ < θ + 1 / 8 by linarith)] with θ' hθ'
    have hzero : ∀ s : ℝ, s ∉ Set.Ioc a b →
        Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s = 0 := by
      intro s hs
      have hs' : s ≤ a ∨ b < s := by
        by_cases h : s ≤ a
        · exact Or.inl h
        · exact Or.inr (by
            by_contra hb'
            exact hs ⟨not_le.mp h, not_lt.mp hb'⟩)
      rcases hs' with h | h
      · have hle : ε ≤ |θ' - s| := by
          have h2 : (1 / 2 : ℝ) < θ' - s := by linarith [h, hθ'.1, ha]
          have h3 : θ' - s ≤ |θ' - s| := le_abs_self _
          linarith
        rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 hle, zero_mul]
      · have hle : ε ≤ |θ' - s| := by
          have h2 : (1 / 2 : ℝ) < s - θ' := by linarith [h, hθ'.2, hb]
          have h3 : s - θ' ≤ |θ' - s| := by rw [abs_sub_comm]; exact le_abs_self _
          linarith
        rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 hle, zero_mul]
    rw [intervalIntegral.integral_of_le hab]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- … and the value of the derivative.
  have hcong2 : (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s)
      = ∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    have hs' : s ≤ a ∨ b < s := by
      by_cases h : s ≤ a
      · exact Or.inl h
      · exact Or.inr (by
          by_contra hb'
          exact hs ⟨not_le.mp h, not_lt.mp hb'⟩)
    rcases hs' with h | h
    · have h1 : ε < θ - s := by linarith [h, ha, hε1]
      have h2 : ε < |θ - s| := lt_of_lt_of_le h1 (le_abs_self _)
      rw [sKerd_eq_zero_of_lt_abs hε0 h2, zero_mul]
    · have h1 : ε < s - θ := by linarith [h, hb, hε1]
      have h2 : ε < |θ - s| := by
        have h3 : s - θ ≤ |θ - s| := by rw [abs_sub_comm]; exact le_abs_self _
        linarith
      rw [sKerd_eq_zero_of_lt_abs hε0 h2, zero_mul]
  have hfin : HasDerivAt (fun θ' : ℝ => ∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Q s)
      (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Q s) θ :=
    (hcong1.hasDerivAt_iff).mpr key
  rwa [hcong2] at hfin

end Work.FTS.EllSol.EllPkgAux.MollDzAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl.limitBoundAux.pieces` — shared ingredients for `AeColl.limitBound` (part 1)

The vocabulary is that of `AeColl/Defs` (`Pcut`, `Dcut`, `Trcut`, `Acut`, `Vfull`,
`Uz = z∂_zu`, `Vz = z∂_z∂_θu`, `Az = z²∂_z²u`, `wt = w²`, `sigθ = sin(2θ)^{-η}`).

This module (part 1) contains

* continuity of `Az u`, `Uz u`, `∂_θθu` on the open quadrant, from `AeData.smooth`;
* the bridge "diagonal `IPMem`s + continuity ⟹ mixed `IPMem`" for the open class;
* the honest pairings of the four slots, in particular the mixed ones
  `IPMem (Uz u) (∂_θθu)` and `IPMem (Az u) (∂_θθu)`;
* a Cauchy–Schwarz bound with a bounded radial coefficient.

Part 2 (`...limitBoundAux.pieces2`) contains the identifications of `Pcut u n`, `Vfull u`,
`Dcut u n`, `Trcut u n` with `z`-integrals of `z`-only slice functions, together with
integrability/monotonicity facts.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Continuity on the open quadrant -/

theorem w2_zero : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
  simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]

theorem sigθ_eq : sigθ = Work.FTS.EllipticEst.AngSecond.sig := rfl

theorem wt_eq : wt = Work.FTS.EllipticEst.AngSecond.w2 := rfl

theorem continuousOn_w2_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

theorem continuousOn_sig_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  simpa only [Work.FTS.EllipticEst.AngSecond.sig] using hsin

theorem continuousOn_wt : ContinuousOn wt (Set.Ioi 0) := by
  have hfun : wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [wt, Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem SmoothOpen_of_AeData {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.FTS.EllipticEst.SmoothOpen u :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)

theorem continuousOn_rad2 {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Az u)) Work.FTS.EllipticEst.Q0 :=
  (continuousOn_fst.pow 2).mul ((h.pzIter 2).continuousOn)

theorem continuousOn_grad {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Uz u)) Work.FTS.EllipticEst.Q0 :=
  continuousOn_fst.mul (h.pz).continuousOn

theorem continuousOn_ang2 {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 u)) Work.FTS.EllipticEst.Q0 :=
  (h.pth.pth).continuousOn

/-! ## 2. The mixed `IPMem` from the diagonal ones, in the open class -/

/-- The mixed honesty `IPMem g h` follows from the two diagonal honesties once `g` and `h` are
continuous on the open quadrant. -/
theorem IPMem_of_diag_cont {g h : ℝ → ℝ → ℝ}
    (hgc : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hhc : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hgg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hhh : Work.FTS.EllipticEst.AngSecond.IPMem h h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h := by
  have hprod : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((hgc.mul hhc).mul continuousOn_w2_Q0).mul continuousOn_sig_Q0
  refine Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm hgg hhh ?_ ?_
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hzero : (fun θ : ℝ => g 0 θ * h 0 θ * Work.FTS.EllipticEst.AngSecond.w2 0
          * Work.FTS.EllipticEst.AngSecond.sig θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [w2_zero]; ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hprod hzpos
  · exact Work.Spaces.aesm_of_continuousOn_Qd _ hprod

/-! ## 3. The honest pairings of the slots -/

theorem IPMem_grad_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Uz u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hU

theorem IPMem_ang2_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 h)

theorem IPMem_rad2_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Az u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 h)

theorem IPMem_grad_ang2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Work.Spaces.pthIter 2 u) :=
  IPMem_of_diag_cont (continuousOn_grad (SmoothOpen_of_AeData h))
    (continuousOn_ang2 (SmoothOpen_of_AeData h)) (IPMem_grad_self h hU) (IPMem_ang2_self h)

theorem IPMem_rad2_ang2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u) :=
  IPMem_of_diag_cont (continuousOn_rad2 (SmoothOpen_of_AeData h))
    (continuousOn_ang2 (SmoothOpen_of_AeData h)) (IPMem_rad2_self h) (IPMem_ang2_self h)

/-! ## 4. Cauchy–Schwarz with a bounded radial coefficient -/


end Work.FTS.EllipticEst.AeColl
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSin_layer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.L12Aux.L12_moment_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.L12Aux

set_option linter.unusedSimpArgs false

/-! ## Elementary angular facts -/

/-- The angular weight `sinθcos²θ` is continuous on the closed angular interval. -/
theorem continuousOn_sinCos2 :
    ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (π / 2)) := by
  unfold Work.Elliptic.sinCos2
  fun_prop


/-! ## Continuity of `F_*(F)` for the data of `EllHyp` -/


/-! ## The derivative of `L₁₂(F)` -/


/-! ## The moment of `D_zΨ` and the derivatives of the moment -/

/-- The derivative of the angular moment, evaluated by differentiating under the integral. -/
theorem hasDerivAt_Fstar (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Elliptic.Fstar Ψ z')
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) z :=
  Work.Elliptic.hasDerivAt_integral_Iθ Ψ Work.Elliptic.sinCos2 hsm continuousOn_sinCos2
    (by linarith : (-1 : ℝ) < z)

/-- `D_z = z ∂_z` pulls out of the angular integral: `F_*(D_zΨ)(z) = z·F_*(Ψ)'(z)`. -/
theorem Fstar_DzIter_one_eq (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z := by
  have hd : deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ :=
    (hasDerivAt_Fstar Ψ hsm hz).deriv
  have key : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = ∫ θ in Work.Spaces.Iθ, z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    rw [Work.Elliptic.Fstar]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    show (Work.Spaces.DzIter 1 Ψ z θ) * Work.Elliptic.sinCos2 θ
      = z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  rw [key, MeasureTheory.integral_const_mul, hd]

/-- The derivative of `z ↦ F_*(Ψ)'(z)`, again by differentiating under the integral. -/
theorem hasDerivAt_deriv_Fstar (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (deriv (fun z' => Work.Elliptic.Fstar Ψ z'))
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) z := by
  have hsm1 : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) := hsm.pz
  have h := Work.Elliptic.hasDerivAt_integral_Iθ (Work.Spaces.pz Ψ) Work.Elliptic.sinCos2 hsm1
    continuousOn_sinCos2 (by linarith : (-1 : ℝ) < z)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
  have hw' : (-1 : ℝ) < w := by
    simp only [Set.mem_Ioi] at hw; linarith
  exact (Work.Elliptic.hasDerivAt_integral_Iθ Ψ Work.Elliptic.sinCos2 hsm continuousOn_sinCos2
    hw').deriv

/-! ## The derivative of the right-hand side -/


/-! ## `L₁₂(F) → 0` at infinity -/


/-! ## The squared `L²`-mass of the right-hand side -/







/-! ## Integrability of `r ↦ F_*(F)(r)/r`

The improper integral `L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(r)/r dr` converges because
`r ↦ F_*(F)(r)/r ∈ L¹(0,∞)`.  This is proved exactly as in the sibling
`Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp`, but with a *self-contained* proof of
the radial `L²`-bound `(r·w(r))⁻¹² ∈ L¹` that the sibling borrows from
`Work.FTS.EllipticEst.Cert.HasFiniteIntegralWInvSq`, still unproved there); the argument is
repeated here so that this module rests only on `[propext, Classical.choice, Quot.sound]`. -/



/-! ## The moment identity -/


end Work.FTS.EllipticEst.Cert.L12Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gbar_le_open_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The imported auxiliary facts (thin adapters)

The chain rule and the integration by parts for the Hardy operator are proved in the sibling
modules `Work.FTS.EllipticEst.GbarSin` and `Work.FTS.EllipticEst.Cert.GbarSin`; the two
lemmas below are the copies of those statements in this namespace.  The weighted Hardy
inequality is proved in `Work.FTS.EllipticEst.Gbar_hardy_le` (see `gbar_HarOp_weighted_integral_le`),
and the a.e. strong measurability of `HarOp (bet α) (Uj F j)` needed to apply it is
`gbar_HarOp_aesm_Uj` below (continuity of the primitive of a locally integrable function). -/

/-- The chain rule for the angular moment (sibling module, same statement). -/
theorem FstarDzIter_chain_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r :=
  Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz

/-- Integration by parts for `HarOp` from the chain relation (sibling module, same statement). -/
theorem HarOp_eq_sub_of_chain (β : ℝ) (hβ : 1 < β) {u v : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : IntegrableOn (fun r : ℝ => v r / r) (Set.Ioo 0 z))
    (hchain : ∀ s ∈ Set.Ioo (0 : ℝ) z, u z - u s = ∫ r in s..z, v r / r) :
    HarOp β v z = u z - β * HarOp β u z :=
  Work.FTS.EllipticEst.Cert.GbarSin.HarOp_eq_sub_of_chain β hβ hz hint hchain

/-- The weighted Hardy inequality, with the a.e. strong measurability of `HarOp β f` supplied
by the caller (here: `gbar_HarOp_aesm_Uj`). -/
theorem HarOp_weighted_integral_le (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hfw : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2) (Set.Ioi 0))
    (hmeas : AEStronglyMeasurable (HarOp β f) (volume.restrict (Set.Ioi 0))) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 :=
  gbar_HarOp_weighted_integral_le β hβ f hf hfw hmeas








/-! ## The angular weight is continuous -/

theorem gbar_continuousOn_sinCos2 :
    ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (π / 2)) := by
  unfold Work.Elliptic.sinCos2; fun_prop

/-! ## The angular constants -/

/-- A uniform (in `α ∈ (0,1]`) bound for `(D_θ^i sin 2θ)² sin(2θ)^{-γ}`. -/
noncomputable def gbar_angC (i : ℕ) : ℝ := Classical.choose (sinIter_weight_bound i)

theorem gbar_angC_nonneg (i : ℕ) : 0 ≤ gbar_angC i :=
  (Classical.choose_spec (sinIter_weight_bound i)).1

theorem gbar_angC_bound (i : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ gbar_angC i :=
  (Classical.choose_spec (sinIter_weight_bound i)).2 α hα hα1 θ hθ

/-- The angular constant of the estimate of order `k`. -/
noncomputable def gbar_Kang (k : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i

theorem gbar_Kang_pos (k : ℕ) : 0 < gbar_Kang k := by
  have h : 0 ≤ ∑ i ∈ Finset.range (k + 1), gbar_angC i :=
    Finset.sum_nonneg fun i _ => gbar_angC_nonneg i
  simp only [gbar_Kang]
  linarith

/-! ## Elementary angular facts -/

theorem gbar_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- `sin(2θ)² / (sin(2θ)^{η/2})² ≤ 1` on the angular interval. -/
theorem gbar_sin_two_ratio_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · rw [← hs]
    simp
  · have hpow : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hnum : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [hpow, hnum, ← Real.rpow_sub hs (y := (2 : ℝ)) (z := Work.Spaces.eta)]
    exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by
      have h := Work.Spaces.eta_lt_one; linarith)

/-- The first-sum term of the target `H^k`-integrand is bounded by `A² w²`. -/
theorem gbar_sin_two_term_le (A w : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (A * Real.sin (2 * θ) * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ A ^ 2 * w ^ 2 := by
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · rw [← hs, mul_zero, zero_mul, show (0 : ℝ) ^ 2 = 0 by norm_num]
    exact mul_nonneg (sq_nonneg A) (sq_nonneg w)
  · have hratio := gbar_sin_two_ratio_sq_le_one hθ
    have he : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hs _)
    calc (A * Real.sin (2 * θ) * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = A ^ 2 * w ^ 2 *
            ((Real.sin (2 * θ)) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by
          simp only [mul_pow, div_pow]
          ring
      _ ≤ A ^ 2 * w ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (sq_nonneg A) (sq_nonneg w))
      _ = A ^ 2 * w ^ 2 := by ring

/-- The mixed term of the target `H^k`-integrand is bounded by `w² · angC i · A²`. -/
theorem gbar_sinIter_Wt_term_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) (A z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (A * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * gbar_angC i * A ^ 2 := by
  have hb := gbar_angC_bound i α hα hα1 hθ
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · have hW : Work.Spaces.Wt α z θ = 0 := by
      rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hs,
        Real.zero_rpow (show -(Work.Spaces.gam α / 2) ≠ 0 by
          have hg := Work.Spaces.gam_pos hα
          intro hc
          linarith [neg_eq_zero.mp hc]),
        mul_zero]
    rw [hW, mul_zero, show (0 : ℝ) ^ 2 = 0 by norm_num]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (gbar_angC_nonneg i)) (sq_nonneg A)
  · have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    calc (A * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * A ^ 2 *
            ((sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hpow]
          ring
      _ ≤ (Work.Spaces.w z) ^ 2 * A ^ 2 * gbar_angC i :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.w z) ^ 2 * gbar_angC i * A ^ 2 := by ring

/-! ## The factorisations of the `D`-derivatives of the target -/

theorem gbar_DzIter_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = rDzIter i (Work.Elliptic.Gbar α F) z * Real.sin (2 * θ) :=
  DzIter_mul_of_radial i (Work.Elliptic.Gbar α F) (fun θ => Real.sin (2 * θ)) z θ

theorem gbar_DthIter_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      = fun z θ => Work.Elliptic.Gbar α F z * sinIter i θ := by
  funext z θ
  rw [DthIter_mul_of_angular i (Work.Elliptic.Gbar α F) (fun θ => Real.sin (2 * θ)) z θ]
  rfl

theorem gbar_mixed_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = rDzIter j (Work.Elliptic.Gbar α F) z * sinIter i θ := by
  simp only [Work.Spaces.mixed]
  rw [gbar_DthIter_target_eq α F i]
  exact DzIter_mul_of_radial j (Work.Elliptic.Gbar α F) (fun θ => sinIter i θ) z θ

/-! ## The pointwise comparison of the `H^k`-integrands -/

theorem gbar_HkIntegrand_target_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      ≤ gbar_Kang k * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ j ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [gbar_DzIter_target_eq α F i z θ]
    calc (rDzIter i (Work.Elliptic.Gbar α F) z * Real.sin (2 * θ)
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (rDzIter i (Work.Elliptic.Gbar α F) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          gbar_sin_two_term_le _ _ hθ
      _ = (Work.Spaces.w z) ^ 2 * (rDzIter i (Work.Elliptic.Gbar α F) z) ^ 2 := by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * gbar_angC i * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, gbar_mixed_target_eq α F j i z θ]
            exact gbar_sinIter_Wt_term_le α hα hα1 i _ z hθ
          · rw [if_neg hc]
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (gbar_angC_nonneg i)) (sq_nonneg _)
      _ = (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
            (∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
          calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  (Work.Spaces.w z) ^ 2 * gbar_angC i *
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
              = ∑ i ∈ Finset.range (k + 1), ((Work.Spaces.w z) ^ 2 * gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
            _ = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.w z) ^ 2 * gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                rw [Finset.sum_mul]
            _ = (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                have e1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.w z) ^ 2 * gbar_angC i)
                    = (Work.Spaces.w z) ^ 2 * ∑ i ∈ Finset.range (k + 1), gbar_angC i :=
                  (Finset.mul_sum _ _ _).symm
                have e2 : (∑ j ∈ Finset.range (k + 1),
                      (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
                    = (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
                      (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 :=
                  (Finset.mul_sum _ _ _).symm
                rw [e1, e2]
                ring
  rw [Work.Spaces.HkIntegrand]
  have htot : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
    calc _ ≤ (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
          + (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
            (∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) :=
          add_le_add h1 h2
      _ = (1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by ring
  refine htot.trans (le_of_eq ?_)
  have e2 : (∑ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := (Finset.mul_sum _ _ _).symm
  rw [e2]
  simp only [gbar_Kang]
  ring

/-! ## The angular moment `U_j` and the weighted slice `A_j` -/

/-- The angular moment `U_j = F_*(D_z^j F)` of the `j`-th `D_z`-iterate of the source. -/
noncomputable def Uj (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z

/-- The `j`-th weighted `L²`-slice `A_j = ∫_θ (D_z^j F · w/sin(2θ)^{η/2})²`. -/
noncomputable def Aj (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

@[simp] theorem Uj_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Uj F j z = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z := rfl

@[simp] theorem Aj_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Aj F j z = ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

/-- The `j`-th summand of the `H^k`-integrand is integrable on the angular slice and is
dominated by the whole `H^k`-integrand. -/
theorem Aj_le_HkIntegrand_integral (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Aj F j z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
  rw [Aj_apply]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z hz) (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F z θ j hj)

/-- The `z ↦ A_j(z)` is a.e. strongly measurable. -/
theorem Aj_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (Aj F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry fun z θ : ℝ =>
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
    (hF.continuousOn_summand j).pow 2
  have h := aestronglyMeasurable_integral_Itheta_Q0
    (fun z θ : ℝ => (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    hg (fun _ : ℝ => (1 : ℝ)) continuousOn_const
  change AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) _
  simpa only [mul_one] using h

/-- The angular moment `z ↦ U_j(z)` is a.e. strongly measurable. -/
theorem Uj_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (Uj F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry (Work.Spaces.DzIter j F)) Q0 :=
    (hF.DzIter j).continuousOn
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F) hg
    Work.Elliptic.sinCos2 gbar_continuousOn_sinCos2
  change AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ) _
  simpa only [mul_one] using h

/-- The slice functional `A_j` is integrable on `(0,∞)`, with integral bounded by `HkSq`. -/
theorem Aj_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (Aj F j) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, Aj F j z) ≤ Work.Spaces.HkSq α k F := by
  have hmaj : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  refine ⟨?_, ?_⟩
  · refine hmaj.mono' (Aj_aesm α k F hF j) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ‖Aj F j z‖ ≤ _
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    rw [Aj_apply, Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact Aj_le_HkIntegrand_integral α k F hmem j hj hzI
  · have h1 : (∫ z in Set.Ioi 0, Aj F j z)
        ≤ ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
        integral_nonneg fun θ => sq_nonneg _) hmaj ?_
      show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), _
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz =>
        Aj_le_HkIntegrand_integral α k F hmem j hj (by
          rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz))
    refine h1.trans (le_of_eq ?_)
    rw [Work.Spaces.HkSq, restrict_Ioi_eq_restrict_Iz]

/-! ## Preliminaries: square-root bounds and integrability -/

/-- For a nonnegative integrable function on a finite-measure set, its square root is
integrable. -/
theorem integrableOn_sqrt {A : ℝ → ℝ} {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hS : volume S ≠ ⊤) (hA : IntegrableOn A S) (hAnn : ∀ r ∈ S, 0 ≤ A r) :
    IntegrableOn (fun r => Real.sqrt (A r)) S := by
  refine Integrable.mono' ((integrableOn_const (s := S) (C := (1 : ℝ)) hS).add hA)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable) ?_
  · show ∀ᵐ r ∂(volume.restrict S), ‖Real.sqrt (A r)‖ ≤ (1 : ℝ) + A r
    rw [ae_restrict_iff' hSmeas]
    refine Eventually.of_forall fun r hr => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_iff.mpr ⟨by linarith [hAnn r hr],
      by nlinarith [hAnn r hr, sq_nonneg (A r)]⟩

/-- The Cauchy–Schwarz bound `|U_j z| ≤ √(π/2)·√(A_j z)/w(z)`. -/
theorem Uj_sqrt_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    |Uj F j z| ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := by
  have hsq : (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * Aj F j z :=
    FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
  have hA0 : 0 ≤ Aj F j z := integral_nonneg fun θ => sq_nonneg _
  have hw0 : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hdiv : (Uj F j z) ^ 2 ≤ ((π / 2) * Aj F j z) / (Work.Spaces.w z) ^ 2 :=
    (le_div_iff₀ (pow_pos hw0 2)).mpr hsq
  have hTnn : 0 ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := by positivity
  have hTsq : (Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2
      = ((π / 2) * Aj F j z) / (Work.Spaces.w z) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hA0]
  have hU2 : (Uj F j z) ^ 2 ≤ (Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2 := by
    rw [hTsq]; exact hdiv
  calc |Uj F j z| = Real.sqrt ((Uj F j z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2) :=
        Real.sqrt_le_sqrt hU2
    _ = Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := Real.sqrt_sq hTnn

/-- The Cauchy–Schwarz bound `(U_j z)² w(z)² ≤ (π/2) A_j(z)`, integrated. -/
theorem Uj_sq_mul_w_integrable (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2)
        ≤ (π / 2) * Work.Spaces.HkSq α k F := by
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2 ≤ (π / 2) *
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    have h1 : (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * Aj F j z :=
      FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
    have h2 := Aj_le_HkIntegrand_integral α k F hmem j hj hzI
    calc (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2
        = (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ (π / 2) * Aj F j z := h1
      _ ≤ (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
    rw [hfun]
    refine ContinuousOn.pow ?_ 2
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hz)))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) (volume.restrict (Set.Ioi 0)) :=
    (hw2.aestronglyMeasurable measurableSet_Ioi).mul ((Uj_aesm α k F hF j).pow 2)
  have hmaj : IntegrableOn (fun z => (π / 2) *
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)) (Set.Ioi 0) :=
    hB.const_mul _
  refine ⟨hmaj.mono' haesm ?_, ?_⟩
  · show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ‖(Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2‖ ≤ _
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpoint z hz
  · have hInt : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2)
        ≤ ∫ z in Set.Ioi 0, (π / 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hmaj ?_
      show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), _
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz => hpoint z hz
    refine hInt.trans (le_of_eq ?_)
    rw [integral_const_mul, Work.Spaces.HkSq, restrict_Ioi_eq_restrict_Iz]

/-! ## Continuity of the angular moments -/

theorem Uj_continuousOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (Uj F j) (Set.Ioi 0) := by
  refine continuousOn_of_primitive_of_sqrt_bound (u := Uj F j) (v := Uj F (j + 1))
    (A := Aj F (j + 1)) (Aj_integrableOn α k F hF hmem (j + 1) hj).1 ?_ ?_
  · intro r hr
    exact Uj_sqrt_bound α k F hF hmem (j + 1) hj hr
  · intro s z hs hsz
    exact FstarDzIter_chain_open α k F hF hmem j hj hs hsz


/-! ## Integrability of the `D_z^j Ḡ` and the radial identity -/

/-- The integral of a constant over `Iθ`. -/
theorem gbar_integral_Iθ_const (c : ℝ) :
    (∫ θ in Work.Spaces.Iθ, c) = (π / 2) * c := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  rw [hvol]

/-- A finite sum of integrable functions is integrable. -/
theorem gbar_integrable_finsetSum (μ : Measure ℝ) (s : Finset ℕ) (f : ℕ → ℝ → ℝ)
    (h : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_zero (α := ℝ) (μ := μ))
  | insert a s ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s, f i z)
          = (fun z => f a z + ∑ i ∈ s, f i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `s^(β-1)·U_j` is interval integrable on `[0,z]`. -/
theorem intervalIntegrable_rpow_Uj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k)
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s) volume 0 z := by
  have hβ5 : 5 ≤ bet α := by rw [bet, le_div_iff₀ hα]; linarith
  have hβp : 0 < bet α := by linarith
  have hsqrt : IntegrableOn (fun s => Real.sqrt (Aj F j s)) (Set.Ioo 0 z) :=
    integrableOn_sqrt measurableSet_Ioo (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      ((Aj_integrableOn α k F hF hmem j hj).1.mono_set (fun r hr => hr.1))
      (fun r _ => integral_nonneg fun θ => sq_nonneg _)
  have hAjnn : ∀ r ∈ Set.Ioo (0:ℝ) z, 0 ≤ Aj F j r :=
    fun r _ => integral_nonneg fun θ => sq_nonneg _
  have hbd : ∀ s ∈ Set.Ioc (0:ℝ) z,
      ‖s ^ (bet α - 1) * Uj F j s‖
        ≤ Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1) * Real.sqrt (Aj F j s) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hU := Uj_sqrt_bound α k F hF hmem j hj hs0
    have hnn : 0 ≤ s ^ (bet α - 1) := Real.rpow_nonneg hs0.le _
    have hdiv : s ^ (bet α + 1) / (1 + s) ^ 2 ≤ (1 + z) ^ (bet α + 1) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + s) ^ 2)]
      calc s ^ (bet α + 1) ≤ (1 + z) ^ (bet α + 1) :=
            Real.rpow_le_rpow hs0.le (by linarith [hs.2]) (by linarith : (0:ℝ) ≤ bet α + 1)
        _ ≤ (1 + z) ^ (bet α + 1) * (1 + s) ^ 2 :=
            le_mul_of_one_le_right (Real.rpow_nonneg (by linarith [hs.2]) _)
              (by nlinarith [hs0])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    have hw : Work.Spaces.w s = (1 + s) ^ 2 / s ^ 2 := rfl
    have hstep : s ^ (bet α - 1) * (Real.sqrt (π / 2) * Real.sqrt (Aj F j s)
        / Work.Spaces.w s)
        = Real.sqrt (π / 2) * Real.sqrt (Aj F j s)
          * (s ^ (bet α + 1) / (1 + s) ^ 2) := by
      rw [hw]
      have hsp : s ^ (bet α - 1) * (s ^ (2:ℝ)) = s ^ (bet α + 1) := by
        rw [← Real.rpow_add hs0]
        congr 1
        ring
      field_simp
      rw [show s ^ 2 = s ^ (2:ℝ) from (Real.rpow_natCast s 2).symm]
      calc s ^ (bet α - 1) * Real.sqrt (Aj F j s) * s ^ (2:ℝ)
          = Real.sqrt (Aj F j s) * (s ^ (bet α - 1) * s ^ (2:ℝ)) := by ring
        _ = Real.sqrt (Aj F j s) * s ^ (bet α + 1) := by rw [hsp]
    calc s ^ (bet α - 1) * |Uj F j s|
        ≤ s ^ (bet α - 1) * (Real.sqrt (π / 2) * Real.sqrt (Aj F j s) / Work.Spaces.w s) :=
          mul_le_mul_of_nonneg_left hU hnn
      _ = Real.sqrt (π / 2) * Real.sqrt (Aj F j s) * (s ^ (bet α + 1) / (1 + s) ^ 2) := hstep
      _ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j s) * (1 + z) ^ (bet α + 1) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1) * Real.sqrt (Aj F j s) := by ring
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hcont : ContinuousOn (fun s : ℝ => s ^ (bet α - 1)) (Set.Ioc 0 z) :=
      (Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ bet α - 1)).continuousOn
    have h1 : AEStronglyMeasurable (Uj F j) (volume.restrict (Set.Ioc (0:ℝ) z)) :=
      (Uj_aesm α k F hF j).mono_measure (Measure.restrict_mono (fun s hs => hs.1) le_rfl)
    exact ((hcont.aestronglyMeasurable measurableSet_Ioc).mul h1)
  have hsqrt' : IntegrableOn (fun s => Real.sqrt (Aj F j s)) (Set.Ioc 0 z) :=
    integrableOn_sqrt measurableSet_Ioc (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      ((Aj_integrableOn α k F hF hmem j hj).1.mono_set (fun r hr => hr.1))
      (fun r _ => integral_nonneg fun θ => sq_nonneg _)
  have hint : IntegrableOn (fun s => Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1)
      * Real.sqrt (Aj F j s)) (Set.Ioc 0 z) :=
    hsqrt'.const_mul _
  rw [IntervalIntegrable]
  refine ⟨hint.mono' haesm ?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => hbd s hs
  have hemp : Set.Ioc z 0 = ∅ := by
    rw [Set.Ioc_eq_empty_iff]
    exact not_lt.mpr hz.le
  rw [hemp]
  exact integrableOn_empty

/-! ## The exact radial identity and the per-order bound -/

/-- **The radial identity**: `D_z^j Ḡ(α,F) = -(3/(4α))·HarOp(5/α)(U_j)` on `(0,∞)`. -/
theorem rDzIter_Gbar_eq_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j ≤ k → Set.EqOn (rDzIter j (Work.Elliptic.Gbar α F))
      (fun z => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  intro j
  induction j with
  | zero =>
      intro hj z hz
      have h := Gbar_eq_HarOp α (ne_of_gt hα) F z
      have hfun : (Uj F 0) = (fun s : ℝ => Work.Elliptic.Fstar F s) := by
        funext s; simp
      simpa only [rDzIter_zero, hfun, Work.Spaces.DzIter_zero] using h
  | succ j ih =>
      intro hj z hz
      have hjk : j ≤ k := by omega
      have hj1k : j + 1 ≤ k := hj
      have hidj : Set.EqOn (rDzIter j (Work.Elliptic.Gbar α F))
          (fun w => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) w) (Set.Ioi 0) := ih hjk
      have hev : rDzIter j (Work.Elliptic.Gbar α F) =ᶠ[𝓝 z]
          (fun w => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) w) :=
        (Filter.eventually_mem_set.mpr (Ioi_mem_nhds hz)).mono (fun w hw => hidj hw)
      rw [rDzIter_succ, rDz, Filter.EventuallyEq.deriv_eq hev, deriv_const_mul_field]
      have hβp : 0 < bet α := by rw [bet]; positivity
      have hβ1 : 1 < bet α := by rw [bet, lt_div_iff₀ hα]; linarith
      have hcont : ContinuousOn (Uj F j) (Set.Ioi 0) := Uj_continuousOn α k F hF hmem j hj1k
      have hint : IntervalIntegrable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s) volume 0 z :=
        intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hjk hz
      have hD6 := rDz_HarOp_of_continuousAt (bet α) hβp hz hcont hint
      rw [rDz] at hD6
      have hchainD4 : ∀ s ∈ Set.Ioo (0 : ℝ) z,
          Uj F j z - Uj F j s = ∫ r in s..z, Uj F (j + 1) r / r :=
        fun s hs => FstarDzIter_chain_open α k F hF hmem j hj1k hs.1 hs.2.le
      have hintD4 : IntegrableOn (fun r : ℝ => Uj F (j + 1) r / r) (Set.Ioo 0 z) := by
        have hsqrt : IntegrableOn (fun r => Real.sqrt (Aj F (j + 1) r)) (Set.Ioo 0 z) :=
          integrableOn_sqrt measurableSet_Ioo
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
            ((Aj_integrableOn α k F hF hmem (j + 1) hj1k).1.mono_set (fun r hr => hr.1))
            (fun r _ => integral_nonneg fun θ => sq_nonneg _)
        refine (hsqrt.const_mul (Real.sqrt (π / 2))).mono' ?_ ?_
        · have hU : AEStronglyMeasurable (Uj F (j + 1))
              (volume.restrict (Set.Ioo (0:ℝ) z)) :=
            (Uj_aesm α k F hF (j + 1)).mono_measure
              (Measure.restrict_mono (fun s hs => hs.1) le_rfl)
          have hInv : AEStronglyMeasurable (fun r : ℝ => r⁻¹)
              (volume.restrict (Set.Ioo (0:ℝ) z)) :=
            ((continuousOn_id.inv₀ (fun r hr => ne_of_gt hr.1)).aestronglyMeasurable
              measurableSet_Ioo)
          exact hU.mul hInv
        · show ∀ᵐ r ∂(volume.restrict (Set.Ioo (0:ℝ) z)),
            ‖Uj F (j + 1) r / r‖ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r)
          rw [ae_restrict_iff' measurableSet_Ioo]
          refine Eventually.of_forall fun r hr => ?_
          have hr0 : 0 < r := hr.1
          have hU := Uj_sqrt_bound α k F hF hmem (j + 1) hj1k hr0
          have hAw : 1 ≤ r * Work.Spaces.w r := by
            rw [Work.Spaces.w]
            field_simp
            nlinarith [hr0, sq_nonneg r, pow_pos hr0 3]
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0, div_eq_mul_inv]
          calc |Uj F (j + 1) r| * r⁻¹
              ≤ (Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) / Work.Spaces.w r) * r⁻¹ :=
                mul_le_mul_of_nonneg_right hU (by positivity)
            _ = Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) * (r * Work.Spaces.w r)⁻¹ := by
                ring
            _ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) * 1 := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact inv_le_one_of_one_le₀ hAw
            _ = Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) := by ring
      have hD4 := HarOp_eq_sub_of_chain (bet α) hβ1 hz hintD4 hchainD4
      have hgoal : z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * (-bet α * HarOp (bet α) (Uj F j) z + Uj F j z) := by
        rw [show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
            = -(3 / (4 * α)) * (z * deriv (HarOp (bet α) (Uj F j)) z) by ring, hD6]
      show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * HarOp (bet α) (Uj F (j + 1)) z
      rw [hgoal, hD4]
      ring

/-- The primitive `z ↦ ∫_0^z f` of a function that is interval integrable on `[0,z]` for every
`z > 0` is continuous on `(0,∞)`. -/
theorem gbar_continuousOn_primitive_Ioi {f : ℝ → ℝ}
    (hf : ∀ z : ℝ, 0 < z → IntervalIntegrable f volume 0 z) :
    ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, f s) (Set.Ioi 0) := by
  have hcont2 : ContinuousOn (fun z => ∫ s in Set.Ioc (0 : ℝ) z, f s) (Set.Ioi 0) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h2x : (0 : ℝ) < 2 * x := by linarith
    have hIcc : IntegrableOn f (Set.Icc 0 (2 * x)) :=
      ((hf (2 * x) h2x).1).congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (a := (0:ℝ)) (b := 2 * x)).symm
    have hcont := intervalIntegral.continuousOn_primitive hIcc
    exact (hcont x ⟨hx'.le, by linarith⟩).continuousAt
      (Icc_mem_nhds hx' (by linarith)) |>.continuousWithinAt
  refine hcont2.congr ?_
  intro y hy
  exact intervalIntegral.integral_of_le hy.le

/-- `HarOp (bet α) (Uj F j)` is a.e. strongly measurable: it is `z ↦ z^{-β}` times the primitive
of `s ↦ s^{β-1} U_j(s)`, which is interval integrable on `[0,z]` for every `z > 0`
(`intervalIntegrable_rpow_Uj`), and the primitive of such a function is continuous
(`Cert.GbarLayer.continuousOn_primitive_Ioi`). -/
theorem gbar_HarOp_aesm_Uj (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : j ≤ k) :
    AEStronglyMeasurable (HarOp (bet α) (Uj F j)) (volume.restrict (Set.Ioi 0)) := by
  have hint : ∀ z : ℝ, 0 < z →
      IntervalIntegrable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s) volume 0 z :=
    fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz
  have hcont : ContinuousOn (fun z : ℝ => ∫ s in (0 : ℝ)..z,
      s ^ (bet α - 1) * Uj F j s) (Set.Ioi 0) :=
    gbar_continuousOn_primitive_Ioi hint
  have hfac : ContinuousOn (fun z : ℝ => z ^ (-(bet α))) (Set.Ioi 0) :=
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx))
  have hfun : HarOp (bet α) (Uj F j) = fun z : ℝ => z ^ (-(bet α)) *
      ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s := rfl
  rw [hfun]
  exact (hfac.aestronglyMeasurable measurableSet_Ioi).mul
    (hcont.aestronglyMeasurable measurableSet_Ioi)

/-- **The weighted `L²` bound of `D_z^j Ḡ`**, with constant `(9/4)(π/2)` independent of `α`. -/
theorem Gbar_rDzIter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
          ≤ (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
  have hβ5 : 5 ≤ bet α := by rw [bet, le_div_iff₀ hα]; linarith
  have hU2 : IntegrableOn (fun z => (Uj F j z) ^ 2) (Set.Ioi 0) := by
    refine (Uj_sq_mul_w_integrable α k F hF hmem j hj).1.mono' ((Uj_aesm α k F hF j).pow 2) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ‖(Uj F j z) ^ 2‖ ≤ (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hw1 : 1 ≤ Work.Spaces.w z := by
      have hz2 : (0:ℝ) < z ^ 2 := pow_pos (Set.mem_Ioi.mp hz) 2
      rw [Work.Spaces.w, le_div_iff₀ hz2]
      nlinarith [Set.mem_Ioi.mp hz]
    have hw0 : 0 ≤ Work.Spaces.w z := by linarith [hw1]
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [hw1, hw0]
    nlinarith [hw2, sq_nonneg (Uj F j z)]
  obtain ⟨hH_int, hH_le⟩ := HarOp_weighted_integral_le (bet α) hβ5 (Uj F j) hU2
    (Uj_sq_mul_w_integrable α k F hF hmem j hj).1
    (gbar_HarOp_aesm_Uj α k F hF hmem hα hα1 j hj)
  have hid := rDzIter_Gbar_eq_open α hα hα1 k F hF hmem j hj
  have hae : (fun z => (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z => (Work.Spaces.w z) ^ 2 *
        ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz => by rw [hid hz]
  have hconst : ((-(3 / (4 * α))) ^ 2) * (100 / (bet α) ^ 2) = 9 / 4 := by
    rw [bet]; field_simp; ring
  have hg_int : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    refine Integrable.congr (hH_int.const_mul ((-(3 / (4 * α))) ^ 2)) ?_
    filter_upwards with z
    ring
  have hkey : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      ≤ (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
    calc (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
            ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2 := integral_congr_ae hae
      _ = ((-(3 / (4 * α))) ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
            (HarOp (bet α) (Uj F j) z) ^ 2 := by
          rw [show (fun z => (Work.Spaces.w z) ^ 2 *
                ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2)
              = (fun z => ((-(3 / (4 * α))) ^ 2) *
                ((Work.Spaces.w z) ^ 2 * (HarOp (bet α) (Uj F j) z) ^ 2)) from
            funext fun z => by ring,
            integral_const_mul]
      _ ≤ ((-(3 / (4 * α))) ^ 2) * ((100 / (bet α) ^ 2) *
            ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) :=
          mul_le_mul_of_nonneg_left hH_le (sq_nonneg _)
      _ ≤ ((-(3 / (4 * α))) ^ 2) * ((100 / (bet α) ^ 2) *
            ((π / 2) * Work.Spaces.HkSq α k F)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (Uj_sq_mul_w_integrable α k F hF hmem j hj).2
      _ = (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
          rw [← mul_assoc, hconst]
          ring
  refine ⟨?_, ?_⟩
  · show Integrable _ (volume.restrict Work.Spaces.Iz)
    rw [← restrict_Ioi_eq_restrict_Iz]
    exact hg_int.congr hae.symm
  · have hset : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
      rw [restrict_Ioi_eq_restrict_Iz]
    rw [hset]
    exact hkey

/-! ## The `H^k`-square estimate and the main theorem -/

theorem Gbar_HkSq_le_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      ≤ (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) * Work.Spaces.HkSq α k F := by
  have hpc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
        ≤ gbar_Kang k * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 :=
    fun z hz θ hθ => gbar_HkIntegrand_target_le α hα hα1 k F z θ hz hθ
  have hmeas : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ)
        ≤ (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
    intro z hz
    have hstep : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k _ z θ)
        (integrableOn_const hmeas)
        (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
          (hpc z hz θ hθ).trans (le_of_eq (mul_assoc _ _ _)))
    exact hstep.trans (le_of_eq (gbar_integral_Iθ_const _))
  have hsum : IntegrableOn (fun z => ∑ j ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) Work.Spaces.Iz :=
    gbar_integrable_finsetSum (volume.restrict Work.Spaces.Iz) (Finset.range (k + 1))
      (fun j z => (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      (fun j hj => (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
  have hIntmaj : IntegrableOn (fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
      ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)))
      Work.Spaces.Iz := by
    have heq : (fun z => ∑ j ∈ Finset.range (k + 1), ((π / 2) * gbar_Kang k) *
          ((Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))
        = (fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))) := by
      funext z
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← heq]
    refine gbar_integrable_finsetSum (volume.restrict Work.Spaces.Iz) (Finset.range (k + 1))
      (fun j z => ((π / 2) * gbar_Kang k) *
        ((Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) fun j hj => ?_
    exact (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1.const_mul _
  calc Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, ((π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ) hIntmaj
          (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hslice z hz)
    _ = (π / 2) * (gbar_Kang k * ∑ j ∈ Finset.range (k + 1),
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_const_mul]
        congr 1
        rw [setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
          (fun z _ => Finset.mul_sum _ _ _)]
        exact MeasureTheory.integral_finsetSum (Finset.range (k + 1))
          (fun j hj => (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
    _ ≤ (π / 2) * (gbar_Kang k * ∑ j ∈ Finset.range (k + 1),
          ((9 / 4) * (π / 2) * Work.Spaces.HkSq α k F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (le_of_lt (gbar_Kang_pos k))
        exact (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
    _ = (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
          Work.Spaces.HkSq α k F := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem Gbar_Hk_le_open_SmoothOpen (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → SmoothOpen F → Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  refine ⟨Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2)))), ?_, ?_⟩
  · have hK : 0 < gbar_Kang k := gbar_Kang_pos k
    positivity
  · intro α F hα hα1 hF hmem
    have hDnn : (0 : ℝ) ≤ (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) := by
      have hK : 0 < gbar_Kang k := gbar_Kang_pos k
      positivity
    have hsq := Gbar_HkSq_le_open α hα hα1 k F hF hmem
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        ≤ Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
            Work.Spaces.HkSq α k F) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2)))) *
            Real.sqrt (Work.Spaces.HkSq α k F) := Real.sqrt_mul hDnn _


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.step3Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option linter.unusedVariables false

/-! ## Two elementary helpers -/



/-! ## The lemma -/


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceLeftTendsto =====
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
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Slice integrability of `g z · · sinθcos²θ` from the honesty of `g` -/


/-! ## The moment identity for the source -/


/-! ## Slice integrability of the `∂_zΨ`-moment from the equation -/


/-! ## The main theorem -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.HonHardyCosWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.Step1G

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # The sharp weighted Hardy inequality with a `cos²(2θ)` weight, honest hypotheses

This file proves `HonHardyCosWeight`: for `0 ≤ η < 1` there is `C > 0` such that for every
`f : ℝ → ℝ` of class `C²` on the *open* interval `(0, π/2)` whose one-sided limits at the two
endpoints vanish and whose two `η`-weighted energies `∫ f² sin(2θ)^{-η}` and
`∫ (f')² sin(2θ)^{-η}` are finite,

`∫ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫ (f')² sin(2θ)^{-η} + C ∫ f² sin(2θ)^{-η}`.

The sharp constant `(1+η)^{-2}` is produced by the *half-interval* form of the inequality,
`Work.FTS.EllipticEst.H2W.AeWAux.leftHalfSharp`, which is the open-interval version of the
classical sharp Hardy inequality (no boundary condition at the singular endpoint is needed: the
finiteness of the `cos²`-weighted singular integral supplies the endpoint decay).  The halves
`(0, π/4)` and `(π/4, π/2)` are glued after reflecting the second one by `θ ↦ π/2 - θ` (under
which `sin(2θ)` is invariant and `cos(2θ)` changes sign, so the `cos²`-weight is preserved).

The case in which the left-hand integrand is *not* integrable needs separate treatment:
Mathlib's totalised integral assigns it the value `0`, and then the claim reduces to the
nonnegativity of the right-hand side.
-/

/-! ## Auxiliary facts about the reflection `θ ↦ π/2 - θ` and about splitting `(0, π/2)` -/


private lemma sin_two_pi_half_sub (x : ℝ) :
    Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]





/-! ## The inequality on `(0, π/2)`, assuming the `cos²`-weighted integrand is integrable -/


/-! ## The target -/


end Work.FTS.EllipticEst.Honest.Step1G
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.honSliceDivCosLintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ = sEta` -/






/-! ## Boundedness of the slice and of its derivative -/





/-! ## The `θ`-split of `Iθ` -/


/-! ## The left half `[0, π/4]` -/



/-! ## The right half `[π/4, π/2]` -/






end

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.excess_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
## The `ℋ⁰`-integrand on the open quadrant

`ℋ⁰` is the *radial* level of the weighted `ℋ^k`-integrands: `HkIntegrand α 0 f z θ` is exactly
the square `(f z θ · w(z)/sin(2θ)^{η/2})²`, and it vanishes identically on the two angular
boundary lines and on the axis `z = 0` (both weights degenerate there).  Hence the `ℋ⁰`-vocabulary
is invariant under changes of the function outside the *open* quadrant
`Q0 = (0,∞) × (0,π/2)`, which is what lets us transfer the `ℋ⁰`-membership along identities that
only hold on `Q0`.
-/




/-- Multiplication of a `SmoothOpen` function by the polynomial `z²` stays `SmoothOpen`. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => z ^ 2 * g z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry g := by funext p; rfl
  rw [hfun]
  exact (contDiffOn_fst.pow 2).mul hg

/-! ## The `ℋ⁰`-integrand -/

/-- `HkIntegrand α 0 f` is the weighted square of `f`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The `ℋ⁰`-integrand vanishes at `z = 0`. -/
theorem HkIntegrand_zero_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  simp [Work.Spaces.w]

/-- The `ℋ⁰`-integrand vanishes at `θ = 0`. -/
theorem HkIntegrand_zero_theta_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [HkIntegrand_zero_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand vanishes at `θ = π/2`. -/
theorem HkIntegrand_zero_theta_pi {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [HkIntegrand_zero_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand of a function continuous on the open quadrant is continuous there. -/
theorem continuousOn_HkIntegrand_zero {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      = fun p : ℝ × ℝ => (f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    funext p
    exact HkIntegrand_zero_eq α f p.1 p.2
  rw [hfun]
  exact (hf.mul (Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2

/-! ## `ℋ⁰`-membership: domination, congruence, addition -/

/-- **`ℋ⁰`-membership by a pointwise majorant.**  If `f` is continuous on the open quadrant and
`HkIntegrand α 0 f` is dominated on the closed quadrant by a function whose angular slices are
integrable and whose slice-integral is integrable, then `f ∈ ℋ⁰`. -/
theorem HkMem_zero_of_majorant {α : ℝ} {f M : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMsl : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hC := continuousOn_HkIntegrand_zero (α := α) hf
  refine Work.Blocks.HkMem_of_majorant_aesm (α := α) (k := 0) (f := f) (M := M) ?_ ?_ hMsl hMz hle
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine (MeasureTheory.aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      exact (HkIntegrand_zero_zero (α := α) f θ).symm
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hC hz0
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hC).integral_prod_right'

/-- **`ℋ⁰`-membership transfers along an identity on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.Spaces.HkMem α 0 g) :
    Work.Spaces.HkMem α 0 f := by
  refine HkMem_zero_of_majorant (α := α) (f := f)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g z θ) hf ?_ ?_ ?_
  · intro z hz
    exact (hg.1 z hz).const_mul 2
  · have h' := hg.2.const_mul 2
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_zero]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ0
      · rw [← hθ_eq, HkIntegrand_zero_theta_zero]
        exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g z 0)
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ1
        · rw [hθ_eq, HkIntegrand_zero_theta_pi]
          exact mul_nonneg (by norm_num)
            (Work.Spaces.HkIntegrand_nonneg α 0 g z (Real.pi / 2))
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, h z θ hz0 hθ0 hθ1]
          nlinarith [sq_nonneg (g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]


/-! ## Single radial summands of an honest `ℋ^k`-integrand -/

/-- **A single radial summand of an honest `ℋ^k`-integrand is honest in `ℋ⁰`.**  For `i ≤ k` the
`i`-th radial summand of `HkIntegrand α k f` is `HkIntegrand α 0 (D_z^i f)`, and it is dominated
by `HkIntegrand α k f`; both honesty requirements transfer. -/
theorem excess_zsummand_mem (α : ℝ) (k i : ℕ) (f : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) (hi : i ≤ k) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) := by
  refine HkMem_zero_of_majorant (α := α) (f := Work.Spaces.DzIter i f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) hcont (fun z hz => hmem.1 z hz)
    hmem.2 ?_
  intro z hz θ hθ
  rw [HkIntegrand_zero_eq]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi

/-! ## The two radial summands at levels `k + 1` and `k + 2` -/




/-! ## The finiteness transfer for the mixed interpolation

`D_z∂_θG` is bounded in `L²(ρ)` (`ρ = w²σ`, `σ = sin(2θ)^{-η}`) by the three quantities
`dInt G = ∫∫(D_zG)²ρ`, `ttInt G = ∫∫(∂_θ²G)²ρ` and `ddInt G = ∫∫(D_z²G)²ρ`:

* the *slicewise* Hardy-type inequality `slice_key` gives, for every `z > 0`,
  `κ ∫_θ (D_z∂_θG)²σ ≤ -∫_θ (D_zG)(∂_θ²G)σ + c₁ ∫_θ (D_zG)²σ`, `κ = (1-η)/(1+η)`;
* the logarithmic cut-off `zc φ k` makes the `z`-integration legitimate
  (`cut_integration`), and the `z`-integration by parts `radial_ibp_weight` rewrites the middle
  term, whose two pieces are bounded by `ibp_bounds`;
* Fatou/monotone convergence lets the cut-off tend to `1`.

The conclusion is the *honesty* of the `D_z∂_θ`-slot, i.e. the finiteness transfer. -/


/-- The `z`-slice of a function smooth on the open strip is smooth on `(0,∞)`. -/
theorem slice_z_contDiffOn {f : ℝ → ℝ → ℝ} {N : ℕ} {θ : ℝ}
    (h : ContDiffOn ℝ N (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffOn ℝ N (fun z => f z θ) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.DzAmgm.contDiffOn_slice_z_nat
    (s := Set.Ioi 0) (t := Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) h hθ






/-! ## The pointwise identities of the assembly -/




/-- **The `D_z`-`∂_θ` commutation at the shifted level**:
`D_z∂_θ(D_z^kΨ) = D_z^{k+1}∂_θΨ` on the half-quadrant, for `Ψ` smooth on a neighbourhood of
the closed quadrant. -/
theorem Dz_pth_DzIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
        = Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ := by
  intro z hz θ hθ
  have h1 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter k (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.Dz_congr (Work.Elliptic.pth_DzIter_eqOn Ψ hΨ k)
      (Work.Spaces.mem_nbhU hz hθ)
  rw [h1, Work.Spaces.DzIter_succ]
end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.StepPieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.StepPieces`: the assembly of the induction step, with a cone that avoids `propHk_fts`

This module is a *verbatim copy* of `Work.FTS.EllipticEst.remov.EllEstUnif_step_of_pieces`
(`Submission/Work/FTS/EllipticEst/remov/EllEstUnif_step.lean`, lines 39--328), renamed into the
namespace `Work.FTS.EllipticEst.TT.ESW.Pieces`.

The copy is necessary because the original module's import cone contains
`remov.EllWeakPos_DzIter_one_shift` and `remov.A_top_slot_bound`, whose cones reach
`remov.propHk_fts`; and `propHk_fts` reaches `TT.propHk_core`, which *imports* the target of this
work, `TT.est_step_weak`.  Anything on the critical path of `TT.est_step_weak` must therefore
avoid `propHk_fts` entirely.

The statement is the one of the original: with the exact splitting of `HkSq` at level `k`, the
domination of the shifted level-`(k-1)` expression, the admissibility of the radially
differentiated data, the top-angular core and the elementary side conditions as hypotheses, the
induction step follows.  Only `remov.EllEstUnifStepAux` (the vocabulary `Qd`, `Tk`) is imported.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Step

/-- `√(x + y) ≤ √x + √y` for nonnegative `x, y`. -/
theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h4 : 0 ≤ Real.sqrt x + Real.sqrt y := by
    have h1 := Real.sqrt_nonneg x
    have h2 := Real.sqrt_nonneg y
    linarith
  have h5 : (Real.sqrt x + Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
      = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
    have h2 := Real.sq_sqrt hx
    have h3 := Real.sq_sqrt hy
    nlinarith only [h2, h3]
  have h6 : 0 ≤ 2 * (Real.sqrt x * Real.sqrt y) := by
    have h1 := Real.sqrt_nonneg x
    have h2 := Real.sqrt_nonneg y
    positivity
  have h7 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x + y)
  have h8 := Real.sqrt_nonneg (x + y)
  nlinarith only [h5, h6, h7, h8, h4]

/-- `√(x + y + z) ≤ √x + √y + √z` for nonnegative `x, y, z`. -/
theorem sqrt_add_add_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have h1 : Real.sqrt (x + y + z) ≤ Real.sqrt (x + y) + Real.sqrt z :=
    sqrt_add_le' (by linarith) hz
  have h2 : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := sqrt_add_le' hx hy
  linarith

end Step

open Work.FTS.EllipticEst.TT

/-- **The assembly of the induction step.**  Given the exact splitting of `HkSq` at level `k`
(with the top angular slot), the domination of the shifted level-`(k-1)` expression, the
admissibility of the radially differentiated data, the top-angular core, and the elementary
smoothness and congruence side conditions, the induction step `EllEstUnif (k-1) C → EllEstUnif k C`
follows. -/
theorem EllEstUnif_step_of_pieces
    (hstep : ∀ {k : ℕ}, 1 ≤ k → ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.remov.Step.Qd) → Work.Spaces.HkMem α k f →
      Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α (k - 1) f
        + ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f) + Work.FTS.EllipticEst.remov.Step.Tk α k f)
    (hshift : ∀ {k : ℕ}, 1 ≤ k → ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.remov.Step.Qd) → Work.Spaces.HkMem α k f →
      Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k f)
    (hpos : ∀ {α : ℝ} {k : ℕ}, 2 ≤ k → ∀ {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
        (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ))
    (hcore : ∀ (D : ℝ), 0 < D → ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) ≤ C * Work.Spaces.HkNorm α k F)
    (hsmF : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.remov.Step.Qd)
    (hsmA : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) Work.FTS.EllipticEst.remov.Step.Qd)
    (hsmB : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.remov.Step.Qd)
    (hAz : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    (hBz : ∀ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
          = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :
    ∀ k : ℕ, 3 ≤ k → (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
      (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C := by
  intro k hk _ hk1
  obtain ⟨C₁, hC₁pos, hEst⟩ := hk1
  obtain ⟨Ck, hCkpos, hcorek⟩ := hcore (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
    (mul_pos hC₁pos (Real.sqrt_pos.mpr (by positivity))) k hk
  refine ⟨2 * C₁ * (1 + Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
    + Ck + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hFmem : Work.Spaces.HkMem α k F := h.memF
  have hA : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := h.memA
  have hB : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hsmF' := hsmF h
  have hsmA' := hsmA h
  have hsmB' := hsmB h
  -- the shifted data and the descent of the equation data
  have h₂ : Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := hpos (by omega) h
  have h₁ : Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1) F Ψ :=
    ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmF' hFmem,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmA' hA,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) hsmB' hB,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
        (by omega) (Work.FTS.EllipticEst.TT.smoothOpen_diagHon hsmB') h.memZPth2⟩
  have e₁ := hEst α F Ψ hα hα4 h₁
  have e₂ := hEst α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 h₂
  -- the constants
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hDzFbound : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F)
      ≤ Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkNorm α k F := by
    have h1 : Work.Spaces.HkSq α (k - 1) (Work.Spaces.DzIter 1 F)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k F :=
      hshift (by omega) α F hsmF' hFmem
    have h2 : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F)
        ≤ Real.sqrt (((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k F) := by
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt h1
    refine le_trans h2 ?_
    rw [Real.sqrt_mul (by positivity), Work.Spaces.HkNorm]
  have hFmono : Work.Spaces.HkNorm α (k - 1) F ≤ Work.Spaces.HkNorm α k F := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (f := F) (by omega) hFmem)
  -- the two hypotheses of the core
  have hcore_hyp₁ : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
    calc α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ C₁ * Work.Spaces.HkNorm α (k - 1) F := e₁
      _ ≤ C₁ * Work.Spaces.HkNorm α k F :=
          mul_le_mul_of_nonneg_left hFmono (le_of_lt hC₁pos)
      _ ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
          have h0 : (0 : ℝ) ≤ C₁ * Work.Spaces.HkNorm α k F := by
            have hkF : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
            positivity
          have h1 := mul_le_mul_of_nonneg_left hsqrt1 h0
          nlinarith [h1]
  have hcore_hyp₂ : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by
    calc α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ C₁ * Work.Spaces.HkNorm α (k - 1) (Work.Spaces.DzIter 1 F) := e₂
      _ ≤ C₁ * (Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkNorm α k F) :=
          mul_le_mul_of_nonneg_left hDzFbound (le_of_lt hC₁pos)
      _ = (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F := by ring
  have htop := hcorek α F Ψ hα hα4 h hcore_hyp₁ hcore_hyp₂
  -- the exact splitting, for `A` and `B`, with the shifted fields identified
  have hAeq : Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = Work.Spaces.HkSq α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    Work.FTS.EllipticEst.HkSq_congr_open α (k - 1) (fun z θ hz hθ hlt => hAz h z θ hz hθ hlt)
  have hBeq : Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      = Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α (k - 1) (fun z θ hz hθ hlt => hBz h z θ hz hθ hlt)
  have hsplitA := hstep (k := k) (by omega) α
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hsmA' hA
  have hsplitB := hstep (k := k) (by omega) α (Work.Spaces.pthIter 2 Ψ) hsmB' hB
  rw [hAeq] at hsplitA
  rw [hBeq] at hsplitB
  -- square-root bookkeeping
  have hrootA : Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hsplitA) ?_
    have h1 : 0 ≤ Work.Spaces.HkSq α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.Spaces.HkSq_nonneg _ _ _
    have h2 : 0 ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
      have := Work.Spaces.HkSq_nonneg α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      positivity
    have h3 : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    refine le_trans (Step.sqrt_add_add_le h1 h2 h3) ?_
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), Work.Spaces.HkNorm]
    exact le_refl _
  have hrootB : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ)
      ≤ Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hsplitB) ?_
    have h1 : 0 ≤ Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.Spaces.HkSq_nonneg _ _ _
    have h2 : 0 ≤ ((k : ℝ) + 1) * Work.Spaces.HkSq α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
      have := Work.Spaces.HkSq_nonneg α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      positivity
    have h3 : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ) := Work.FTS.EllipticEst.remov.Step.Tk_nonneg _ _ _
    refine le_trans (Step.sqrt_add_add_le h1 h2 h3) ?_
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), Work.Spaces.HkNorm]
    exact le_refl _
  -- final bookkeeping
  have hFk : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
  have hb1 : α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F :=
    hcore_hyp₂
  have hcross : Real.sqrt ((k : ℝ) + 1) * α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
      + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ Real.sqrt ((k : ℝ) + 1) * (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
        * Work.Spaces.HkNorm α k F := by
    have h0 : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hb1 h0
    nlinarith [h1]
  have hαsq : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have htop' : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ)) ≤ Ck * Work.Spaces.HkNorm α k F := htop
  calc α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ)
      ≤ α ^ 2 * (Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + (Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))) := by
        nlinarith only [hrootA, hrootB, hαsq, le_refl (0:ℝ)]
    _ = (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ))
        + Real.sqrt ((k : ℝ) + 1) * α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
        + Real.sqrt ((k : ℝ) + 1) * Work.Spaces.HkNorm α (k - 1)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        + (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Work.Spaces.pthIter 2 Ψ))) := by ring
    _ ≤ (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkNorm α k F
        + Real.sqrt ((k : ℝ) + 1) * (C₁ * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
          * Work.Spaces.HkNorm α k F
        + Ck * Work.Spaces.HkNorm α k F := by
        linarith [hcore_hyp₁, hcross, htop']
    _ ≤ (2 * C₁ * (1 + Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)))
        + Ck + 1) * Work.Spaces.HkNorm α k F := by
        set S := Real.sqrt ((k : ℝ) + (k : ℝ) * (k : ℝ)) with hS
        set x := Real.sqrt ((k : ℝ) + 1) with hx
        have hSnn : 0 ≤ S := Real.sqrt_nonneg _
        have hxnn : 0 ≤ x := Real.sqrt_nonneg _
        have hx1 : 1 ≤ x := by
          rw [hx]
          have h1k : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ k + 1)
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt h1k
        have hxS : x ≤ S := by
          rw [hx, hS]
          exact Real.sqrt_le_sqrt (by push_cast; nlinarith)
        have hprod1 : (1 - x) * S ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hSnn
        have hscal : C₁ * S + x * (C₁ * S) + Ck ≤ 2 * C₁ * (1 + x * S) + Ck + 1 := by
          nlinarith [hprod1, hC₁pos, hSnn, hxnn, hx1]
        have hmul := mul_le_mul_of_nonneg_right hscal hFk
        rw [hS, hx] at hmul ⊢
        nlinarith [hmul]

end Work.FTS.EllipticEst.TT.ESW.Pieces
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.slice_tendsto_pi_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest

/-- **The right-endpoint behaviour of a `θ`-slice from the raw hypotheses, for every real `α`.**
Same statement and same proof as `Work.FTS.EllipticEst.H2W.AeProof.sliceRightTendsto_raw`, but
without the hypotheses `0 < α` and `α ≤ 1/4`: the only place where the proof uses `0 < α` is the
nonnegativity of the coefficient `α(5+α)z` of the `∂_zΨ`-term, and there `|α(5+α)z|` does the
job.  (For `α > 0` the two statements coincide, so this is a strict generalisation.) -/
theorem sliceRightTendsto_raw_allAlpha (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemF : Work.Spaces.HkMem α 0 F)
    (hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |Ψ z θ| ≤ K * (Real.pi / 2 - θ) := by
  -- the base point `a` of the `θ`-integration
  set a : ℝ := Real.pi / 4 with hadef
  have ha_pos : 0 < a := by rw [hadef]; linarith [Real.pi_pos]
  have ha_lt : a < Real.pi / 2 := by rw [hadef]; linarith [Real.pi_pos]
  have hz1 : 0 < z + 1 := by linarith
  set C5 : ℝ := |α * (5 + α) * z| with hC5def
  -- slicewise `L²(σ)`-integrability of `∂_θθΨ` at every `s > 0` (from `memB`)
  have hth : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemB hs
    refine h0.congr_fun (fun θ _ => ?_) measurableSet_Icc
    have h1 : Work.Spaces.pthIter 2 Ψ s θ
        = deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    show (Work.Spaces.pthIter 2 Ψ s θ) ^ 2 * sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2 * sEta θ
    rw [h1]
  -- boundedness of the slices and of their `θ`-derivatives at `z` and at `z + 1`
  obtain ⟨M, hMpos, hMb⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz (hsm 2)) (hth z hz)
  obtain ⟨M₁, hM₁pos, hM₁b⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz1 (hsm 2)) (hth (z + 1) hz1)
  -- the `σ`-weighted square of the `z`-slice of `∂_z²Ψ` (from `memA`, divided by `z⁴`)
  have hp_int : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma hmemA hz
    have hz2 : (z ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((z ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- the `σ`-weighted square of the `F`-slice
  have hF_int : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := HkMemSliceSqSigma hmemF hz
  -- a.e. measurability of the `σ`-weighted slice norm of `∂_z²Ψ` (from the honest `z`-integral
  -- `hmemA.2`, after dividing by the measurable weight `w s²·s⁴`)
  have hγaem : AEMeasurable
      (fun s => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (s ^ 4)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have hm : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (s ^ 4)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
        (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    have hden : AEMeasurable (fun s : ℝ => (Work.Spaces.w s) ^ 2 * s ^ 4)
        (volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aemeasurable ?_
      have hw : Measurable fun s : ℝ => Work.Spaces.w s := by
        show Measurable fun s : ℝ => (1 + s) ^ 2 / s ^ 2
        fun_prop
      exact (hw.pow_const 2).mul (measurable_id.pow_const 4)
    refine (hm.div hden).congr ?_
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
    have h0' : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz), s ∈ Set.Ioi (0 : ℝ) := by
      rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      filter_upwards [h0] with s hs hmem
      exact lt_of_le_of_ne hmem (Ne.symm hs)
    filter_upwards [h0'] with s hs
    have hw : (Work.Spaces.w s) ^ 2 * s ^ 4 ≠ 0 := by
      have h1 : Work.Spaces.w s ≠ 0 := by
        show (1 + s) ^ 2 / s ^ 2 ≠ 0
        have hs' : s ≠ 0 := ne_of_gt hs
        have h1' : (1 : ℝ) + s ≠ 0 := by
          have hs0 : (0 : ℝ) < s := hs
          have : (0 : ℝ) < 1 + s := by linarith
          exact ne_of_gt this
        exact div_ne_zero (pow_ne_zero 2 h1') (pow_ne_zero 2 hs')
      exact mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 4 (ne_of_gt hs))
    exact mul_div_cancel_left₀ _ hw
  -- `γ` written with the `s⁴`-weight of `memA` (the form `HkMemSliceGammaLinTop` bounds)
  have hγw : ∀ s, (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      = (s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by ring)
  -- a.e. measurability of the *weighted* slice norm, on `Icc z (z+1)`
  have hγw_aem : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have h1 : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    -- remove the weight `w s²` (multiply the *unweighted* norm, whose measurability is `hγaem`,
    -- by the measurable factor `(s²)²`)
    have h2 : AEMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        (volume.restrict Work.Spaces.Iz) := by
      refine (hγaem.mul ((measurable_id.pow_const 2).pow_const 2).aemeasurable).congr ?_
      refine Filter.Eventually.of_forall fun s => ?_
      show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) * (s ^ 2) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ
      rw [mul_comm, (hγw s).symm]
    exact (h2.ennreal_ofReal).mono_measure
      (Measure.restrict_mono (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)) le_rfl)
  -- the weighted version is exactly `HkMemSliceGammaLinTop`
  have hγw_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    refine lt_of_eq_of_lt ?_ (HkMemSliceGammaLinTop hmemA hz)
    exact MeasureTheory.lintegral_congr fun s => by rw [hγw s]
  -- the unweighted lintegral, via the pointwise scaling `γ s ≤ (z⁴)⁻¹ · γ_w s` on `Icc z (z+1)`
  have hgamma : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    have hpt : ∀ s ∈ Set.Icc z (z + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
      have hs4 : 0 < s ^ 4 := pow_pos hs0 4
      have hle : (s ^ 4)⁻¹ ≤ (z ^ 4)⁻¹ :=
        inv_anti₀ (pow_pos hz 4) (pow_le_pow_left₀ (le_of_lt hz) hs.1 4)
      have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
        rw [hγw s]
        have heq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            = (s ^ 4)⁻¹ * ((s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) := by
          rw [show (s ^ 2) ^ 2 = s ^ 4 from by ring, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hs4), one_mul]
        conv_lhs => rw [heq]
        refine mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (s ^ 2)) ?_)
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
      calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ENNReal.ofReal (((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
              (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))).mpr h1
        _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
      _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_const_mul'' _ hγw_aem
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγw_lin
  -- a.e. measurability of `ofReal γ` on `Icc z (z+1)` (transfer from `hγaem`)
  have hγaemK : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) :=
    (hγaem.ennreal_ofReal).mono_measure (Measure.restrict_mono_set volume
      (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)))
  -- the lintegral of `(1/2)(γ + π/2)` is finite (this is the constant `c` below)
  have hb_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2)) < ⊤ := by
    -- it suffices to bound the *decomposed* integrand `ofReal γ + ofReal (π/2)`, since
    -- `(1/2)(γ + π/2) ≤ γ + π/2`; this avoids pulling out the constant `ofReal (1/2)`
    have hsum : ∫⁻ s in Set.Icc z (z + 1), (ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + ENNReal.ofReal (Real.pi / 2)) < ⊤ := by
      rw [MeasureTheory.lintegral_add_left' hγaemK]
      refine ENNReal.add_lt_top.mpr ⟨hgamma, ?_⟩
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt ?_ hsum
    refine MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s _ => ?_))
    have hγnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have hle : (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2) ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2 := by linarith [Real.pi_pos]
    calc ENNReal.ofReal ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))
        ≤ ENNReal.ofReal ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + Real.pi / 2) := (ENNReal.ofReal_le_ofReal_iff (by linarith [Real.pi_pos])).mpr hle
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + ENNReal.ofReal (Real.pi / 2) := by
          rw [ENNReal.ofReal_add hγnn (by linarith [Real.pi_pos])]
  -- the `b`-independent constant bounding `|P_b(z)|`
  set c : ℝ := ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2))) with hcdef
  have hcnonneg : 0 ≤ c := by rw [hcdef]; exact ENNReal.toReal_nonneg
  -- joint continuity of `pz Ψ` on the open quadrant (finite order: `∂_z` of a `C¹` function)
  have hpz_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderivWithin ℝ (Function.uncurry Ψ)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (hsm 1).fderivWithin (m := 0) hU.uniqueDiffOn (by norm_num)
      refine (contDiffOn_zero.mp h1).congr (fun p hp => ?_)
      show fderiv ℝ (Function.uncurry Ψ) p
        = fderivWithin ℝ (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p
      rw [fderivWithin_of_isOpen hU hp]
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p (1, 0))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    refine h2.congr (fun p hp => ?_)
    show Work.Spaces.pz Ψ p.1 p.2 = fderiv ℝ (Function.uncurry Ψ) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv
      (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp))
  -- **first application**: `∂_z ∫_a^b Ψ s θ dθ = ∫_a^b pz Ψ s θ dθ` for `s ∈ [z, z+1]`
  have hZderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Ψ t θ) (∫ θ in a..b, Work.Spaces.pz Ψ s θ) s := by
    intro b hb s hs
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1)
      ?_ ?_ ?_
    · exact ((hsm 0).continuousOn.mono hrect).mono hsub
    · exact (hpz_cont.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact (Work.Spaces.differentiableAt_curry_left
        (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxU))).hasDerivAt
  -- *** Stage A ***
  -- `F` is smooth on the open quadrant (it *is* `bslOp α Ψ` there), so each of its `θ`-slices
  -- is continuous on `(0, π/2)`; in particular `F z ·` is a genuine interval integral on `[a,b]`.
  have hFcont : ContinuousOn (fun θ => F z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hU : IsOpen Qd := isOpen_Qd
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) (hsm 2)
    have hpz2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
      have h2 : ContDiffOn ℝ (2 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
        Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 2) (hsm 3)
      have h1 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) h2
      rw [pzIter_two_eq Ψ]
      exact h1
    have hp2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz hpz2).continuousOn
    have hp1 : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pz Ψ) hz hpz1).continuousOn
    have hpsi : ContinuousOn (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice Ψ hz (hsm 0)).continuousOn
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (hsm 2)
    have hpth2 : ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ'))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      rw [pthIter_two_eq Ψ z]
      exact h2.continuousOn
    have htan : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have hpthtan : ContinuousOn (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        htan.mul hslice2
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
      rw [hfun]
      exact h1.continuousOn
    have hcomb : ContinuousOn (fun θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        + (-Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
            - 6 * Ψ z θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hp2.const_mul (-(α ^ 2 * z ^ 2))).sub (hp1.const_mul (α * (5 + α) * z))).add
        ((hpth2.neg.add hpthtan).sub (hpsi.const_mul 6))
    refine hcomb.congr (fun θ hθ => ?_)
    simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
      using (heq z hz θ hθ.1 hθ.2).symm
  -- the `σ`-weighted square of the `∂_z²Ψ`-slice, for every `s > 0`
  have hps_int : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemA hs
    have h2 : (s ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((s ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- joint continuity of `pz Ψ` on the open quadrant
  have hUq : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hpz1c : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hUq (n := 1) (hsm 2)
  have hpz2c : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn hUq (hsm 2)
  -- **second application**: `∂_z ∫_a^b pz Ψ s θ dθ = ∫_a^b pzIter 2 Ψ s θ dθ`
  have hPderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pz Ψ t θ) (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
      s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz_cont.mono hrect).mono hsub
    · exact (hpz2c.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      have h := hasDerivAt_slice_of_contDiffOn_open hUq hpz1c hxU
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pzIter_succ,
        show (1 : ℕ) = 0 + 1 from rfl, Work.Spaces.pzIter_zero] using h
  -- *** Stage B ***
  -- the two `b`-independent `σ`-weighted slice norms
  set QP : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ with hQPdef
  set QF : ℝ := ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * sEta θ with hQFdef
  have hQPnn : 0 ≤ QP := by
    rw [hQPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hQFnn : 0 ≤ QF := by
    rw [hQFdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  -- the third application: `Q_b` is differentiable, hence continuous
  have hpz2cd : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
    have h1 : ContDiffOn ℝ (4 : WithTop ℕ∞) (Function.uncurry Ψ) Qd := hsm 4
    have h2 : ContDiffOn ℝ (3 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 3) h1
    have h3 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 2) h2
    rw [pzIter_two_eq Ψ]
    exact h3
  have hpz3cd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 3 Ψ)) Qd := by
    have h4 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 1) hpz2cd
    have h5 : Work.Spaces.pzIter 3 Ψ = Work.Spaces.pz (Work.Spaces.pzIter 2 Ψ) := rfl
    rw [h5]
    exact h4
  have hQderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ t θ)
      (∫ θ in a..b, Work.Spaces.pzIter 3 Ψ s θ) s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz2c.mono hrect).mono hsub
    · exact ((hpz3cd.continuousOn).mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact hasDerivAt_slice_of_contDiffOn_open hUq (hpz2cd.of_le (by norm_num)) hxU
  -- **the bound on `P_b(z)`** — the only place where the `z`-dependence of the data is used
  have hPb : ∀ b ∈ Set.Ioo a (Real.pi / 2),
      |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c := by
    intro b hb
    have hZder := hZderiv b hb
    have hPder := hPderiv b hb
    have hQder := hQderiv b hb
    have hcontP : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hPder s hs).continuousAt.continuousWithinAt
    have hcontQ : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hQder s hs).continuousAt.continuousWithinAt
    have hceq : Set.uIcc z (z + 1) = Set.Icc z (z + 1) := Set.uIcc_of_le (by linarith)
    have hcontPu : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.uIcc z (z + 1)) := by rw [hceq]; exact hcontP
    -- first fundamental-theorem step: `∫_z^{z+1} P_b = Z(z+1) - Z(z)`
    have h1 : (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
        = (∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => ∫ θ in a..b, Ψ t θ)
        (f' := fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ) ?_ hcontPu.intervalIntegrable
      intro s hs
      rw [hceq] at hs
      exact hZder s hs
    -- second step: `P_b(t) - P_b(z) = ∫_z^t Q_b`
    have h2 : ∀ t ∈ Set.Icc z (z + 1),
        (∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          = ∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ) := by
      intro t ht
      have hle : z ≤ t := ht.1
      have hsub : Set.uIcc z t ⊆ Set.Icc z (z + 1) := by
        rw [Set.uIcc_of_le hle]
        exact Set.Icc_subset_Icc le_rfl ht.2
      have hint : IntervalIntegrable (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
          volume z t := (hcontQ.mono hsub).intervalIntegrable
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hPder s (hsub hs)) hint).symm
    -- the algebraic consequence
    have h3 : (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
        = ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
          - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
              - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) := by
      have hsub2 : (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
            - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          = (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
            - ∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ z θ) :=
        intervalIntegral.integral_sub hcontPu.intervalIntegrable intervalIntegrable_const
      rw [hsub2, h1, intervalIntegral.integral_const]
      ring
    -- the uniform bound on the subtracted term
    have hB : ∀ t ∈ Set.Icc z (z + 1),
        |(∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)| ≤ c := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hzt | hzt
      · rw [← hzt, sub_self, abs_zero]; exact hcnonneg
      · rw [h2 t ht]
        have hQint : IntegrableOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
            (Set.Icc z (z + 1)) := hcontQ.integrableOn_Icc
        have hQabs : IntegrableOn (fun s => |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
            (Set.Icc z (z + 1)) := by
          simpa only [Real.norm_eq_abs, MeasureTheory.IntegrableOn] using hQint.norm
        have hstep : |∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)|
            ≤ ∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ| := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzt.le) ?_
          rw [intervalIntegral.integral_of_le hzt.le]
          refine MeasureTheory.setIntegral_mono_set hQabs
            (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (Filter.Eventually.of_forall (fun s hs => ?_))
          exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
        refine le_trans hstep ?_
        calc (∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
              ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|) :=
                setIntegral_le_toReal_lintegral _
                  (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            _ ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))) := by
                refine ENNReal.toReal_mono (ne_of_lt hb_lin) (MeasureTheory.lintegral_mono_ae ?_)
                refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
                have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
                have hQb := le_trans
                  (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
                  (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) (hps_int s hs0))
                have hnn : 0 ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2) :=
                  mul_nonneg (by norm_num) (add_nonneg
                    (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
                    (by linarith [Real.pi_pos]))
                exact (ENNReal.ofReal_le_ofReal_iff hnn).mpr hQb
            _ = c := rfl
    -- the two slice integrals at `z` and `z + 1`
    have hZc : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ z θ| ≤ C) →
        |∫ θ in a..b, Ψ z θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZc1 : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ (z + 1) θ| ≤ C) →
        |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ (z + 1) θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZ1 := hZc1 M₁ hM₁pos.le (fun θ hθ => (hM₁b θ hθ).2)
    have hZ0 := hZc M hMpos.le (fun θ hθ => (hMb θ hθ).2)
    calc |∫ θ in a..b, Work.Spaces.pz Ψ z θ|
        = |((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          conv_lhs => rw [h3]
      _ ≤ |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
            + |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          have := abs_sub_le ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            (0 : ℝ) (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          simpa using this
      _ ≤ (M₁ * (Real.pi / 2) + M * (Real.pi / 2)) + c := by
          refine add_le_add ?_ ?_
          · calc |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
                ≤ |∫ θ in a..b, Ψ (z + 1) θ| + |∫ θ in a..b, Ψ z θ| := by
                  simpa using abs_sub_le (∫ θ in a..b, Ψ (z + 1) θ) (0 : ℝ) (∫ θ in a..b, Ψ z θ)
              _ ≤ M₁ * (Real.pi / 2) + M * (Real.pi / 2) := add_le_add hZ1 hZ0
          · have hmain : |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| ≤ c := by
              have h := intervalIntegral.norm_integral_le_of_norm_le_const
                (f := fun t => (∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                  - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (a := z) (b := z + 1) (C := c)
                (fun t ht => by
                  rw [Real.norm_eq_abs]
                  rw [Set.uIoc_of_le (by linarith : z ≤ z + 1)] at ht
                  exact hB t ⟨le_of_lt ht.1, ht.2⟩)
              simpa only [Real.norm_eq_abs, show (z + 1) - z = 1 from by ring, abs_one,
                mul_one] using h
            exact hmain
      _ = (Real.pi / 2) * (M + M₁) + c := by ring
  -- the per-`b` bound
  set K : ℝ := |Real.tan a * Ψ z a| + C5 * ((Real.pi / 2) * (M + M₁) + c)
      + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) + (1 / 2) * (QF + Real.pi / 2)
      + 2 * M + 6 * (M * (Real.pi / 2)) with hKdef
  have key : ∀ b ∈ Set.Ioo a (Real.pi / 2), |Real.tan b * Ψ z b| ≤ K := by
    intro b hb
    rw [hKdef]
    have hab' : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro θ hθ
      rw [Set.uIcc_of_le (le_of_lt hb.1)] at hθ
      exact ⟨lt_of_lt_of_le ha_pos hθ.1, lt_of_le_of_lt hθ.2 hb.2⟩
    have hFint : IntervalIntegrable (fun θ => F z θ) volume a b :=
      (hFcont.mono hab').intervalIntegrable
    have hcontp : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz (n := 1) (hpz2cd.of_le (by norm_num))
      exact h2.continuousOn.mono hab'
    have hpI : IntervalIntegrable (fun θ => Work.Spaces.pzIter 2 Ψ z θ) volume a b :=
      hcontp.intervalIntegrable
    have hcontq : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pz Ψ) hz (n := 1) hpz1c
      exact h2.continuousOn.mono hab'
    have hqI : IntervalIntegrable (fun θ => Work.Spaces.pz Ψ z θ) volume a b :=
      hcontq.intervalIntegrable
    have hcontψ : ContinuousOn (fun θ => Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 0 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice Ψ hz (n := 0) (hsm 0)
      exact h2.continuousOn.mono hab'
    have hψI : IntervalIntegrable (fun θ => Ψ z θ) volume a b := hcontψ.intervalIntegrable
    have hslice1 : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 1) (hsm 1)
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 2) (hsm 2)
    have hcontp2 : ContinuousOn (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h2.continuousOn.mono hab'
    have hp2I : IntervalIntegrable (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        volume a b := hcontp2.intervalIntegrable
    have htansm : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      htansm.mul hslice2
    have hconttw : ContinuousOn (deriv (fun θ => Real.tan θ * Ψ z θ)) (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h1.continuousOn.mono hab'
    have htwI : IntervalIntegrable (deriv (fun θ => Real.tan θ * Ψ z θ)) volume a b :=
      hconttw.intervalIntegrable
    -- the derivative facts for the three functions of `TanSliceFTC`
    have hdu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
      fun θ hθ => (hslice1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdu1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (deriv (fun θ' => Ψ z θ')) θ := by
      intro θ hθ
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdtw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
      fun θ hθ => (htw.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    -- the amplitude `A` of the `tan`-identity, and its `(a,b)`-integral
    set A : ℝ → ℝ := fun θ => α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + α * (5 + α) * z * Work.Spaces.pz Ψ z θ + F z θ with hAdef
    have hAI : IntervalIntegrable A volume a b := by
      rw [hAdef]
      exact ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))).add hFint
    have hsplit : (∫ θ in a..b, A θ)
        = (α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ) := by
      rw [hAdef]
      rw [intervalIntegral.integral_add
        ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))) hFint]
      rw [intervalIntegral.integral_add (hpI.const_mul (α ^ 2 * z ^ 2))
        (hqI.const_mul (α * (5 + α) * z))]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- the `tan`-identity
    have heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * Ψ z t) θ
        = A θ + deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ + 6 * Ψ z θ := by
      intro θ hθ
      have hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, ha_pos], by linarith [hθ.2, hb.2]⟩
      have hb' := heq z hz θ hθo.1 hθo.2
      rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb'
      rw [hAdef]
      simp only [pthIter_two_eq_fun Ψ, Work.Spaces.pth] at hb' ⊢
      linear_combination (norm := ring_nf) hb'
    have hid := TanSliceFTC (u := fun θ => Ψ z θ) (A := A) (a := a) (b := b) (le_of_lt hb.1)
      (fun θ hθ => (hdu θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdu1 θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdtw θ (hab' hθ)).hasDerivAt)
      hp2I htwI hAI hψI heq
    -- the individual bounds
    have htanb : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
        ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hp_int)
    have hqbound : |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c :=
      hPb b hb
    have htanF : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
      le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hF_int)
    have hψbd : |∫ θ in a..b, Ψ z θ| ≤ M * (Real.pi / 2) := by
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ M * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := M) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact (hMb θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩).2)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hMpos.le)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hderivbd : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a| ≤ 2 * M := by
      have h1 : |deriv (fun θ => Ψ z θ) b| ≤ M :=
        (hMb b ⟨lt_trans ha_pos hb.1, hb.2⟩).1
      have h2 : |deriv (fun θ => Ψ z θ) a| ≤ M :=
        (hMb a ⟨ha_pos, ha_lt⟩).1
      have htri : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          ≤ |deriv (fun θ => Ψ z θ) b| + |deriv (fun θ => Ψ z θ) a| := by
        have := abs_sub_le (deriv (fun θ => Ψ z θ) b) 0 (deriv (fun θ => Ψ z θ) a)
        simpa using this
      linarith
    -- the `tan`-identity solved for the left-hand side
    have hid' : Real.tan b * Ψ z b
        = Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
          + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
          + 6 * ∫ θ in a..b, Ψ z θ := by linarith [hid]
    -- the `(a,b)`-integral of the amplitude
    have hAbound : |∫ θ in a..b, A θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
        + C5 * ((Real.pi / 2) * (M + M₁) + c)
        + (1 / 2) * (QF + Real.pi / 2) := by
      rw [hsplit]
      have htri : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ)|
          ≤ |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| := by
        have h2 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (∫ θ in a..b, F z θ)
        have h1 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ))
          ((α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ))
        linarith
      have hbd : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
              + C5 * ((Real.pi / 2) * (M + M₁) + c)
              + (1 / 2) * (QF + Real.pi / 2) := by
        have h1 : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (le_trans
            (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => Work.Spaces.pzIter 2 Ψ z θ) ha_pos hb.2
              (le_of_lt hb.1) hp_int)) (by positivity)
        have h2 : |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            ≤ C5 * ((Real.pi / 2) * (M + M₁) + c) := by
          rw [hC5def, abs_mul]
          exact mul_le_mul_of_nonneg_left (hPb b hb) (abs_nonneg _)
        have h3 : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
          le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => F z θ) ha_pos hb.2 (le_of_lt hb.1) hF_int)
        linarith
      linarith
    rw [hid']
    have htri : |Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
        + 6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ| := by
      have h1 := abs_add_le (Real.tan a * Ψ z a) (∫ θ in a..b, A θ)
      have h2 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ))
        (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
      have h3 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a))
        (6 * ∫ θ in a..b, Ψ z θ)
      exact le_trans h3 (le_trans (add_le_add h2 le_rfl)
        (add_le_add (add_le_add h1 le_rfl) le_rfl))
    have hfin : |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a|
          + C5 * ((Real.pi / 2) * (M + M₁) + c)
          + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
          + (1 / 2) * (QF + Real.pi / 2) + 2 * M + 6 * (M * (Real.pi / 2)) := by
      have h6 : |6 * ∫ θ in a..b, Ψ z θ| = 6 * |∫ θ in a..b, Ψ z θ| := by
        rw [abs_mul]; norm_num
      have h6b : 6 * |∫ θ in a..b, Ψ z θ| ≤ 6 * (M * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hψbd (by norm_num)
      rw [h6]
      linarith [hAbound, hderivbd, h6b]
    linarith
  -- the squeeze
  have hKlim : Tendsto (fun θ => K / Real.tan θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcos : Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := (Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.cos_pi_div_two] using h.mono_left h'
    have hsin : Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
      have h := (Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.sin_pi_div_two] using h.mono_left h'
    have h2 : Tendsto (fun θ => K * Real.cos θ / Real.sin θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 : Tendsto (fun θ => K * Real.cos θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hcos)
      have := h1.div hsin one_ne_zero
      rw [show (0 : ℝ) / 1 = 0 from by norm_num] at this
      exact this
    refine Tendsto.congr' ?_ h2
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hKnn : 0 ≤ K := by
    have hb0 : (a + Real.pi / 2) / 2 ∈ Set.Ioo a (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg _) (key _ hb0)
  have hTend : Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hKlim
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
    rw [le_div_iff₀ htanpos]
    calc ‖Ψ z θ‖ * Real.tan θ = |Real.tan θ * Ψ z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos htanpos, mul_comm]
      _ ≤ K := key θ hθ
  refine ⟨hTend, 2 * K, by linarith, ?_⟩
  -- the rate: `|Ψ z θ| ≤ K/tan θ` and `1/tan θ = cos θ/sin θ ≤ 2(π/2-θ)` on `(π/4, π/2)`
  filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
  have htanpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinhalf : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin (a := Real.pi / 6) (b := θ)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos, ha_pos, hθ.1], le_of_lt hθ.2⟩
      (by linarith [Real.pi_pos, ha_pos, hθ.1])
    rwa [Real.sin_pi_div_six] at h
  have hdiv : Real.cos θ / Real.sin θ ≤ 2 * (Real.pi / 2 - θ) := by
    have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have h1 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (by linarith [hθ.2])
    have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h2 : (1 : ℝ) ≤ 2 * Real.sin θ := by linarith
    rw [div_le_iff₀ hsinpos]
    calc Real.cos θ = Real.sin (Real.pi / 2 - θ) := hcos
      _ ≤ Real.pi / 2 - θ := h1
      _ = (Real.pi / 2 - θ) * 1 := by ring
      _ ≤ (Real.pi / 2 - θ) * (2 * Real.sin θ) := mul_le_mul_of_nonneg_left h2 ht0
      _ = 2 * (Real.pi / 2 - θ) * Real.sin θ := by ring
  have htan_eq : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hu : |Ψ z θ| ≤ K / Real.tan θ := by
    rw [le_div_iff₀ htanpos]
    calc |Ψ z θ| * Real.tan θ = |Real.tan θ| * |Ψ z θ| := by
          rw [abs_of_pos htanpos, mul_comm]
      _ = |Real.tan θ * Ψ z θ| := (abs_mul _ _).symm
      _ ≤ K := key θ hθ
  calc |Ψ z θ| ≤ K / Real.tan θ := hu
    _ = K * (Real.cos θ / Real.sin θ) := by
        rw [htan_eq]
        field_simp
    _ ≤ K * (2 * (Real.pi / 2 - θ)) := mul_le_mul_of_nonneg_left hdiv hKnn
    _ = (2 * K) * (Real.pi / 2 - θ) := by ring


/-! ## The target -/

/-- **The right-endpoint limit of the `θ`-slices of the weak class.** -/
theorem slice_tendsto_pi_half {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_F hwk
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    have h2 : (2 : ℕ) = 1 + 1 := rfl
    rw [h2, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    exact (hΨ.pth).pth
  have hmemF : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.zero_le k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hF) hwk.memF
  have hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.zero_le k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hA) hwk.memA
  have hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.zero_le k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hB) hwk.memB
  exact (sliceRightTendsto_raw_allAlpha α F Ψ hwk.eq hwk.smooth hmemF hmemA hmemB z hz).1

end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


end

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
-- ===== merged: Submission.Work.H2.WPQ.hardy_slice_Aang =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `rpow` algebra on the angular interval -/



private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The angular Hardy inequality with a one-sided limit at `0`

This is the interior replacement for the private `core` of `Work.Spaces.HardyTheta`: the value
`u 0 = 0` is replaced by the one-sided limit hypothesis `u → 0` at `0⁺`.  The proof passes
through the intervals `[ε,θ]` and lets `ε → 0⁺`, so that neither continuity nor integrability
of `u'` at the endpoint `0` is ever needed. -/


/-! ## The integrability of the weighted `θ`-derivative of the `z`-slice -/


/-! ## The one-sided angular limit of `D_z^d g` -/


/-! ## The interior identity between `Aang` and the `Btil`-integrand -/




end Work.H2.WPQ
end
