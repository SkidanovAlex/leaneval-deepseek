import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-- `Iz = [0,∞)` and `(0,∞)` carry the same Lebesgue measure. -/
private theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
  (Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm

/-- **Angular AM–GM against the `ℋ⁰`-integrand.**  For `θ` in the open interval,
`w(z)² |f||g| ≤ (HkIntegrand α 0 f + HkIntegrand α 0 g)/2`; the two terms are handled
separately so that the result applies to the three pairings of the `Lzero` decomposition. -/
private theorem pair_le (α : ℝ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hp : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * |f z θ| * |g z θ|
      ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) / 2 := by
  have hamgm : |f z θ| * |g z θ| ≤ ((f z θ) ^ 2 + (g z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  calc (Work.Spaces.w z) ^ 2 * |f z θ| * |g z θ|
      = (Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (((f z θ) ^ 2 + (g z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hamgm hw2
    _ = ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2) / 2 := by ring
    _ ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) / 2 := by
        linarith [Work.FTS.EllipticEst.Dispatch.sq_weight_le_Hk (z := z) α f hp,
          Work.FTS.EllipticEst.Dispatch.sq_weight_le_Hk (z := z) α g hp]

theorem lzeroProfInt (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)) Work.Spaces.Iz := by
  -- ## the smoothness of the datum on the open quadrant
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α) hU)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  have hR : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  have hD : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := hU.Dz
  -- ## the honest `ℋ⁰`-memberships
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hmg : Work.Spaces.HkMem α 0 G := h.memG
  have hmr : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := h.memRad2
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- ## joint integrability of the four `ℋ⁰`-integrands
  have hIu := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hU hmu
  have hIg := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hG hmg
  have hIr := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hR hmr
  have hIdx := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hD hmd
  have hα5 : 0 ≤ α * (5 + α) := by nlinarith [h.hα]
  -- ## continuity of the radial weight on the quadrant
  have hw2cont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => (((1 + p.1) ^ 2) / (p.1) ^ 2) ^ 2 := by
      funext p; simp only [Work.Spaces.w]
    rw [hfun]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuous_const.add continuous_fst).continuousOn.pow 2
    · exact continuous_fst.continuousOn.pow 2
    · intro p hp; exact pow_ne_zero 2 (ne_of_gt hp.1)
  -- ## continuity on the quadrant of the decomposed `Lzero`-pairing
  have hZcont : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2 * u p.1 p.2
      + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
      + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2 * u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hG.continuousOn.mul hU.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hR.continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hD.continuousOn
    have h4 := (h2.mul hU.continuousOn).const_mul (α ^ 2)
    have h5 := (h3.mul hU.continuousOn).const_mul (α * (5 + α))
    exact (h1.add h4).add h5
  -- ## a.e. strong measurability of the (decomposed) target integrand
  have haesmφw : AEStronglyMeasurable
      (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2) Dispatch.nuFts :=
    ((hφm.comp measurable_fst).aestronglyMeasurable).mul
      (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hw2cont)
  have haesmZ : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) Dispatch.nuFts :=
    haesmφw.mul (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hZcont).norm
  -- ## the majorant (in the association produced by `Integrable.add`)
  have hMajInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + ((α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)))) Dispatch.nuFts :=
    ((hIg.add hIu).const_mul (1 / 2)).add
      (((hIr.add hIu).const_mul (α ^ 2 / 2)).add ((hIdx.add hIu).const_mul (α * (5 + α) / 2)))
  have hMajInt' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2))) Dispatch.nuFts :=
    hMajInt.congr (Filter.Eventually.of_forall fun p => by ring)
  -- ## the pointwise bound
  have hbound : ∀ᵐ p ∂Dispatch.nuFts, ‖φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|‖
      ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)) := by
    filter_upwards [Dispatch.ae_mem_Ioo_nu] with p hp
    obtain ⟨z, θ⟩ := p
    set X : ℝ := G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
      + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) with hX
    have hGterm : (Work.Spaces.w z) ^ 2 * |G z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α G u hp
    have hRterm : (Work.Spaces.w z) ^ 2 * |z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) u hp
    have hXterm : (Work.Spaces.w z) ^ 2 * |z * Work.Spaces.pz u z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α (Work.FTS.EllipticEst.H2W.Ae.grad u) u hp
    have hdec : |X| ≤ |G z θ| * |u z θ| + α ^ 2 * (|z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + (α * (5 + α)) * (|z * Work.Spaces.pz u z θ| * |u z θ|) := by
      rw [hX]
      have hAB := abs_add_le (G z θ * u z θ)
        (α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))
      have hABC := abs_add_le
        (G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))
        ((α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ))
      have h1 : |G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)|
          ≤ |G z θ * u z θ| + |α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)|
            + |(α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)| := by
        linarith [hABC, hAB]
      refine h1.trans (le_of_eq ?_)
      simp only [abs_mul, abs_of_nonneg (sq_nonneg α), abs_of_nonneg hα5]
    have hstep1 : φ z * (Work.Spaces.w z) ^ 2 * |X| ≤ (Work.Spaces.w z) ^ 2 * |X| := by
      have h : φ z * ((Work.Spaces.w z) ^ 2 * |X|) ≤ 1 * ((Work.Spaces.w z) ^ 2 * |X|) :=
        mul_le_mul_of_nonneg_right (hφ1 z)
          (mul_nonneg (sq_nonneg (Work.Spaces.w z)) (abs_nonneg X))
      linarith [h]
    have hnnφ : (0 : ℝ) ≤ φ z * (Work.Spaces.w z) ^ 2 * |X| :=
      mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg (Work.Spaces.w z))) (abs_nonneg X)
    rw [Real.norm_eq_abs, abs_of_nonneg hnnφ]
    calc φ z * (Work.Spaces.w z) ^ 2 * |X|
        ≤ (Work.Spaces.w z) ^ 2 * |X| := hstep1
      _ ≤ (Work.Spaces.w z) ^ 2
          * (|G z θ| * |u z θ| + α ^ 2 * (|z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
            + (α * (5 + α)) * (|z * Work.Spaces.pz u z θ| * |u z θ|)) :=
          mul_le_mul_of_nonneg_left hdec (sq_nonneg (Work.Spaces.w z))
      _ = (Work.Spaces.w z) ^ 2 * |G z θ| * |u z θ|
          + α ^ 2 * ((Work.Spaces.w z) ^ 2 * |z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + (α * (5 + α))
            * ((Work.Spaces.w z) ^ 2 * |z * Work.Spaces.pz u z θ| * |u z θ|) := by ring
      _ ≤ (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ) / 2
          + α ^ 2 * ((Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) / 2)
          + (α * (5 + α))
            * ((Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) / 2) := by
          have h1 := mul_le_mul_of_nonneg_left hRterm (sq_nonneg α)
          have h2 := mul_le_mul_of_nonneg_left hXterm hα5
          linarith [hGterm, h1, h2]
      _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ)
          + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)
          + ((α * (5 + α) / 2)
            * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)) := by ring
  -- ## joint integrability of the decomposed integrand
  have hIntDec : MeasureTheory.Integrable (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) Dispatch.nuFts :=
    hMajInt'.mono' haesmZ hbound
  -- ## the a.e. identity `Lzero u = G + α²z²∂_z²u + α(5+α)z∂_zu` on the quadrant
  have hae : (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
        * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|)
      =ᵐ[Dispatch.nuFts] (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
        * |G p.1 p.2 * u p.1 p.2
          + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
          + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) := by
    filter_upwards [Dispatch.ae_mem_Ioi_nu, Dispatch.ae_mem_Ioo_nu] with p hpz hpθ
    obtain ⟨z, θ⟩ := p
    have heq := h.eq z hpz θ hpθ.1 hpθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hL : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    have hinner : (G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ)) * u z θ
        = G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) := by ring
    rw [hL, hinner]
  have hInt : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|)) Dispatch.nuFts :=
    hIntDec.congr hae.symm
  -- ## integrability of the outer `z`-profile integral by Fubini
  have hIntIz : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq_Ioi]
    exact hInt
  refine hIntIz.integral_prod_left.congr (Filter.Eventually.of_forall fun z => ?_)
  show (∫ θ in Work.Spaces.Iθ, φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|)
      = φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)
  rw [MeasureTheory.integral_const_mul]

end

end Work.FTS.EllipticEst.Prop.CutEnergyAux
