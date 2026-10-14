import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.H2W.dzPsiSliceLimits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- **The clamped source**: `F` on `{z > 0}` and `0` elsewhere.  It agrees with `F` on the open
quadrant, and its angular moment `F_*` vanishes *for every real `z`* — for `z > 0` because `F`'s
does, for `z ≤ 0` because the integrand is `0`.  This is the form of the solvability condition
that the existence theorem consumes (the node only assumes it for `z > 0`). -/
def clampQ (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => if 0 < z then F z θ else 0

/-- `clampQ F` agrees with `F` on the open quadrant. -/
theorem clampQ_eqOn_Q0 (F : ℝ → ℝ → ℝ) :
    Set.EqOn (Function.uncurry (clampQ F)) (Function.uncurry F) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  show (if 0 < p.1 then F p.1 p.2 else 0) = F p.1 p.2
  rw [if_pos hz]

/-- The clamped source keeps the open-quadrant smoothness of `F`. -/
theorem smoothOpen_clampQ {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (clampQ F) :=
  h.congr (fun p hp => clampQ_eqOn_Q0 F hp)

/-- The angular moment of the clamped source. -/
theorem fstar_clampQ (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (clampQ F) z = if 0 < z then Work.Elliptic.Fstar F z else 0 := by
  by_cases hz : 0 < z
  · have hfun : (fun θ => clampQ F z θ * Work.Elliptic.sinCos2 θ)
        = fun θ => F z θ * Work.Elliptic.sinCos2 θ := by
      funext θ
      simp only [clampQ, if_pos hz]
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hfun, if_pos hz]
  · have hfun : (fun θ => clampQ F z θ * Work.Elliptic.sinCos2 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [clampQ, if_neg hz, zero_mul]
    rw [Work.Elliptic.Fstar, hfun, if_neg hz]
    simp

/-- The clamped source satisfies the *global* moment condition `OrthCond`. -/
theorem orthCond_clampQ {F : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) :
    Work.Elliptic.OrthCond (clampQ F) := by
  intro z
  rw [fstar_clampQ]
  by_cases hz : 0 < z
  · rw [if_pos hz]; exact h z hz
  · rw [if_neg hz]


/-- **The `ℋ⁰`-membership of the source makes the unweighted square `F²` integrable on the open
quadrant.**  The `ℋ⁰` density is `(F z θ)² · w(z)² · sin(2θ)^{-η}`; on `Q0` both weights are
`≥ 1` (`z > 0` gives `w z ≥ 1`, and `0 < sin 2θ ≤ 1` gives `sin(2θ)^{-η} ≥ 1`), and the density
is integrable on the product `Iz ×ˢ Iθ` by
`Cores.InterpBrickAux.hkDensity_prod_integrable`. -/
theorem integrableOn_sq_Q0_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 := by
  have hprod := Work.FTS.EllipticEst.Cores.InterpBrickAux.hkDensity_prod_integrable hF hsm
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨le_of_lt hz, le_of_lt hθ0, le_of_lt hθ1⟩
  have hG := hprod.integrableOn.mono_set hsub
  -- carry the product measure to `volume` on `ℝ × ℝ`
  have hme : ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)).restrict
        Work.FTS.EllipticEst.Q0 = (volume.prod volume).restrict Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.Measure.prod_restrict,
      MeasureTheory.Measure.restrict_restrict_of_subset hsub]
  change Integrable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)).restrict
        Work.FTS.EllipticEst.Q0) at hG
  rw [hme] at hG
  -- a.e. strong measurability of `F²` from the open-quadrant continuity
  have hAESM : AEStronglyMeasurable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    have hF' : AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hsm.continuousOn
    exact hF'.pow 2
  have hle : (volume.prod volume).restrict Work.FTS.EllipticEst.Q0
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [← hme]; exact MeasureTheory.Measure.restrict_le_self
  refine hG.mono' (MeasureTheory.AEStronglyMeasurable.mono_measure hAESM hle) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (Work.FTS.EllipticEst.isOpen_Q0.measurableSet)] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hsin : 0 < Real.sin (2 * p.2) := by
    have h1 : 0 < 2 * p.2 := by linarith
    have h2 : 2 * p.2 < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hsin1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
  have hσ : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    have hη : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    have hle1 : (Real.sin (2 * p.2)) ^ Work.Spaces.eta ≤ 1 :=
      Real.rpow_le_one hsin.le hsin1 hη
    have hinv : (1 : ℝ) ≤ ((Real.sin (2 * p.2)) ^ Work.Spaces.eta)⁻¹ :=
      (one_le_inv₀ (Real.rpow_pos_of_pos hsin _)).mpr hle1
    rw [Real.rpow_neg hsin.le]
    exact hinv
  have hw : 1 ≤ (Work.Spaces.w p.1) ^ 2 := by
    have h1 : 1 ≤ Work.Spaces.w p.1 := by
      rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < p.1 ^ 2)]
      nlinarith
    nlinarith
  have h2 : (0 : ℝ) ≤ (F p.1 p.2) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h2]
  have hA : (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul hw hσ (by norm_num) (le_trans zero_le_one hw)
  calc (F p.1 p.2) ^ 2 = (F p.1 p.2) ^ 2 * 1 := by ring
    _ ≤ (F p.1 p.2) ^ 2 * ((Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := mul_le_mul_of_nonneg_left hA h2
    _ = (F p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by ring


end Work.FTS.PhiStar
