/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two finite-dimensional energy comparisons in the **open** class

This file proves the open-quadrant (`SmoothOpen`) version of the two weighted-energy
comparisons that the level-one coercivity ledger of `𝓛_Γ^T` consumes (their
`SmoothQuad`-based twins live in `Work.FTS.CoercivityFix.Coer1T.SlotsDzGam` as
`EDthW_le_EDth_Q` and `EL12z_le_Q`):

* `EDthW_EL12z_open.1`, i.e. `EDthW f ≤ EDth α f`:
  `|D_θ f·w|²_{L²} ≤ |D_θ f·w/√(sin(2θ)^γ)|²_{L²}`.  The two energies differ only by the
  angular factor `sin(2θ)^{-γ}`, which is `≥ 1` on the open angular interval (`γ = 1 + α/10 > 0`
  and `0 < sin(2θ) ≤ 1` there).  The `γ`-weighted integrand is the `(i,j) = (1,0)` mixed slot
  of `HkIntegrand α 2 f`, so `i2Mem_sq_of_le` supplies the honesty of its iterated integral from
  `SmoothOpen f` (continuity on the open quadrant) and `HkMem α 2 f` alone.

* `EDthW_EL12z_open.2`, i.e. `EL12z f ≤ 16·Ef f`: the paper's `Lemma HardyWeight` chain
  `∫(L₁₂f)²/z² ≤ 4∫(L₁₂dens)² ≤ 12∫(∫_θ f²)/z² ≤ 12|f w|²_{L²}` (`Work.Coercivity.EL12z_le`),
  whose only side condition is the joint integrability of `(f w)²` on the quadrant.  That is
  obtained here by dominating `(f w)²` a.e. by the `D_z⁰`-summand `(f w/√(sin(2θ)^η))²` of
  `HkIntegrand α 2 f`, which is jointly integrable by `joint_of_le_HkIntegrand`.

Both are proved for a merely `C^∞`-on-the-open-quadrant datum (`SmoothOpen`), which is exactly
the class reachable along the route (`RegQo α 5 (slice (JfamP ρ ε g) τ)`); the analytic
`SmoothQuad`-hypothesis of the frozen twins is *not* available there.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne
import Submission.Work.Coercivity.EL12z_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary continuity on the open quadrant -/

/-- The radial weight `w z = (1+z)²/z²` is continuous on the open quadrant. -/
theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The square of the radial weight is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

/-- The `ℋ^k`-weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  refine continuousOn_w_Q0.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-! ## The joint integrability of `(f w)²` in the open class -/

/-- **`(f w)²` is jointly integrable on the quadrant** for a datum `f` of class `C^∞` on the open
quadrant which is honestly in `ℋ²`.

The dominating function is the `D_z⁰`-summand `(f·w/√(sin(2θ)^η))²` of `HkIntegrand α 2 f`
(which is `≥ (f w)²` a.e.: off the null set `{sin(2θ) = 0}` one has
`sin(2θ)^{η/2} ∈ (0,1]`, hence `w ≤ w/√(sin(2θ)^η)`). -/
theorem integrableOn_f_sq_w_sq_open {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- the `η`-weighted dominating integrand, a summand of the `ℋ²`-integrand
  have hbig : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      ((hso.continuousOn_summand 0).pow 2)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ 0 (by norm_num))
  -- a.e. strong measurability of `(f w)²`, from its continuity on the open quadrant
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.continuousOn
      have hfun : (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
          = fun p : ℝ × ℝ => f p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 := by
        funext p; ring
      rw [hfun]
      exact (h1.pow 2).mul continuousOn_w_sq_Q0
    have h2 := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) hcont
    rwa [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h2
  -- the a.e. domination by the `η`-weighted summand
  have hle : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      ‖(f p.1 p.2 * Work.Spaces.w p.1) ^ 2‖
        ≤ ‖(f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2‖ := by
    have hmem : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
        p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
      have h := Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
      rwa [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at h
    filter_upwards [hmem] with p hp
    have hs : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.1]) (by linarith [hp.2, Real.pi_pos])
    have hs1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have heta : 0 < Work.Spaces.eta / 2 := by rw [Work.Spaces.eta]; norm_num
    have hsle : Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hs) hs1 (le_of_lt heta)
    have hspos : 0 < Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hs _
    have hw0 : 0 ≤ Work.Spaces.w p.1 := by rw [Work.Spaces.w]; positivity
    have hws : Work.Spaces.w p.1
        ≤ Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hspos]
      nlinarith [hw0, hsle]
    have h1 : |f p.1 p.2 * Work.Spaces.w p.1|
        ≤ |f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw0,
        abs_of_nonneg (div_nonneg hw0 (le_of_lt hspos))]
      exact mul_le_mul_of_nonneg_left hws (abs_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    calc (f p.1 p.2 * Work.Spaces.w p.1) ^ 2
        = |f p.1 p.2 * Work.Spaces.w p.1| ^ 2 := (sq_abs _).symm
      _ ≤ |f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (f p.1 p.2 * (Work.Spaces.w p.1
            / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_abs _
  exact hbig.norm.mono' haesm hle

/-! ## The two comparisons -/

/-- `EDthW f ≤ EDth α f`: the unweighted angular energy is dominated by the
`sin(2θ)^{-γ}`-weighted one.

`EDthW f = ∫∫ (D_θ f)² w²` is the iterated integral of `(D_θf · w)²`; its angular majorant
`(D_θf · Wt α)²` is the `(i,j) = (1,0)` mixed summand of `HkIntegrand α 2 f`, so
`i2Mem_sq_of_le` (from the open-quadrant smoothness of `f` and `f ∈ ℋ²`) makes the iterated
integral of the majorant honest, and monotonicity of the iterated integral closes the bound. -/
theorem EDthW_le_EDth_open {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f := by
  -- ## the angular majorant is honest
  have hB : Work.Coercivity.I2Mem
      (fun z θ => (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 2 hm ?_ ?_
    · exact (((hso.Dth).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    · intro z _ θ _
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ 1 0 (by norm_num) (by norm_num)
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using h
  -- ## the two energies as squared iterated `L²`-norms
  have hW : Work.Coercivity.EDthW f
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.w z) := by
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip, Work.Spaces.L2Sq]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  have hD : Work.Coercivity.EDth α f
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) := rfl
  rw [hW, hD, Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  -- ## the outer integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hB.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  -- ## the inner (angular) integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hB.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  -- ## the pointwise comparison of the two angular weights
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hg : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith
  have hge1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.rpow_neg (le_of_lt hs)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr
      (Real.rpow_le_one (le_of_lt hs) hs1 hg)
  have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hwle : Work.Spaces.w z ≤ Work.Spaces.Wt α z θ := by
    show Work.Spaces.w z ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
    calc Work.Spaces.w z = Work.Spaces.w z * 1 := (mul_one _).symm
      _ ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
          mul_le_mul_of_nonneg_left hge1 hw0
  have h1 : |Work.Spaces.Dth f z θ * Work.Spaces.w z|
      ≤ |Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (le_trans hw0 hwle)]
    exact mul_le_mul_of_nonneg_left hwle (abs_nonneg _)
  calc (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2
      = |Work.Spaces.Dth f z θ * Work.Spaces.w z| ^ 2 := (sq_abs _).symm
    _ ≤ |Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2 := sq_abs _

/-- **The open-class replacement of the two finite-dimensional inputs of the level-one
coercivity ledger**: `EDthW f ≤ EDth α f` and `EL12z f ≤ 16 Ef f`, from `SmoothOpen f`,
`f ∈ ℋ²` and the Hardy hypotheses `HardyHyp f` — no `SmoothQuad` (flatness at `z = 0`) is
needed. -/
theorem EDthW_EL12z_open {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (hHH : Work.Coercivity.HardyHyp f) :
    Work.Coercivity.EDthW f ≤ Work.Coercivity.EDth α f ∧
      Work.Coercivity.EL12z f ≤ 16 * Work.Coercivity.Ef f :=
  ⟨EDthW_le_EDth_open hα hso hm,
    Work.Coercivity.EL12z_le f hHH (integrableOn_f_sq_w_sq_open hso hm)⟩

end Work.FTS.StrongEps.EpsE4Thr
