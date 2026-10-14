import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
-- ===== merged: Submission.Work.ConstructionInstance.continuousOn_selfSimVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.unusedVariables false

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-! ## Continuity of the cylindrical coordinates -/

theorem continuous_rho : Continuous (Work.Cyl.rho : R3 → ℝ) := by
  have h : (Work.Cyl.rho : R3 → ℝ) = fun x => ‖x‖ := funext Work.Cyl.rho_eq_norm
  rw [h]
  exact continuous_norm

theorem continuous_radial : Continuous (Work.Cyl.radial : R3 → ℝ) := by
  have h : (Work.Cyl.radial : R3 → ℝ) = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    funext x
    rw [Work.Cyl.radial, Work.Cyl.radSq]
  rw [h]
  fun_prop

/-- `θ = arctan (x₃/r)` is continuous off the symmetry axis. -/
theorem continuousAt_theta_of_radial_ne_zero {x : R3} (hx : Work.Cyl.radial x ≠ 0) :
    ContinuousAt Work.Cyl.theta x := by
  have h1 : ContinuousAt (fun y : R3 => Work.Cyl.axial y / Work.Cyl.radial y) x := by
    refine ContinuousAt.div ?_ continuous_radial.continuousAt hx
    show ContinuousAt (fun y : R3 => y 2) x
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).continuousAt
  have h2 : ContinuousAt (fun y : R3 => Real.arctan (Work.Cyl.axial y / Work.Cyl.radial y)) x :=
    (Real.continuous_arctan.continuousAt).comp h1
  exact h2

/-! ## The profile at the exceptional angle `π/2` -/

theorem Fstar_pi_div_two {p : ℝ} (hp : p ≠ 0) (z : ℝ) :
    Work.Construction.Fstar p z (Real.pi / 2) = 0 := by
  have hbase : Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  rw [Work.Construction.Fstar, Work.Spaces.Gam, hbase,
    Real.zero_rpow (by positivity : p / 3 ≠ 0)]
  ring

theorem profile_pi_div_two {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (z : ℝ) :
    profile p g z (Real.pi / 2) = 0 := by
  rw [profile_of_nonneg (le_of_lt (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)),
    Fstar_pi_div_two hp z, hvt.2 z, add_zero]

/-! ## The corrected angle `θ ⟶ psi` and the parity factor -/

/-- The sign of the axial coordinate (`= 1` on the closed half space `x₃ ≥ 0`).  It is bounded
by `1` everywhere and locally constant off the plane `x₃ = 0`, which is all the axis argument
needs: the profile factor vanishes there. -/
def sgnThird (x : R3) : ℝ := if 0 ≤ x 2 then 1 else -1

theorem abs_sgnThird_le_one (x : R3) : |sgnThird x| ≤ 1 := by
  rw [sgnThird]
  split <;> norm_num

/-- `psi` is the corrected angle: it agrees with `|θ|` off the axis and equals `π/2` on it,
where the profile vanishes.  Hence the profile at `θ x` is the parity factor `sgnThird x` times
the profile at `psi x`. -/
theorem profile_theta_eq_sgnThird_mul {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (z : ℝ) (x : R3) :
    profile p g z (Work.Cyl.theta x) = sgnThird x * profile p g z (psi x) := by
  by_cases h : Work.Cyl.radial x = 0
  · have hθ : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, h, div_zero, Real.arctan_zero]
    have hψ : psi x = Real.pi / 2 := by rw [psi, h, zero_div, Real.arccos_zero]
    rw [hθ, hψ, profile_zero hp hvt.1, profile_pi_div_two hp hvt z, mul_zero]
  · have hpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm h)
    rw [psi_eq_abs_theta hpos]
    rcases lt_trichotomy (x 2) 0 with hlt | heq | hgt
    · have hy : x 2 / Work.Cyl.radial x < 0 := div_neg_of_neg_of_pos hlt hpos
      have hθneg : Work.Cyl.theta x < 0 := by
        have h1 : 0 < Real.arctan (-(x 2 / Work.Cyl.radial x)) := Real.arctan_pos.mpr (neg_pos.mpr hy)
        rw [Real.arctan_neg] at h1
        have h2 : Work.Cyl.theta x = Real.arctan (x 2 / Work.Cyl.radial x) := by
          rw [Work.Cyl.theta, Work.Cyl.axial]
        rw [h2]
        linarith
      rw [profile_of_neg (not_le.mpr hθneg), abs_of_neg hθneg,
        profile_of_nonneg (neg_nonneg.mpr hθneg.le), sgnThird, ite_eq_right (not_le.mpr hlt)]
      ring
    · have hθ0 : Work.Cyl.theta x = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial, heq, zero_div, Real.arctan_zero]
      rw [hθ0, abs_zero, profile_zero hp hvt.1, sgnThird, ite_eq_left (le_of_eq heq.symm)]
      ring
    · have hy : 0 < x 2 / Work.Cyl.radial x := div_pos hgt hpos
      have hθpos : 0 < Work.Cyl.theta x := by
        rw [Work.Cyl.theta, Work.Cyl.axial]
        exact Real.arctan_pos.mpr hy
      rw [abs_of_pos hθpos, sgnThird, ite_eq_left hgt.le, one_mul]

/-! ## A bounded factor times a vanishing continuous factor -/

/-- If `f` is continuous (within `s`) at `a` with `f a = 0`, and `g` is bounded by `1` on `s`,
then `f • g` is continuous (within `s`) at `a` — the point being that `g` itself may be
discontinuous there, as is the angular frame vector `e_θ` on the axis. -/
theorem ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one {α : Type*} [TopologicalSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → ℝ} {g : α → E}
    {s : Set α} {a : α} (hf : ContinuousWithinAt f s a) (hf0 : f a = 0)
    (hg : ∀ x ∈ s, ‖g x‖ ≤ 1) :
    ContinuousWithinAt (fun x => f x • g x) s a := by
  rw [ContinuousWithinAt, hf0, zero_smul]
  refine squeeze_zero_norm' (a := fun x => ‖f x‖) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    calc ‖f x • g x‖ = ‖f x‖ * ‖g x‖ := norm_smul _ _
      _ ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (hg x hx) (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  · have h : Tendsto f (𝓝[s] a) (𝓝 0) := by simpa [hf0] using hf.tendsto
    simpa using h.norm

theorem continuousOn_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hsmooth : Work.Spaces.SmoothNbhd g) {L : ℝ} (hL : 0 < L)
    {lam : ℝ → ℝ} {T : ℝ} (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {R : ℝ} (hR : 0 ≤ R) :
    ContinuousOn (Function.uncurry (Work.ConstructionInstance.selfSimVort p g L lam))
      (Work.StabilityFar.coreRegion R ×ˢ Work.ConstructionInstance.preWindow T) := by
  set U : Set (R3 × ℝ) :=
    Work.StabilityFar.coreRegion R ×ˢ Work.ConstructionInstance.preWindow T with hU
  intro q₀ hq₀
  rw [hU] at hq₀
  have hlamq : 0 < lam q₀.2 := hlam q₀.2 hq₀.2
  have hlamc : ContinuousAt lam q₀.2 := (hlamdif q₀.2 hq₀.2).continuousAt
  -- the four factors: `λ⁻¹`, `χ`, the profile and the frame vector
  have hA : ContinuousWithinAt (fun q : R3 × ℝ => (lam q.2)⁻¹) U q₀ :=
    ((hlamc.comp continuous_snd.continuousAt).inv₀ (ne_of_gt hlamq)).continuousWithinAt
  have hB : ContinuousWithinAt (fun q : R3 × ℝ => Work.Stability.chi (Work.Cyl.rho q.1 / L)) U q₀ :=
    ((Work.Stability.chi_continuous.continuousAt).comp
      ((continuous_rho.comp continuous_fst).div_const L).continuousAt).continuousWithinAt
  -- the self-similar variable `ρ^p/λ` is continuous
  have hzc : ContinuousAt (fun q : R3 × ℝ => Work.Cyl.rho q.1 ^ p / lam q.2) q₀ :=
    (((continuous_rho.comp continuous_fst).continuousAt).rpow_const (Or.inr hp.le)).div
      (hlamc.comp continuous_snd.continuousAt) (ne_of_gt hlamq)
  -- the profile factor `profile p g (ρ^p/λ) (θ x)`
  have hCcont : ContinuousWithinAt
      (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
      U q₀ := by
    have hzp : -1 < Work.Cyl.rho q₀.1 ^ p / lam q₀.2 := by
      have h0 : 0 ≤ Work.Cyl.rho q₀.1 ^ p / lam q₀.2 :=
        div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg q₀.1) p) hlamq.le
      linarith
    rcases eq_or_ne (Work.Cyl.radial q₀.1) 0 with hr0 | hr0
    · rcases eq_or_ne q₀.1 0 with hx0 | hx0
      · -- the origin: the profile vanishes linearly in the self-similar variable
        obtain ⟨K, _hK0, hK⟩ := exists_profile_abs_le_mul_z hp hp1 hquad0 hsmooth
        have hztend : Tendsto (fun q : R3 × ℝ => Work.Cyl.rho q.1 ^ p / lam q.2)
            (𝓝[U] q₀) (𝓝 0) := by
          have hval : Work.Cyl.rho q₀.1 ^ p / lam q₀.2 = 0 := by
            rw [hx0]
            simp [Work.Cyl.rho_eq_norm, Real.zero_rpow hp.ne']
          have hle : 𝓝[U] q₀ ≤ 𝓝 q₀ := nhdsWithin_le_nhds
          have h := hzc.tendsto.mono_left hle
          rwa [hval] at h
        have hsmall : ∀ᶠ q in 𝓝[U] q₀, Work.Cyl.rho q.1 ^ p / lam q.2 < 1 :=
          hztend.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
        have hbound : ∀ᶠ q in 𝓝[U] q₀,
            ‖profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)‖
              ≤ K * (Work.Cyl.rho q.1 ^ p / lam q.2) := by
          filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hq1
          rw [hU] at hq
          have hq0 : 0 ≤ Work.Cyl.rho q.1 ^ p / lam q.2 :=
            div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg q.1) p) (hlam q.2 hq.2).le
          have hθle : |Work.Cyl.theta q.1| ≤ Real.pi / 2 := by
            rw [abs_le]
            exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
              le_of_lt (Real.arctan_lt_pi_div_two _)⟩
          rw [Real.norm_eq_abs]
          exact hK _ ⟨hq0, le_of_lt hq1⟩ _ hθle
        have hupper : Tendsto (fun q : R3 × ℝ => K * (Work.Cyl.rho q.1 ^ p / lam q.2))
            (𝓝[U] q₀) (𝓝 0) := by
          simpa using hztend.const_mul K
        have hCtend : Tendsto
            (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
            (𝓝[U] q₀) (𝓝 0) := squeeze_zero_norm' hbound hupper
        have hC0 : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (Work.Cyl.theta q₀.1) = 0 := by
          rw [hx0]
          have hθ : Work.Cyl.theta (0 : R3) = 0 := by
            simp [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq]
          rw [hθ, profile_zero hp.ne' hvt.1]
        rw [ContinuousWithinAt, hC0]
        exact hCtend
      · -- the axis, away from the origin: `θ` is replaced by the continuous corrected angle
        -- `psi` (they differ only on the axis, where the profile vanishes)
        have hψmem : psi q₀.1 = Real.pi / 2 := by
          rw [psi, hr0, zero_div, Real.arccos_zero]
        have hval : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (psi q₀.1) = 0 := by
          rw [hψmem]
          exact profile_pi_div_two hp.ne' hvt _
        have hψc : ContinuousAt
            (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1)) q₀ := by
          have hψ : ContinuousAt (fun q : R3 × ℝ => psi q.1) q₀ :=
            (continuousAt_psi hx0).comp continuous_fst.continuousAt
          have hpair : ContinuousAt
              (fun q : R3 × ℝ => (Work.Cyl.rho q.1 ^ p / lam q.2, psi q.1)) q₀ :=
            hzc.prodMk hψ
          have hprof : ContinuousAt (Function.uncurry (profile p g))
              (Work.Cyl.rho q₀.1 ^ p / lam q₀.2, psi q₀.1) := by
            rw [hψmem]
            exact profile_continuousAt_pi_half hp hvt hsmooth hzp
          exact hprof.comp (f := fun q : R3 × ℝ =>
            (Work.Cyl.rho q.1 ^ p / lam q.2, psi q.1)) hpair
        have hsm : ContinuousWithinAt
            (fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) • sgnThird q.1) U q₀ :=
          ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one hψc.continuousWithinAt hval
            (fun q _ => abs_sgnThird_le_one q.1)
        have hfun : (fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
            = fun q : R3 × ℝ =>
              sgnThird q.1 * profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) :=
          funext fun q => profile_theta_eq_sgnThird_mul hp.ne' hvt _ _
        have hfun' : (fun q : R3 × ℝ =>
              sgnThird q.1 * profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1))
            = fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) • sgnThird q.1 := by
          funext q
          rw [smul_eq_mul, mul_comm]
        rw [hfun, hfun']
        exact hsm
    · -- off the axis: a composition of continuous maps
      have hθc : ContinuousAt (fun q : R3 × ℝ => Work.Cyl.theta q.1) q₀ :=
        (continuousAt_theta_of_radial_ne_zero hr0).comp continuous_fst.continuousAt
      have hpair : ContinuousAt
          (fun q : R3 × ℝ => (Work.Cyl.rho q.1 ^ p / lam q.2, Work.Cyl.theta q.1)) q₀ :=
        hzc.prodMk hθc
      have hθmem : Work.Cyl.theta q₀.1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
      have hprof : ContinuousAt (Function.uncurry (profile p g))
          (Work.Cyl.rho q₀.1 ^ p / lam q₀.2, Work.Cyl.theta q₀.1) := by
        rcases eq_or_ne (Work.Cyl.theta q₀.1) 0 with h0 | h0
        · rw [h0]
          exact profile_continuousAt_zero hp hvt hsmooth hzp
        · exact (contDiffAt_uncurry_profile (Work.Stability.SmoothFar.of_smoothNbhd hsmooth)
            hzp hθmem h0).continuousAt
      exact (hprof.comp (f := fun q : R3 × ℝ =>
        (Work.Cyl.rho q.1 ^ p / lam q.2, Work.Cyl.theta q.1)) hpair).continuousWithinAt
  -- the frame vector: continuous off the axis, and multiplied by the vanishing profile factor
  -- on the axis (where `e_θ` jumps)
  have hCV : ContinuousWithinAt (fun q : R3 × ℝ =>
      (profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) • Work.Cyl.eTheta q.1)
      U q₀ := by
    rcases eq_or_ne (Work.Cyl.radial q₀.1) 0 with hr0 | hr0
    · have hθ0 : Work.Cyl.theta q₀.1 = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial, hr0, div_zero, Real.arctan_zero]
      have hC0 : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (Work.Cyl.theta q₀.1) = 0 := by
        rw [hθ0, profile_zero hp.ne' hvt.1]
      exact ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one hCcont hC0
        (fun q _ => norm_eTheta_le_one q.1)
    · have hVc : ContinuousWithinAt (fun q : R3 × ℝ => Work.Cyl.eTheta q.1) U q₀ :=
        ((continuousAt_eTheta_of_radial_ne_zero hr0).comp
          continuous_fst.continuousAt).continuousWithinAt
      exact hCcont.smul hVc
  have hF : ContinuousWithinAt (fun q : R3 × ℝ => (lam q.2)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho q.1 / L) •
        ((profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) •
          Work.Cyl.eTheta q.1))) U q₀ :=
    hA.smul (hB.smul hCV)
  have hgoal : (Function.uncurry (selfSimVort p g L lam)) = fun q : R3 × ℝ => (lam q.2)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho q.1 / L) •
        ((profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) •
          Work.Cyl.eTheta q.1)) := by
    funext q
    show selfSimVort p g L lam q.1 q.2 = _
    simp only [selfSimVort, omegaSz]
  rw [hgoal]
  exact hF

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.holder_omegaStar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## Elementary geometric and `rpow` estimates -/

/-- `|x₂ - y₂| ≤ ‖x - y‖`. -/
lemma abs_ax_sub_le (x y : R3) : |x 2 - y 2| ≤ ‖x - y‖ := by
  have h1 : ‖x - y‖ ^ 2 = (x 2 - y 2) ^ 2 + ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_eq]
    simp only [PiLp.sub_apply]
    ring
  nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1), norm_nonneg (x - y),
    sq_abs (x 2 - y 2)]

/-- `d r^{β-1} ≤ 2^{β-1} d^β` when `2d ≤ r`, `β ∈ (0,1]`, `d > 0`. -/
lemma mul_rpow_sub_le {β d r : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hd : 0 < d) (hr : 2 * d ≤ r) :
    d * r ^ (β - 1) ≤ 2 ^ (β - 1) * d ^ β := by
  have h1 : r ^ (β - 1) ≤ (2 * d) ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
  have h2 : (2 * d) ^ (β - 1) = 2 ^ (β - 1) * d ^ (β - 1) :=
    Real.mul_rpow (by norm_num) hd.le
  have h3 : d * d ^ (β - 1) = d ^ β := by
    have h := Real.rpow_add hd (β - 1) 1
    rw [show β - 1 + 1 = β by ring, Real.rpow_one] at h
    rw [h, mul_comm]
  calc d * r ^ (β - 1) ≤ d * (2 * d) ^ (β - 1) := mul_le_mul_of_nonneg_left h1 hd.le
    _ = d * (2 ^ (β - 1) * d ^ (β - 1)) := by rw [h2]
    _ = 2 ^ (β - 1) * (d * d ^ (β - 1)) := by ring
    _ = 2 ^ (β - 1) * d ^ β := by rw [h3]

/-- **The amplitude-weighted angular difference is `β`-Hölder** (for `‖x - y‖ ≤ 1`):
`A0 β x · ‖e_θ x - e_θ y‖ ≤ 2^{2β+2} ‖x - y‖^β`.  The case distinction is
`‖x - y‖ ≤ r x / 2` (where `eTheta_dist_le` gives `√2 d / min(r x, r y) ≤ 2√2 d / r x` and
`A0 β x ≤ 2 r x^β`) against `‖x - y‖ > r x / 2` (where `‖e_θ‖ ≤ 1` and `A0 β x ≤ 2 r x^{2β}`). -/
lemma A0_mul_eTheta_sub_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x y : R3}
    (hd : ‖x - y‖ ≤ 1) :
    A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by
  by_cases hxy : x = y
  · subst hxy
    have h0 : ‖x - x‖ ^ β = 0 := by
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hβ)]
    rw [sub_self, norm_zero, mul_zero, h0, mul_zero]
  rcases eq_or_ne (Work.Cyl.radial x) 0 with hrx0 | hrx0
  · rw [A0_eq_zero_of_radial_eq_zero β hβ hrx0, zero_mul]; positivity
  · have hrxp : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hrx0)
    have hdn : 0 < ‖x - y‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hxy
    by_cases hd2 : ‖x - y‖ ≤ Work.Cyl.radial x / 2
    · -- sub-case 1: `d ≤ r x / 2`
      have hry : 0 < Work.Cyl.radial y := by
        have h := (abs_le.mp (radial_dist_le x y)).2
        linarith
      have hmin : Work.Cyl.radial x / 2 ≤ min (Work.Cyl.radial x) (Work.Cyl.radial y) := by
        have h := (abs_le.mp (radial_dist_le x y)).2
        exact le_min (by linarith) (by linarith)
      have hE1 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x := by
        have h1 := eTheta_dist_le x y hrxp hry
        have h2 : Real.sqrt 2 * ‖x - y‖ / min (Work.Cyl.radial x) (Work.Cyl.radial y)
            ≤ Real.sqrt 2 * ‖x - y‖ / (Work.Cyl.radial x / 2) := by
          rw [div_le_div_iff_of_pos_left (by positivity) (lt_min hrxp hry) (by positivity)]
          exact hmin
        have h2' : Real.sqrt 2 * ‖x - y‖ / (Work.Cyl.radial x / 2)
            = 2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x := by
          field_simp
        linarith [h2.trans_eq h2']
      have hA : A0 β x ≤ 2 * (Work.Cyl.radial x) ^ β := A0_le_rpow β hβ x
      have heq : (2 * (Work.Cyl.radial x) ^ β) * (2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x)
          = 4 * Real.sqrt 2 * (‖x - y‖ * (Work.Cyl.radial x) ^ (β - 1)) := by
        rw [Real.rpow_sub hrxp, Real.rpow_one]
        field_simp
        ring
      have hr2 : 2 * ‖x - y‖ ≤ Work.Cyl.radial x := by linarith
      have hstep := mul_rpow_sub_le hβ hβ1 hdn hr2
      have h5 : 4 * Real.sqrt 2 * (2 : ℝ) ^ (β - 1) ≤ (2 : ℝ) ^ (2 * β + 2) := by
        have h3 : 4 * Real.sqrt 2 ≤ (8 : ℝ) := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have h4 : 8 * (2 : ℝ) ^ (β - 1) = (2 : ℝ) ^ (β + 2) := by
          rw [show β + 2 = 3 + (β - 1) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          norm_num
        have h6 : (2 : ℝ) ^ (β + 2) ≤ (2 : ℝ) ^ (2 * β + 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (β - 1)]
      calc A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ (2 * (Work.Cyl.radial x) ^ β) * (2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x) :=
            mul_le_mul hA hE1 (norm_nonneg _) (by positivity)
        _ = 4 * Real.sqrt 2 * (‖x - y‖ * (Work.Cyl.radial x) ^ (β - 1)) := heq
        _ ≤ 4 * Real.sqrt 2 * ((2 : ℝ) ^ (β - 1) * ‖x - y‖ ^ β) := by
            have hs := Real.sqrt_nonneg 2
            have hdβ := Real.rpow_nonneg hdn.le β
            nlinarith [hstep]
        _ ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by
            have hdβ := Real.rpow_nonneg hdn.le β
            nlinarith [h5]
    · -- sub-case 2: `d > r x / 2`
      have hE2 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ 2 := eTheta_norm_sub_le_two x y
      have hA : A0 β x ≤ 2 * (Work.Cyl.radial x) ^ (2 * β) := A0_le_rpow2 β hβ x
      have hp : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 4 * (Work.Cyl.radial x) ^ (2 * β) := by
        have h0 := A0_nonneg β x
        have h1 : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ A0 β x * 2 :=
          mul_le_mul_of_nonneg_left hE2 h0
        nlinarith [hA, h1]
      have hr2 : Work.Cyl.radial x ≤ 2 * ‖x - y‖ := by
        have := lt_of_not_ge hd2
        linarith
      have hs : (Work.Cyl.radial x) ^ (2 * β) ≤ (2 * ‖x - y‖) ^ (2 * β) :=
        Real.rpow_le_rpow (Work.Cyl.radial_nonneg x) hr2 (by linarith)
      have hs2 : (2 * ‖x - y‖) ^ (2 * β) = (2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ (2 * β) :=
        Real.mul_rpow (by norm_num) (norm_nonneg _)
      have hdβ : ‖x - y‖ ^ (2 * β) ≤ ‖x - y‖ ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hdn hd (by linarith)
      have hconst : 4 * (2 : ℝ) ^ (2 * β) = (2 : ℝ) ^ (2 * β + 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (2 * β) 2]
        norm_num
        ring
      calc A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 4 * (Work.Cyl.radial x) ^ (2 * β) := hp
        _ ≤ 4 * ((2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ (2 * β)) := by
            have h2β := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β)
            nlinarith [hs, hs2]
        _ ≤ 4 * ((2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ β) := by
            have h2β := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β)
            have hb := Real.rpow_nonneg hdn.le β
            nlinarith [hdβ]
        _ = (4 * (2 : ℝ) ^ (2 * β)) * ‖x - y‖ ^ β := by ring
        _ = (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by rw [hconst]

/-- `|Aom β x - Aom β y| ≤ (C + 4) ‖x - y‖^β` whenever `A0` is `β`-Hölder with constant `C`.
Because `|cSign| ≤ 1` and `cSign` takes one value on `x₂ ≥ 0` and another on `x₂ < 0`, the only
extra term appears when the two points straddle the plane `x₂ = 0`; then `|x₂|, |y₂| ≤ ‖x-y‖`
and `A0 β y ≤ 2 |y₂|^β` closes the estimate with `4 ‖x-y‖^β`. -/
lemma Aom_sub_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {C : NNReal}
    (hC : ∀ x y : R3, |A0 β x - A0 β y| ≤ (C : ℝ) * ‖x - y‖ ^ β) (x y : R3) :
    |Aom β x - Aom β y| ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := by
  have hcx : |cSign β (x 2)| ≤ 1 := abs_cSign_le_one β (x 2)
  have hcy : |cSign β (y 2)| ≤ 1 := abs_cSign_le_one β (y 2)
  have hd : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  have hsplit : cSign β (x 2) * A0 β x - cSign β (y 2) * A0 β y
      = cSign β (x 2) * (A0 β x - A0 β y) + (cSign β (x 2) - cSign β (y 2)) * A0 β y := by
    ring
  rw [Aom, Aom, hsplit]
  by_cases hsign : cSign β (x 2) = cSign β (y 2)
  · rw [sub_eq_zero.mpr hsign, zero_mul, add_zero]
    calc |cSign β (x 2) * (A0 β x - A0 β y)|
        = |cSign β (x 2)| * |A0 β x - A0 β y| := abs_mul _ _
      _ ≤ 1 * ((C : ℝ) * ‖x - y‖ ^ β) :=
          mul_le_mul hcx (hC x y) (abs_nonneg _) (by norm_num)
      _ ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := by
          have hCc : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
          nlinarith
  · have h2 : |A0 β y| ≤ 2 * ‖x - y‖ ^ β := by
      have hA := A0_le_ax β hβ y
      have hz : |y 2| ≤ ‖x - y‖ := by
        have hxy2 : |x 2 - y 2| ≤ ‖x - y‖ := abs_ax_sub_le x y
        by_cases hy2 : 0 ≤ y 2
        · have hx : x 2 < 0 := by
            by_contra hx
            exact hsign (by rw [cSign, if_pos (not_lt.mp hx), cSign, if_pos hy2])
          calc |y 2| = y 2 := abs_of_nonneg hy2
            _ ≤ y 2 - x 2 := by linarith
            _ = -(x 2 - y 2) := by ring
            _ ≤ |x 2 - y 2| := neg_le_abs _
            _ ≤ ‖x - y‖ := hxy2
        · have hy : y 2 < 0 := lt_of_not_ge hy2
          have hx : 0 ≤ x 2 := by
            by_contra hx
            exact hsign (by rw [cSign, if_neg hx, cSign, if_neg hy2])
          calc |y 2| = -y 2 := abs_of_neg hy
            _ ≤ x 2 - y 2 := by linarith
            _ ≤ |x 2 - y 2| := le_abs_self _
            _ ≤ ‖x - y‖ := hxy2
      calc |A0 β y| = A0 β y := abs_of_nonneg (A0_nonneg β y)
        _ ≤ 2 * |y 2| ^ β := hA
        _ ≤ 2 * ‖x - y‖ ^ β := by
            have h := Real.rpow_le_rpow (abs_nonneg _) hz hβ.le
            linarith
    have h4 : |cSign β (x 2) - cSign β (y 2)| ≤ 2 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [neg_abs_le (cSign β (x 2)), le_abs_self (cSign β (x 2)),
        neg_abs_le (cSign β (y 2)), le_abs_self (cSign β (y 2))]
    have h5 : |cSign β (x 2)| * |A0 β x - A0 β y| ≤ (C : ℝ) * ‖x - y‖ ^ β := by
      calc |cSign β (x 2)| * |A0 β x - A0 β y| ≤ 1 * ((C : ℝ) * ‖x - y‖ ^ β) :=
            mul_le_mul hcx (hC x y) (abs_nonneg _) (by norm_num)
        _ = (C : ℝ) * ‖x - y‖ ^ β := one_mul _
    have h6 : |cSign β (x 2) - cSign β (y 2)| * |A0 β y| ≤ 2 * (2 * ‖x - y‖ ^ β) :=
      mul_le_mul h4 h2 (abs_nonneg _) (by norm_num)
    have hab : |cSign β (x 2) * (A0 β x - A0 β y) + (cSign β (x 2) - cSign β (y 2)) * A0 β y|
        ≤ |cSign β (x 2)| * |A0 β x - A0 β y|
          + |cSign β (x 2) - cSign β (y 2)| * |A0 β y| := by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul]
    linarith [hab, h5, h6]

/-! ## The Hölder estimate -/

theorem holder_omegaStar {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Holder ⟨β, hβ.le⟩ (Work.ConstructionInstance.omegaStar β) := by
  obtain ⟨C, hC⟩ := A0_holder hβ hβ1
  set K : ℝ := (C : ℝ) + (2 : ℝ) ^ (2 * β + 2) + 4 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨NNReal.mk K hK0, ?_⟩
  refine holder_of_norm_le (βr := β) rfl hβ.le ?_
  intro x y
  change ‖Work.ConstructionInstance.omegaStar β x - Work.ConstructionInstance.omegaStar β y‖
    ≤ K * ‖x - y‖ ^ β
  have hdβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  by_cases hd1 : ‖x - y‖ ≤ 1
  · -- near case: the two `β`-Hölder pieces
    rw [omegaStar_eq_Aom β hβ x, omegaStar_eq_Aom β hβ y]
    have hdec : Aom β x • Work.Cyl.eTheta x - Aom β y • Work.Cyl.eTheta y
        = Aom β x • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)
          + (Aom β x - Aom β y) • Work.Cyl.eTheta y := by
      rw [smul_sub, sub_smul]; abel
    rw [hdec]
    have h1 : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := A0_mul_eTheta_sub_le hβ hβ1 hd1
    have h2 : |Aom β x - Aom β y| ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := Aom_sub_le hβ hβ1 hC x y
    have ha : ‖Aom β x • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_Aom_le_A0 β x) (norm_nonneg _)
    have hb : ‖(Aom β x - Aom β y) • Work.Cyl.eTheta y‖ ≤ |Aom β x - Aom β y| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |Aom β x - Aom β y| * ‖Work.Cyl.eTheta y‖ ≤ |Aom β x - Aom β y| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one y) (abs_nonneg _)
        _ = |Aom β x - Aom β y| := mul_one _
    refine le_trans (norm_add_le _ _) ?_
    rw [hK]
    nlinarith [ha, hb, h1, h2, hdβ]
  · -- far case: both amplitudes are below `1/2`
    have hd0 : 1 ≤ ‖x - y‖ := le_of_lt (lt_of_not_ge hd1)
    have hpow : (1 : ℝ) ≤ ‖x - y‖ ^ β := Real.one_le_rpow hd0 (le_of_lt hβ)
    have hax : ‖Work.ConstructionInstance.omegaStar β x‖ ≤ A0 β x := by
      rw [omegaStar_eq_Aom β hβ x, norm_smul, Real.norm_eq_abs]
      calc |Aom β x| * ‖Work.Cyl.eTheta x‖ ≤ |Aom β x| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
        _ = |Aom β x| := mul_one _
        _ ≤ A0 β x := abs_Aom_le_A0 β x
    have hay : ‖Work.ConstructionInstance.omegaStar β y‖ ≤ A0 β y := by
      rw [omegaStar_eq_Aom β hβ y, norm_smul, Real.norm_eq_abs]
      calc |Aom β y| * ‖Work.Cyl.eTheta y‖ ≤ |Aom β y| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one y) (abs_nonneg _)
        _ = |Aom β y| := mul_one _
        _ ≤ A0 β y := abs_Aom_le_A0 β y
    have hhalff : A0 β x + A0 β y ≤ 1 := by
      have h1 := A0_le_half β hβ x
      have h2 := A0_le_half β hβ y
      linarith
    rw [hK]
    have h1 := C.coe_nonneg
    have h2 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β + 2)
    calc ‖Work.ConstructionInstance.omegaStar β x - Work.ConstructionInstance.omegaStar β y‖
        ≤ A0 β x + A0 β y := le_trans (norm_sub_le _ _) (add_le_add hax hay)
      _ ≤ 1 := hhalff
      _ ≤ ‖x - y‖ ^ β := hpow
      _ ≤ ((C : ℝ) + (2 : ℝ) ^ (2 * β + 2) + 4) * ‖x - y‖ ^ β := by
          nlinarith [hdβ, hpow, h2]

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.timeHolderOnBall_selfSimVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

/-- `window S = [-1, S+1]` is contained in `preWindow T = (-2, T)` as soon as `S + 1 < T`.

All the `λ̄`-data of the construction (`hlam`, `hlamdif`, `hlamd`) is stated on the half-window
`preWindow T = (-2,T)`, whereas `TimeHolderOnBall` is about the (physical) window
`window S = [-1,S+1]`; this is the containment that reconciles the two. -/
theorem window_subset_preWindow {S T : ℝ} (hST : S + 1 < T) :
    Work.StabilityFar.window S ⊆ preWindow T := by
  intro t ht
  rw [Work.StabilityFar.window] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **A uniform positive lower bound for `λ̄` on the window.**

The hypotheses are exactly the `λ̄`-fields of the construction: `λ̄` is positive on
`preWindow T = (-2,T)` and differentiable (hence continuous) there.  Since
`window S = [-1,S+1]` is compact and contained in `preWindow T` (as `S + 1 < T`), the continuous
function `λ̄` attains its minimum on the window, and that minimum is positive.

This is what converts the *weighted* box `λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` of
`bddDt_selfSimVort` into an unweighted bound on the window. -/
theorem lam_pos_le_on_window {lam : ℝ → ℝ} {T S : ℝ} (hS : 0 < S) (hST : S + 1 < T)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Work.StabilityFar.window S, m ≤ lam t := by
  have hsub := window_subset_preWindow hST
  -- `λ̄` is continuous on the open half-window, hence on the compact window
  have hcont : ContinuousOn lam (preWindow T) :=
    fun t ht => (hlamdif t ht).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn lam (Work.StabilityFar.window S) := hcont.mono hsub
  have hne : (Work.StabilityFar.window S).Nonempty :=
    ⟨-1, by rw [Work.StabilityFar.window]; exact ⟨le_rfl, by linarith⟩⟩
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont'
  exact ⟨lam a, hlam a (hsub ha), fun t ht => hmin ht⟩

/-- **The time-Hölder regularity of the constructed (cut) self-similar vorticity on the ball.**

For every strip `[0,S]` with `S + 1 < T`, the field `selfSimVort p g L lam` is `(p/3)`-Hölder in
time on `B(0,R) × [-1,S+1]`, with a constant independent of the point.

The proof is the mean value theorem route `timeHolderOnBall_of_timeDeriv_le`, fed by

* `hasDerivAt_selfSimVort_slice`: every time slice is differentiable on `preWindow T` (the chain
  rule for `λ̄(t)⁻¹ F(ρ^p/λ̄(t))`, with the axis case `radial y = 0` where the field vanishes);
* `bddDt_selfSimVort`: the weighted box `λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` on `preWindow T`;
* `lam_pos_le_on_window`: the uniform lower bound `m > 0` for `λ̄` on the window, which turns the
  weighted box into `‖∂ₜω‖ ≤ K(20p + Cg + Cg')/m² =: Λ` there.

The Hölder exponent is `p/3` — the exponent of the angular vanishing of the profile
(`Γ = (sinθcos²θ)^{p/3}`) — and the constant is `H = Λ · max (S+2) 1`. -/
theorem timeHolderOnBall_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ Work.ConstructionInstance.preWindow T, |deriv lam t| ≤ K)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ S : ℝ, 0 < S → S + 1 < T → ∃ H : ℝ, 0 ≤ H ∧
      Work.StabilityFar.TimeHolderOnBall (p / 3)
        (Work.ConstructionInstance.selfSimVort p g L lam) R S H := by
  intro S hS hST
  have hsub := window_subset_preWindow hST
  -- the constants `Cg`, `Cg'` are nonnegative and so is `20p + Cg + Cg'`
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  -- the uniform lower bound of `λ̄` on the window
  obtain ⟨m, hmpos, hm⟩ := lam_pos_le_on_window hS hST hlam hlamdif
  -- the resulting unweighted bound `Λ` on `∂ₜω`
  set Λ : ℝ := K * (20 * p + Cg + Cg') / m ^ 2 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact div_nonneg (mul_nonneg hK hsum) (by positivity)
  refine timeHolderOnBall_of_timeDeriv_le (α := p / 3) (Λ := Λ) (R := R) (S := S)
    (ω := Work.ConstructionInstance.selfSimVort p g L lam) (by linarith) (by linarith) hΛ ?_ ?_
  · -- differentiability of every time slice on the window
    intro z _hz s hs
    exact hasDerivAt_selfSimVort_slice hgdiff hlam hlamdif (hsub hs) z
  · -- the uniform bound on `∂ₜω` on the ball and the window
    intro z _hz s hs
    have hbox := bddDt_selfSimVort (L := L) hp hp1 hgbdd hg2 hgdiff hK hlam hlamdif hlamd (hsub hs) z
    have hms : m ≤ lam s := hm s hs
    have hms2 : m ^ 2 ≤ (lam s) ^ 2 := by nlinarith [hmpos, hms]
    rw [hΛdef, le_div_iff₀ (by positivity : (0 : ℝ) < m ^ 2)]
    calc ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          * m ^ 2
        = m ^ 2
          * ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          := by ring
      _ ≤ (lam s) ^ 2
          * ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          := mul_le_mul_of_nonneg_right hms2 (norm_nonneg _)
      _ ≤ K * (20 * p + Cg + Cg') := hbox

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeMom.SmoothSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeMom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant as soon as `Ψ` is** (class-free). -/
theorem smoothOpen_bslOp_of_smoothOpen (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-- All the fields attached to a datum of the **a.e.-moment** class (`F`, `Ψ`, `z²∂_zzΨ`,
`∂_θθΨ`) and all their `D_z`-iterates are smooth on the open quadrant. -/
theorem smoothOpen_slices_weak {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j F)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ)
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (smoothOpen_bslOp_of_smoothOpen α hΨso)
      (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)
  refine ⟨hFso.DzIter j, hΨso.DzIter j, ?_, ?_⟩
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)).DzIter j
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter j

end Work.FTS.EllipticEst.AeMom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.DzScratch =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.DzAmgm.Scratch`, in the same namespace `Work.FTS.EllipticEst.DzAmgm`,
-- so importing both was a duplicate-declaration error.  The names stay available to every
-- consumer of this module through the import above.
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeBoxMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular `σ`-masses on a radial box

The three quantities `AAA u`, `BBB u`, `GGG G` of `aeTruncAux` are the angular `σ`-masses
(`σ = sin(2θ)^{-η}`) of the slices of `∂_θθu`, `z²∂_zzu` and `G`.  The hypothesis `AeData α u G`
of the weak class contains the honest `ℋ⁰`-membership of exactly these three functions, i.e.
the `z`-integrability of `z ↦ (w z)² · (the slice mass)`.  Since on a box `[a,b]` with
`0 < a` the radial weight `w z = (1+z)²/z²` is bounded away from `0`, the mass itself is
integrable there.

The proof of the general statement is `integrableOn_sliceMass_of_HkMem` below; the level-`0`
`HkIntegrand` is a single weighted square
(`Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta`), so the mass-times-`w²`
is literally the `z`-marginal of `HkIntegrand α 0 f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarLayer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `sorry`-free part of the open-quadrant certificate (copied verbatim) -/

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

/-- `(0,∞)` and `[0,∞)` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  exact Measure.restrict_congr_set Ioi_ae_eq_Ici

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
    exact Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz


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



/-! ## The agreement of `Ḡ` from the agreement of the angular moments -/


/-! ## The weighted Hardy inequality, in the continuous form needed below -/

/-- **Continuity of `HarOp β g` on `(0,∞)`** from the interval integrability of the weighted
integrand `s ↦ s^{β-1} g s` on `[0,z]` for every `z > 0`: this is
`continuousOn_primitive_Ioi` times the continuous factor `z ↦ z^{-β}`. -/
theorem harOp_continuousOn_of_intervalIntegrable {β : ℝ} {g : ℝ → ℝ}
    (hg : ∀ z, 0 < z → IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * g s) volume 0 z) :
    ContinuousOn (fun z => HarOp β g z) (Set.Ioi 0) := by
  have hprim : ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, s ^ (β - 1) * g s) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi hg
  have hzpow : ContinuousOn (fun z : ℝ => z ^ (-β)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  have hfun : (fun z => HarOp β g z)
      = fun z => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * g s := by
    funext z; rfl
  rw [hfun]
  exact hzpow.mul hprim

/-- **The weighted Hardy inequality** `∫ w² (HarOp β f)² ≤ (100/β²) ∫ w² f²` for `β ≥ 5`,
`w(z) = (1+z)²/z²`, stated for a function `f` whose *Hardy transform is continuous* on `(0,∞)`.

The delivered `lintegral` form `Work.FTS.EllipticEst.HarOp_weighted_lintegral` requires no
measurability of `f` itself, so the missing ingredient for the `∫`-form is precisely an a.e.
strong measurability statement for `z ↦ w(z)²(HarOp β f z)²`, which is supplied here by the
continuity hypothesis.  In the application `f = U_j = F_*(D_z^j F)` this hypothesis is
`harOp_continuousOn_of_intervalIntegrable` applied to the delivered `intervalIntegrable_rpow_Uj`. -/
theorem layer_harOp_weighted_integral_le_cont (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hcont : ContinuousOn (fun z => HarOp β f z) (Set.Ioi 0))
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hfw : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  have hβpos : (0 : ℝ) < β := by linarith
  have hβnn : (0 : ℝ) ≤ 100 / β ^ 2 := by positivity
  have hAnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) :=
    Filter.Eventually.of_forall fun z => by positivity
  have hBnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
    Filter.Eventually.of_forall fun z => by positivity
  have hAaesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
      rw [hfun]
      exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hz)))) 2
    exact (hw.aestronglyMeasurable measurableSet_Ioi).mul
      ((hcont.aestronglyMeasurable measurableSet_Ioi).pow 2)
  -- the delivered `lintegral` estimate
  have hlin := Work.FTS.EllipticEst.HarOp_weighted_lintegral β hβ f hf
  -- its right-hand side is a finite number
  have hBeq : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2)
      = ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfw hBnn).symm
  have hrhs : ENNReal.ofReal (100 / β ^ 2)
        * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) ≠ ⊤ := by
    rw [hBeq, ← ENNReal.ofReal_mul hβnn]
    exact ENNReal.ofReal_ne_top
  have htop : ∫⁻ z in Set.Ioi 0,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top hrhs hlin
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hAaesm hAnn).mp htop, ?_⟩
  have h1 : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      = (∫⁻ z in Set.Ioi 0,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hAnn hAaesm
  rw [h1]
  calc (∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)).toReal
      ≤ (ENNReal.ofReal (100 / β ^ 2)
          * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2)).toReal :=
        ENNReal.toReal_mono hrhs hlin
    _ = (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
        rw [hBeq, ← ENNReal.ofReal_mul hβnn, ENNReal.toReal_ofReal
          (mul_nonneg hβnn (integral_nonneg fun z => by positivity))]

/-! ## The exact radial identity and the per-order bound -/

/-- **The radial identity**: `D_z^j Ḡ(α,F) = -(3/(4α))·HarOp(5/α)(U_j)` on `(0,∞)`. -/
theorem layer_rDzIter_Gbar_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
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
        fun s hs => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α k F hF hmem j hj1k hs.1 hs.2.le
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
      have hD4 := Work.FTS.EllipticEst.Cert.GbarSin.HarOp_eq_sub_of_chain (bet α) hβ1 hz
        hintD4 hchainD4
      have hgoal : z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * (-bet α * HarOp (bet α) (Uj F j) z + Uj F j z) := by
        rw [show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
            = -(3 / (4 * α)) * (z * deriv (HarOp (bet α) (Uj F j)) z) by ring, hD6]
      show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * HarOp (bet α) (Uj F (j + 1)) z
      rw [hgoal, hD4]
      ring

/-- **The weighted `L²` bound of `D_z^j Ḡ`**, with constant `(9/4)(π/2)` independent of `α`. -/
theorem layer_Gbar_rDzIter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
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
  obtain ⟨hH_int, hH_le⟩ := layer_harOp_weighted_integral_le_cont (bet α) hβ5
    (Uj F j)
    (harOp_continuousOn_of_intervalIntegrable (β := bet α) (g :=
      Uj F j) fun z hz =>
        intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz)
    hU2 (Uj_sq_mul_w_integrable α k F hF hmem j hj).1
  have hid := layer_rDzIter_Gbar_eq α hα hα1 k F hF hmem j hj
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

theorem layer_Gbar_HkSq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
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
      (fun j hj => (layer_Gbar_rDzIter_bound α hα hα1 k F hF hmem j
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
    exact (layer_Gbar_rDzIter_bound α hα hα1 k F hF hmem j
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
          (fun j hj => (layer_Gbar_rDzIter_bound α hα hα1 k F hF hmem j
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
    _ ≤ (π / 2) * (gbar_Kang k * ∑ j ∈ Finset.range (k + 1),
          ((9 / 4) * (π / 2) * Work.Spaces.HkSq α k F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (le_of_lt (gbar_Kang_pos k))
        exact (layer_Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
    _ = (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
          Work.Spaces.HkSq α k F := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem layer_Gbar_HkNorm_le_SmoothOpen (k : ℕ) : ∃ C : ℝ, 0 < C ∧
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
    have hsq := layer_Gbar_HkSq_le α hα hα1 k F hF hmem
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        ≤ Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
            Work.Spaces.HkSq α k F) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2)))) *
            Real.sqrt (Work.Spaces.HkSq α k F) := Real.sqrt_mul hDnn _

/-! ## Continuity of the radial derivatives of `Ḡ` -/

/-- **Continuity of the Hardy operator on `(0,∞)`** for an `L¹`-loc integrand: this is the
continuity of the primitive (`Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi`) times the continuous factor
`z ↦ z^(-β)`.  In particular no continuity of `u` itself is needed. -/
theorem layer_harOp_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  have hprim : ContinuousOn
      (fun z => ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz
  have hzpow : ContinuousOn (fun z : ℝ => z ^ (-(bet α))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  have hfun : (fun z => HarOp (bet α) (Uj F j) z)
      = fun z => z ^ (-(bet α)) * ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s := by
    funext z; rfl
  rw [hfun]
  exact hzpow.mul hprim

/-- **The radial derivatives of `Ḡ` are continuous on `(0,∞)`**: by the exact radial identity
`D_z^j Ḡ = -(3/(4α))·HarOp (5/α)(F_*(D_z^j F))` and `layer_harOp_continuousOn`. -/
theorem layer_rDzIter_Gbar_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => rDzIter j (Work.Elliptic.Gbar α F) z) (Set.Ioi 0) := by
  have hH := layer_harOp_continuousOn α hα hα1 k F hF hmem j hj
  refine (hH.const_mul (-(3 / (4 * α)))).congr ?_
  intro z hz
  exact layer_rDzIter_Gbar_eq α hα hα1 k F hF hmem j hj hz

/-! ## Continuity of the `ℋ^k`-integrand of the target on the open quadrant -/

/-- The angular profile `D_θ^i (sin 2θ)` is continuous. -/
theorem layer_continuousOn_sinIter (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => sinIter i p.2) Q0 := by
  have hpoly : Continuous (fun t : ℝ => (sinPoly i).eval t) := Polynomial.continuous _
  have hfun : (fun p : ℝ × ℝ => sinIter i p.2)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (sinPoly i).eval (Real.cos (2 * p.2)) := by
    funext p; exact sinIter_eq_sinPoly i p.2
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.mul
    (hpoly.comp (Real.continuous_cos.comp (continuous_const.mul continuous_snd))).continuousOn

/-- The weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem layer_continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have h2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [h2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- **The `ℋ^k`-integrand of `Ḡ(α,F)·sin 2θ` is continuous on the open quadrant** for a source
`F` which is `C^∞` on `Q0` and lies in `ℋ^k`.

Indeed on `Q0` the factorisations
`D_z^i(Ḡ·sin 2θ) = (D_z^i Ḡ)·sin 2θ` and `D_z^j D_θ^i(Ḡ·sin 2θ) = (D_z^j Ḡ)·D_θ^i(sin 2θ)`
exhibit the integrand as a finite sum of products of continuous functions of `(z,θ)`. -/
theorem layer_continuousOn_target_integrand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) p.1 p.2) Q0 := by
  have hz : ∀ i, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => rDzIter i (Work.Elliptic.Gbar α F) p.1) Q0 := fun i hi =>
    (layer_rDzIter_Gbar_continuousOn α hα hα1 k F hF hmem i hi).comp continuousOn_fst
      (fun p hp => hp.1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 := by fun_prop
  have hwdiv : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1
        / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 := continuousOn_wdivsin_Q0
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := layer_continuousOn_Wt α
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (rDzIter i (Work.Elliptic.Gbar α F) p.1
          * Real.sin (2 * p.2)
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (rDzIter j (Work.Elliptic.Gbar α F) p.1 * sinIter i p.2
                * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0)) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ fun i hi => ?_
      exact (((hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul hsin).mul hwdiv).pow 2
    · refine continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact (((hz j (by omega)).mul (layer_continuousOn_sinIter i)).mul hWt).pow 2
      · simp only [if_neg hc]
        exact continuousOn_const
  · intro p hp
    simp only [Work.Spaces.HkIntegrand]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [gbar_DzIter_target_eq α F i p.1 p.2]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, if_pos hc, gbar_mixed_target_eq α F j i p.1 p.2]
      · rw [if_neg hc, if_neg hc]

/-! ## Membership in `ℋ^k` for a `C^∞` source on the open quadrant -/

/-- **`Ḡ(α,F)·sin 2θ ∈ ℋ^k`** for a source `F` which is `C^∞` on the open quadrant and lies
in `ℋ^k`.

The majorant is `M z θ = Kang k·w(z)²·Σ_{j≤k}(D_z^j Ḡ z)²`, whose `θ`-slices are
constant (`integrableOn_const`) and whose slice integral is integrable by the per-order weighted
bound `layer_Gbar_rDzIter_bound`. -/
theorem layer_HkMem_target_of_smoothOpen (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  set M : ℝ → ℝ → ℝ := fun z θ => gbar_Kang k * (Work.Spaces.w z) ^ 2 *
    ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 with hM
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine Work.FTS.LocData.HkMem_of_majorant (α := α) (k := k)
    (f := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) (M := M)
    (layer_continuousOn_target_integrand α hα hα1 k F hF hmem) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are constant in `θ`
    intro z _
    exact MeasureTheory.integrableOn_const hIθ_ne_top
  · -- the slice integral of the majorant is integrable
    have hconst : ∀ z : ℝ, (fun θ : ℝ => M z θ) = fun _ : ℝ => gbar_Kang k *
        (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
      intro z
      funext θ
      rw [hM]
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, M z θ)
        = fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
      funext z
      rw [hconst z, gbar_integral_Iθ_const]
      ring
    rw [hfun]
    have hsum : Integrable (fun z => ∑ j ∈ Finset.range (k + 1),
        (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      gbar_integrable_finsetSum _ _ _ fun j hj =>
        ((layer_Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1.const_mul (gbar_Kang k)).const_mul _
    refine hsum.congr ?_
    filter_upwards with z
    simp only [Finset.mul_sum]
  · -- the pointwise domination
    intro z hz θ hθ
    exact gbar_HkIntegrand_target_le α hα hα1 k F z θ hz hθ

/-! ## The target theorem -/


end Work.FTS.EllipticEst.Cert.GbarLayer
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.OpenCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

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

/-- `(0,∞)` and `[0,∞)` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  exact Measure.restrict_congr_set Ioi_ae_eq_Ici

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

/-- **The weighted `L²` Hardy estimate, with the measurability of the source supplied by the
continuity of its primitive.**

The `∫⁻`-form `HarOp_weighted_lintegral` needs only the square-integrability of the source, but
its Bochner-integral upgrade requires the a.e. strong measurability of `HarOp β f`.  That is what
the hypothesis `hint` is for: it makes the primitive `z ↦ ∫_0^z s^(β-1) f s ds` continuous on
`(0,∞)` (`continuousOn_primitive_Ioi`), hence `HarOp β f` continuous there.  In the application
`f = F_*(D_z^j F)` the hypothesis is `intervalIntegrable_rpow_Uj`. -/
theorem HarOp_weighted_integral_cont (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hint : ∀ z : ℝ, 0 < z →
      IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * f s) volume 0 z)
    (hfw : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  -- continuity, hence a.e. strong measurability, of `HarOp β f`
  have hcont : ContinuousOn (fun z => HarOp β f z) (Set.Ioi 0) := by
    have hp : ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) (Set.Ioi 0) :=
      continuousOn_primitive_Ioi hint
    have hfun : (fun z => HarOp β f z)
        = fun z => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s := by
      funext z; rfl
    rw [hfun]
    exact (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).mul hp
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h2 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by funext z; rfl
    rw [h2]
    exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
  have hmeas : AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (hw2.mul (hcont.pow 2)).aestronglyMeasurable measurableSet_Ioi
  have hnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2 :=
    Eventually.of_forall fun z => by positivity
  have hnnf : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ (Work.Spaces.w z) ^ 2 * (f z) ^ 2 :=
    Eventually.of_forall fun z => by positivity
  -- the `∫⁻`-form of the weighted Hardy inequality
  have hlin := HarOp_weighted_lintegral β hβ f hf
  have hUsq : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2))
      = ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfw hnnf).symm
  have hfin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
      ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hlin
    rw [hUsq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hintg : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).1 hfin
  refine ⟨hintg, ?_⟩
  have h1 : ENNReal.ofReal
        (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintg hnn
  have h3 : ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal ((100 / β ^ 2) *
          ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
    have hmul : ENNReal.ofReal ((100 / β ^ 2) *
          ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
        = ENNReal.ofReal (100 / β ^ 2) *
          ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 100 / β ^ 2)
    rw [h1, hmul, ← hUsq]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
    (integral_nonneg fun z => by positivity))).1 h3

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
  obtain ⟨hH_int, hH_le⟩ := HarOp_weighted_integral_cont (bet α) hβ5 (Uj F j) hU2
    (fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz)
    (Uj_sq_mul_w_integrable α k F hF hmem j hj).1
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

theorem Gbar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hC, h⟩ := Gbar_Hk_le_open_SmoothOpen k
  exact ⟨C, hC, fun α F hα hα1 hFraw hmem =>
    h α F hα hα1 (smoothOpen_of_forall hFraw) hmem⟩

end Work.FTS.EllipticEst.Cert.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces.TL2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **`Lzero` preserves `C^∞` on the open quadrant.**

`Lzero Φ = -∂_θθΦ + ∂_θ(tan θ·Φ) - 6Φ` is built from `Φ`, its second `θ`-derivative and the
function `∂_θ(tan θ·Φ)`, together with the constant factor `6`; all of these are `C^∞` on `Q0`
whenever `Φ` is (`tan` is smooth there because `cos θ ≠ 0` for `0 < θ < π/2`). -/
theorem smoothOpen_Lzero_of_smoothOpen {Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Φ) := by
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Φ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΦ
  -- `-∂_θθΦ + ∂_θ(tan θ·Φ) - 6Φ`, with the angular operators written as plain `∂_θ`-iterates
  have hcomp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Spaces.pthIter 2 Φ z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ - 6 * Φ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΦ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl htΦ 1))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΦ)
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hcomp
    (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])

/-- **The angular source `Gsrc α G Φ` is `C^∞` on the open quadrant** for every datum of the
weak hypothesis class `EllWeakPos α k G Φ`.

Indeed, on the open quadrant `Q0` the elliptic law `bslOp α Φ = G` (component `1` of
`EllWeakPos`) determines `G`, and substituting it into `Gsrc` turns the source into the
`α = 0` part of the operator:

  `Gsrc α G Φ = G + α²z²∂_zzΦ + α(5+α)z∂_zΦ = bslOp α Φ + α²z²∂_zzΦ + α(5+α)z∂_zΦ = Lzero Φ`,

which is `C^∞` on `Q0` by `smoothOpen_Lzero_of_smoothOpen` (the smoothness of `Φ` on `Q0` is
component `6` of `EllWeakPos`).  `SmoothOpen` is a statement about `Q0` only, so the
congruence `Cert.smoothOpen_congr_bsl` transports the smoothness from `Lzero Φ` to
`Gsrc α G Φ`. -/
theorem smoothOpen_Gsrc {α : ℝ} {k : ℕ} {G Φ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k G Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Mine.Gsrc α G Φ) := by
  -- `Φ` is `C^∞` on the open quadrant, hence so is `Lzero Φ`
  have hΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hL : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Φ) :=
    smoothOpen_Lzero_of_smoothOpen hΦ
  -- on `Q0` the source agrees with `Lzero Φ`
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hL (fun z θ hz hθ0 hθ1 => ?_)
  have heq : Work.Elliptic.bslOp α Φ z θ = G z θ := h.eq z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.FTS.EllipticEst.Mine.Gsrc] at heq ⊢
  rw [← heq]
  ring

end Work.FTS.EllipticEst.Cores.Pieces.TL2
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Radial.hkMem_of_ae_slice_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Radial

set_option linter.unusedVariables false

/-- The level-`0` `HkIntegrand` unfolds into the weight `w` times the basic angular slice
integrand: for `θ ∈ Iθ`,
`HkIntegrand α 0 f z θ = w z ^ 2 * (f z θ ^ 2 * sEta θ)`.  (At `z = 0` the weight `w 0`
vanishes, and both sides are `0`.) -/
private theorem HkI_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z hθ]
  ring

/-- The `θ`-integral of the level-`0` `HkIntegrand` factors out the constant weight
`w z ^ 2`. -/
private theorem HkI_slice_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => HkI_eq α f z hθ)]
  rw [MeasureTheory.integral_const_mul]

theorem hkMem_of_ae_slice_bound {α : ℝ} {g Ψ L : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 < K)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hbound : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hL : Work.Spaces.HkMem α 0 L) :
    Work.Spaces.HkMem α 0 g := by
  -- ## the two conjuncts of `HkMem α 0 g`
  refine ⟨?_, ?_⟩
  · -- ### `θ`-slice integrability of the integrand, from the hypothesis on `g`
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hz0
    · -- `z = 0`: the weight `w 0` vanishes, so the integrand is identically `0`
      subst h0
      refine IntegrableOn.congr_fun (integrableOn_zero (μ := volume) (s := Work.Spaces.Iθ))
        (fun θ hθ => ?_) measurableSet_Icc
      rw [HkI_eq α g 0 hθ]
      simp [Work.Spaces.w]
    · -- `z > 0`: multiply the hypothesis of `hslice` by the constant `w z ^ 2`
      refine IntegrableOn.congr_fun ((hslice z hz0).const_mul ((Work.Spaces.w z) ^ 2))
        (fun θ hθ => ?_) measurableSet_Icc
      exact (HkI_eq α g z hθ).symm
  · -- ### integrability of the `z`-integral of the angular slices
    -- The slice integrals are a.e. strongly measurable, being the partial integrals of the
    -- jointly a.e. strongly measurable `HkIntegrand` (continuous on the open quadrant).
    have hAmeas : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        (volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    -- the integrable majorant `K · (slice integral of Ψ + slice integral of L)`
    have hBC : IntegrableOn (fun z => K *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 L z θ))) Work.Spaces.Iz :=
      (hΨ.2.add hL.2).const_mul K
    refine Integrable.mono' hBC hAmeas ?_
    -- it suffices to dominate a.e. on the open half-line
    have hIzm : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi 0) :=
      Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [hIzm]
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))]
    -- factor out `w z ^ 2` from all three slice integrals
    rw [HkI_slice_eq α g z, HkI_slice_eq α Ψ z, HkI_slice_eq α L z]
    have h1 : (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (Work.Spaces.w z) ^ 2
          * (K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) :=
      mul_le_mul_of_nonneg_left (hbound z hz) (sq_nonneg _)
    calc (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) := h1
      _ = K * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring

end Work.FTS.EllipticEst.H2W.Radial
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.level0SlicesBridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Monotonicity of the level-`0` quantity in the level

The two ingredients of the final assembly that need no analysis:

* the level-`0` `ℋ`-square of the radially differentiated source `D_z^jF` (`j ≤ 2`) is one of
  the summands of the level-`2` `ℋ`-square of `F`, so it is bounded by it as soon as that
  integral is honest (`HkMem α 2 F`, which the weak class `EllWeakPos α 2` provides);
* the level-`0` `ℋ`-square of `g` is the `L²`-square of `g · w / sin(2θ)^{η/2}`
  (`NSq_eq_HkSq` of `H2W/Norms`). -/


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.aesm_F_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem aesm_F_slots {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- `Ψ` is `C^∞` on the open quadrant
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- hence so is `bslOp α Ψ`, which agrees with the source `F` on the open quadrant
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hso
  have hcont1 : ContinuousOn (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      Work.FTS.EllipticEst.Q0 := hbsl.continuousOn
  have hcont2 : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Elliptic.bslOp α Ψ)))
      Work.FTS.EllipticEst.Q0 := hbsl.Dz.continuousOn
  -- almost every `θ ∈ Iθ` lies in the open interval, where the equation holds
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ae_mem_Ioo_of_mem_Iθ
  intro z hz
  constructor
  · -- the first slot: replace `F` by `bslOp α Ψ` a.e.
    refine (aesm_slice_sq_mul_sEta hcont1 hz).congr ?_
    filter_upwards [haeθ] with θ hθ
    rw [h.eq z hz θ hθ.1 hθ.2]
  · -- the second slot: `D_z` also only sees the values on the open quadrant
    refine (aesm_slice_sq_mul_sEta hcont2 hz).congr ?_
    filter_upwards [haeθ] with θ hθ
    have hslice : (fun z' : ℝ => F z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => Work.Elliptic.bslOp α Ψ z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact (h.eq z' hz' θ hθ.1 hθ.2).symm
    have hpz : Work.Spaces.Dz F z θ = Work.Spaces.Dz (Work.Elliptic.bslOp α Ψ) z θ := by
      show z * Work.Spaces.pz F z θ = z * Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ
      rw [show Work.Spaces.pz F z θ = Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ from
        hslice.deriv_eq]
    rw [← hpz]

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDerivBox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The engine: box integrability of a `∂_z`-slice of an `ℋ^k` datum

The common part of both conjuncts of `weakSliceDerivBox`: for a `C^∞` function `g` on the open
quadrant which is honestly in `ℋ^k` with `k ≥ 1`, the function
`(z,θ) ↦ ∂_z g z θ · sinθcos²θ` is integrable over the box `(a,b] × Iθ`, for every `a > 0`.

The argument is the box version of `weakSliceDeriv`.  For each `z ∈ (a,b]` (so `z > 0`) the
pointwise absorption `abs_mul_sinCos2_le_weighted` gives

`|∂_z g z θ · sinθcos²θ| ≤ (∂_z g z θ · w z/sin(2θ)^{η/2})² + 1`,

and `∂_z g · w/sin^{η/2} = z^{-1}·(D_z g · w/sin^{η/2})`, so

`|∂_z g z θ · sinθcos²θ| ≤ a^{-2}·HkIntegrand α k g z θ + 1`

by `sq_le_HkIntegrand_z` at the index `i = 1`.  The right-hand side is integrable on the box:
the angular slices of `HkIntegrand` are integrable for every `z ∈ Iz` and the `z`-integral of
the angular integral is integrable on `Iz` (the two conjuncts of `HkMem`), so Tonelli
(`integrable_prod_ae`) makes the uncurried `HkIntegrand` product-integrable.  A.e. strong
measurability comes from the smoothness of `g` on the open quadrant. -/


/-- **The pointwise domination on the box.**

For `0 < a < z` and `θ ∈ Iθ`,
`|∂_z g z θ · sinθcos²θ| ≤ a⁻² · HkIntegrand α k g z θ + 1`.

This is the combination of `abs_mul_sinCos2_le_weighted` (which absorbs the angular profile
into `(∂_z g · w/sin(2θ)^{η/2})² + 1`) with the identity `D_z g = z·∂_z g` and the
single-summand bound `sq_le_HkIntegrand_z` applied at `i = 1`. -/
private lemma pointwise_bound {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {a z θ : ℝ} (hk : 1 ≤ k)
    (ha : 0 < a) (hz : a < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 := by
  have hzpos : 0 < z := lt_trans ha hz
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pz g z θ) hzpos hθ
  have hDz : Work.Spaces.DzIter 1 g z θ = z * Work.Spaces.pz g z θ := rfl
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pz g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hDz, eq_inv_mul_iff_mul_eq₀ hz2]
    ring
  have h3 : Work.Spaces.HkIntegrand α k g z θ ≥
      ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 1 hk
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 2)⁻¹ := by positivity
  have hzipow : (z ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hz.le 2)
  calc |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pz g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep : (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right hzipow (sq_nonneg _)
        linarith
    _ ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 := by
        have hstep : (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ :=
          mul_le_mul_of_nonneg_left h3 hcinv
        linarith


/-! ## The two instantiations -/



end

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant as soon as `Ψ` is.**

This is the *open-quadrant* version of `Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp`, whose
hypothesis `Work.Spaces.SmoothNbhd Ψ` (analyticity on a neighbourhood of the closed quadrant)
is far too strong for the weak class `EllWeakPos`, where only
`ContDiffOn ℝ n (uncurry Ψ) Q0` is available.

The proof is the same algebraic bookkeeping: `bslOp α Ψ` is built from `Ψ`, the multi-indices
`pzIter 2 Ψ`, `pz Ψ`, `pthIter 2 Ψ`, `pth (tan θ · Ψ)` — all `SmoothOpen` by
`SmoothOpen.pzIter`, `SmoothOpen.pz`, `Cert.smoothOpen_pthIter_bsl`,
`SmoothOpen.pth` — together with the `C^∞` factors `z²`, `z`, `tan θ` (`tan` is smooth on
`Q0` because `cos θ ≠ 0` there). -/
theorem smoothOpen_bslOp_of_smoothOpen (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  -- the second-order term `-α²z²·∂_z²Ψ`
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  -- the first-order term `-α(5+α)z·∂_zΨ`
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  -- the angular operator `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  -- assembly
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-- All the fields attached to a datum of the weak class (`F`, `Ψ`, `z²∂_zzΨ`, `∂_θθΨ`) and
all their `D_z`-iterates are smooth on the open quadrant.  The source `F` is `bslOp α Ψ` there
(the equation), hence smooth; the other two are obtained from `Ψ` by the product rule. -/
theorem smoothOpen_slices_weak {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j F)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ)
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ∧ Work.FTS.EllipticEst.SmoothOpen
          (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) := by
  -- `Ψ` is `C^∞` on the open quadrant by the smoothness component of the weak class
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the source `F` agrees with `bslOp α Ψ` on the open quadrant (the elliptic law)
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (smoothOpen_bslOp_of_smoothOpen α hΨso)
      (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)
  refine ⟨hFso.DzIter j, hΨso.DzIter j, ?_, ?_⟩
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)).DzIter j
  · exact (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter j

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsMomentChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular-moment chain `F_*(D_z^j Ψ) ≡ 0` (`j ≤ 2`) for the weak elliptic class

For a datum `h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` with `k ≥ 1`, the angular moments
`F_*(D_z^j Ψ)(z) = ∫_θ D_z^j Ψ(z,θ) sinθcos²θ dθ` vanish for `j ≤ 2` and every `z > 0`.

The route is the chain rule for the moment along `D_z` (the identity
`F_*(D_z^j Ψ)(z) - F_*(D_z^j Ψ)(s) = ∫_s^z F_*(D_z^{j+1} Ψ)(r)/r dr`, obtained from
`Work.FTS.EllipticEst.moment_relation`, i.e. Fubini on a radial box), together with the
*continuity* of the moments `F_*(D_z Ψ)` and `F_*(D_z² Ψ)`:

* from `j = 0` and `F_*(Ψ) ≡ 0` the primitive of `r ↦ F_*(D_zΨ)(r)/r` vanishes identically on
  `(0,∞)`, so `F_*(D_zΨ) ≡ 0` once it is known to be continuous;
* continuity of `F_*(D_zΨ)` comes from the `j = 1` chain, which exhibits it as an indefinite
  integral of the locally integrable function `r ↦ F_*(D_z²Ψ)(r)/r`;
* the same two steps at `j = 1, 2` give `F_*(D_z²Ψ) ≡ 0`.

The only analytic input is the local integrability and finiteness of the moments
`F_*(D_z^j Ψ)`, which follows from the `θ`-slice energy bounds: the `θ`-energy of every radial
iterate `D_z^j Ψ` (`1 ≤ j ≤ 3`) is dominated on a compact radial interval by the reference
energy `Eref Ψ` (the `θ`-energies of `∂_θ²Ψ`, `D_z∂_θ²Ψ`, `z²∂_z²Ψ` and `D_z(z²∂_z²Ψ)`), and
`Eref Ψ` is locally integrable.  These bounds use the slice Poincaré inequality
`Work.FTS.EllipticEst.remov.ws_slice_pointwise_le` of `remov.wsAux` to pass from the
`ℋ^k`-honesty of `∂_θ²Ψ` (the only angular second-derivative control available) to the
`θ`-energy of `D_zΨ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Measurability helpers -/




/-- The angular moment `F_*(g)` of a function continuous on the open quadrant is a.e. strongly
measurable in the radial variable, on any interval `(a,b]` with `a ≥ 0`. -/
theorem aesm_fstar_Ioc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun z => Work.Elliptic.Fstar g z) (volume.restrict (Set.Ioc a b)) := by
  have hcontσ : Continuous (fun p : ℝ × ℝ => sg p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * sg p.2)
      Work.FTS.EllipticEst.Q0 :=
    hg.mul hcontσ.continuousOn
  have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha).integral_prod_right'
    (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
  simpa only [Work.Elliptic.Fstar] using h

/-- `aesm_fstar_Ioc` on a closed interval. -/
theorem aesm_fstar_Icc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun z => Work.Elliptic.Fstar g z) (volume.restrict (Set.Icc a b)) := by
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  exact aesm_fstar_Ioc hg ha

/-! ## Smoothness of `z²∂_z²Ψ` -/

/-- `z² ∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  have hz2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)
      (s := Work.FTS.EllipticEst.Q0)).pow 2
  refine (hz2.mul hg).congr ?_
  intro p hp
  rfl

/-! ## The `θ`-second-derivative of `∂_zΨ` is a radial iterate of `∂_θ²Ψ` -/

/-- `pthIter 2 (pz Ψ) s t = D_z∂_θ²Ψ (s,t) / s` on the open quadrant.  The one-variable content
is that the radial slice of `∂_zΨ` is the radial slice of `D_zΨ = z∂_zΨ` divided by the
constant `s`, and that `D_z` commutes with `∂_θ²` (`ws_pthIter_two_DzIter`). -/
theorem pthIter_two_pz_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {s t : ℝ} (hs : 0 < s) (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t
      = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t / s := by
  have hfun : Work.Spaces.pz Ψ s = fun t => Work.Spaces.DzIter 1 Ψ s t / s := by
    funext t
    show deriv (fun z' => Ψ z' t) s = Work.Spaces.DzIter 1 Ψ s t / s
    show deriv (fun z' => Ψ z' t) s = (s * deriv (fun z' => Ψ z' t) s) / s
    rw [mul_div_cancel_left₀ _ (ne_of_gt hs)]
  have hstep : Work.Spaces.pth (Work.Spaces.pz Ψ) s
      = fun t => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s t / s := by
    funext t
    show deriv (fun u => Work.Spaces.pz Ψ s u) t
      = deriv (fun u => Work.Spaces.DzIter 1 Ψ s u) t / s
    rw [hfun]
    have hsplit : (fun u : ℝ => Work.Spaces.DzIter 1 Ψ s u / s)
        = fun u => s⁻¹ * Work.Spaces.DzIter 1 Ψ s u := by
      funext u; rw [div_eq_mul_inv, mul_comm]
    rw [hsplit, deriv_const_mul_field]
    ring
  have hstep2 : Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s
      = fun t => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s := by
    show deriv (fun u => Work.Spaces.pth (Work.Spaces.pz Ψ) s u)
      = fun t => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s
    rw [hstep]
    funext t
    show deriv (fun u => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u / s) t
      = deriv (fun u => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u) t / s
    have hsplit : (fun u : ℝ => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u / s)
        = fun u => s⁻¹ * Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u := by
      funext u; rw [div_eq_mul_inv, mul_comm]
    rw [hsplit, deriv_const_mul_field]
    ring
  rw [hstep2]
  show Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s
      = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t / s
  rw [ws_pthIter_two_DzIter hS 1 hs ht]

/-- **The `θ`-energy of the second `θ`-derivative of `∂_zΨ`.**  It is `s⁻²` times the
`θ`-energy of `D_z∂_θ²Ψ`, hence finite and integrable on every slice, by `ws_slot_slice`. -/
theorem integrableOn_pthIter_two_pz {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn
        (fun t => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t) Iθ ∧
      (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
        = (s ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  have hbase := ws_slot_slice hSB h.memB 1 hk hs
  have hae : (fun t => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
      =ᵐ[volume.restrict Iθ]
        (fun t => (s ^ 2)⁻¹
          * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t) ^ 2 * SS t)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun t ht => ?_)
    show (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t
      = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t) ^ 2 * SS t)
    rw [pthIter_two_pz_eq hSΨ hs ht, div_pow, div_eq_mul_inv]
    ring
  refine ⟨(hbase.const_mul _).congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
  rfl

/-- The `θ`-energy scales by the square of a constant: `∫ (c·X s)² sEta = c² ∫ (X s)² sEta`. -/
theorem thetaE_const_mul {X : ℝ → ℝ → ℝ} {c s : ℝ}
    (hX : MeasureTheory.IntegrableOn (fun θ => (X s θ) ^ 2 * SS θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (c * X s θ) ^ 2 * SS θ) Iθ ∧
      thetaE (fun u θ => c * X u θ) s = c ^ 2 * thetaE X s := by
  refine ⟨?_, ?_⟩
  · have hbase := hX.const_mul (c ^ 2)
    refine hbase.congr ?_
    refine Eventually.of_forall (fun θ => ?_)
    show c ^ 2 * (X s θ ^ 2 * SS θ) = (c * X s θ) ^ 2 * SS θ
    ring
  · show (∫ θ in Iθ, (c * X s θ) ^ 2 * SS θ) = c ^ 2 * (∫ θ in Iθ, (X s θ) ^ 2 * SS θ)
    have heq : (fun θ => (c * X s θ) ^ 2 * SS θ)
        = fun θ => c ^ 2 * ((X s θ) ^ 2 * SS θ) := by
      funext θ; ring
    rw [heq, MeasureTheory.integral_const_mul]

/-! ## The Poincaré bound for the slice of `∂_zΨ` -/

/-- **The slice Poincaré bound for `∂_zΨ`.**  On a compact radial interval `[a,b] ⊂ (0,∞)` the
`θ`-energy of `∂_zΨ` is dominated by a constant times `1 + thetaE (D_z∂_θ²Ψ)`; the analytic
input is the slice Poincaré inequality `ws_slice_pointwise_le` applied to the slice
`θ ↦ ∂_zΨ(s,θ)`, whose second `θ`-derivative is `D_z∂_θ²Ψ(s,·)/s`. -/
theorem thetaE_pz_le {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ s θ) ^ 2 * SS θ) Iθ ∧
      thetaE (Work.Spaces.pz Ψ) s ≤ K * (1 + Eref Ψ s) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hqI : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hQ : ∀ s ∈ Set.Icc a b, ((s, Real.pi / 4) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    fun s hs => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hs.1, hqI.1, hqI.2⟩
  have hc1 : ContinuousOn (fun s : ℝ => Work.Spaces.pz Ψ s (Real.pi / 4)) (Set.Icc a b) :=
    (hSΨ.pz).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hQ
  have hc2 : ContinuousOn (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4))
      (Set.Icc a b) :=
    (hSΨ.pz).pth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hQ
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  set A : ℝ := max 1 (|C₁| ^ 2) with hAdef
  set B : ℝ := max 1 (|C₂| ^ 2) with hBdef
  set S : ℝ := ∫ θ in Iθ, SS θ with hSdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hS0 : 0 ≤ S := by rw [hSdef]; exact ws_sEta_integral_nonneg
  have hSle : S ≤ 10000 := by rw [hSdef]; exact ws_sEta_integral_le
  set M : ℝ := 2 * A + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
    + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set Kp : ℝ := max 1 (M * 10000) with hKpdef
  have hKp0 : (0 : ℝ) < Kp := by rw [hKpdef]; positivity
  refine ⟨Kp * 10000, by positivity, ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  obtain ⟨hEint, hIval⟩ := integrableOn_pthIter_two_pz hk h hs0
  have hv : ContDiffOn ℝ 2 (fun θ => Work.Spaces.pz Ψ s θ) (Set.Ioo 0 (Real.pi / 2)) :=
    ws_contDiffOn_slice hSΨ.pz hs0
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ 2 * (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2
          + 4 * Real.pi ^ 2 * (1 + S)
            * (1 + (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
              + (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)) := by
    intro θ hθ
    have h := ws_slice_pointwise_le (v := fun θ => Work.Spaces.pz Ψ s θ) hv hEint θ hθ
    simpa only [← hSdef, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using h
  have hA' : (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ A := by
    have hb1 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ≤ C₁ := by
      have hb := hC₁ s hs
      rwa [Real.norm_eq_abs] at hb
    have hb2 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ≤ |C₁| := le_trans hb1 (le_abs_self C₁)
    rw [hAdef]
    calc (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2
        = |Work.Spaces.pz Ψ s (Real.pi / 4)| ^ 2 := by rw [sq_abs]
      _ ≤ |C₁| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
      _ ≤ max 1 (|C₁| ^ 2) := le_max_right _ _
  have hB' : (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2 ≤ B := by
    have hb1 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ≤ C₂ := by
      have hb := hC₂ s hs
      rwa [Real.norm_eq_abs] at hb
    have hb2 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ≤ |C₂| :=
      le_trans hb1 (le_abs_self C₂)
    rw [hBdef]
    calc (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
        = |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ^ 2 := by rw [sq_abs]
      _ ≤ |C₂| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
      _ ≤ max 1 (|C₂| ^ 2) := le_max_right _ _
  have hI : (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
      ≤ (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
    rw [hIval]
    have hsa : a ≤ s := hs.1
    have hs2a : a ^ 2 ≤ s ^ 2 := by nlinarith
    have h2 : (s ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < s ^ 2) (by positivity : (0 : ℝ) < a ^ 2)).mpr hs2a
    exact mul_le_mul_of_nonneg_right h2 (thetaE_nonneg _ _)
  have hmain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
    intro θ hθ
    have hEb0 : 0 ≤ thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
      thetaE_nonneg _ _
    have hcoef : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) := by positivity
    have hbr : 1 + ((Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
          + (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t))
        ≤ 1 + B + (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
      linarith [hB', hI]
    have hstep : (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ 2 * A + 4 * Real.pi ^ 2 * (1 + S)
            * (1 + B + (a ^ 2)⁻¹ * thetaE
                (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      have h2 := mul_le_mul_of_nonneg_left hbr hcoef
      have h3 : 2 * (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ 2 * A := by linarith [hA']
      linarith [hpt θ hθ, h2, h3]
    have hK2 : 2 * A + 4 * Real.pi ^ 2 * (1 + S)
          * (1 + B + (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
        ≤ M * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      rw [hMdef]
      have hd : (2 * A + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
              + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹)
            * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
          - (2 * A + 4 * Real.pi ^ 2 * (1 + S)
              * (1 + B + (a ^ 2)⁻¹
                * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s))
          = 2 * A * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
            + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
              * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
            + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ := by ring
      have hnn1 : 0 ≤ 2 * A * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
        mul_nonneg (by linarith) hEb0
      have hnn2 : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
          * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)) hEb0
      have hnn3 : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
      linarith [hd, hnn1, hnn2, hnn3]
    have hKM : M * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
        ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      have h1 : M ≤ Kp := by
        rw [hKpdef]
        calc M ≤ M * 10000 := by nlinarith [hM0]
          _ ≤ max 1 (M * 10000) := le_max_right _ _
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith [hstep, hK2, hKM]
  have hInt : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ s θ) ^ 2 * SS θ) Iθ := by
    refine MeasureTheory.Integrable.mono'
      (ws_sEta_integrableOn.const_mul
        (Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s))) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
        ((hSΨ.pz).continuousOn.pow 2 |>.mul ws_contOn_sEta) hs0
    · filter_upwards [ws_ae_mem_Ioo] with θ hθ
      have hSS : 0 ≤ SS θ := ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSS)]
      exact mul_le_mul_of_nonneg_right (hmain θ hθ) hSS
  refine ⟨hInt, ?_⟩
  have hEb0 : 0 ≤ thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := thetaE_nonneg _ _
  have htheta := thetaE_le_const (X := Work.Spaces.pz Ψ) (s := s)
    (M := Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)) hmain
  have hEb_le : thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s ≤ Eref Ψ s := by
    rw [Eref]
    nlinarith [thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s,
      thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s,
      thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s]
  calc thetaE (Work.Spaces.pz Ψ) s
      ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
          * (∫ θ in Iθ, SS θ) := htheta
    _ ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) * 10000 :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = Kp * 10000 * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by ring
    _ ≤ Kp * 10000 * (1 + Eref Ψ s) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hEb_le]

/-! ## The reference energy dominates each of its four summands -/



theorem Eref_ge_thetaE_G (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

theorem Eref_ge_thetaE_DzG (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
      ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  linarith

/-! ## The `θ`-energy of a sum of two slices -/

/-- If `f(z,·) = g(z,·) + h(z,·)` on the open angular interval and the `θ`-energies of the two
summands are finite, then so is that of `f`, and
`thetaE f z ≤ 2 thetaE g z + 2 thetaE h z`. -/
theorem thetaE_add_le {f g h : ℝ → ℝ → ℝ} {s : ℝ}
    (hf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f s θ = g s θ + h s θ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2 * SS θ) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => (h s θ) ^ 2 * SS θ) Iθ)
    (haesm : AEStronglyMeasurable (fun θ => (f s θ) ^ 2 * SS θ) (volume.restrict Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (f s θ) ^ 2 * SS θ) Iθ ∧
      thetaE f s ≤ 2 * thetaE g s + 2 * thetaE h s := by
  have hle : (fun θ => (f s θ) ^ 2 * SS θ) ≤ᵐ[volume.restrict Iθ]
      (fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (f s θ) ^ 2 * SS θ ≤ 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)
    rw [hf θ hθ]
    have hSS := ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (g s θ + h s θ) ^ 2 ≤ 2 * (g s θ) ^ 2 + 2 * (h s θ) ^ 2 := by
      nlinarith [sq_nonneg (g s θ - h s θ)]
    calc (g s θ + h s θ) ^ 2 * SS θ
        ≤ (2 * (g s θ) ^ 2 + 2 * (h s θ) ^ 2) * SS θ := mul_le_mul_of_nonneg_right hsq hSS
      _ = 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ) := by ring
  have hInt : MeasureTheory.IntegrableOn
      (fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) Iθ :=
    (hg.const_mul 2).add (hh.const_mul 2)
  constructor
  · refine MeasureTheory.Integrable.mono' hInt haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hle] with θ hθI hθ
    have hSS := ws_sEta_nonneg hθI
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSS)]
    exact hθ
  · have hmono := MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (f := fun θ => (f s θ) ^ 2 * SS θ)
      (g := fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ))
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθI
        exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθI))
      hInt hle
    show (∫ θ in Iθ, (f s θ) ^ 2 * SS θ)
        ≤ 2 * (∫ θ in Iθ, (g s θ) ^ 2 * SS θ) + 2 * (∫ θ in Iθ, (h s θ) ^ 2 * SS θ)
    calc (∫ θ in Iθ, (f s θ) ^ 2 * SS θ)
        ≤ ∫ θ in Iθ, (2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) := hmono
      _ = 2 * (∫ θ in Iθ, (g s θ) ^ 2 * SS θ) + 2 * (∫ θ in Iθ, (h s θ) ^ 2 * SS θ) := by
          rw [MeasureTheory.integral_add (hg.const_mul 2) (hh.const_mul 2),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## The pointwise splittings of the radial iterates -/

/-- `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant. -/
theorem DzIter_two_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ s θ
      = Work.Spaces.DzIter 1 Ψ s θ + s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ := by
  have h := Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hS hs hθ
  have hq : Work.FTS.EllipticEst.DzAmgm.Qop Ψ s θ
      = s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ := rfl
  rw [hq] at h
  linarith [h]

/-- `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)` on the open quadrant. -/
theorem DzIter_three_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter 3 Ψ s θ
      = Work.Spaces.DzIter 2 Ψ s θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have h1 : Work.FTS.EllipticEst.DzAmgm.Qop (Work.Spaces.Dz Ψ) s θ
      = Work.Spaces.DzIter 2 (Work.Spaces.Dz Ψ) s θ
        - Work.Spaces.DzIter 1 (Work.Spaces.Dz Ψ) s θ :=
    Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hS.Dz hs hθ
  have h2 : Work.FTS.EllipticEst.DzAmgm.Qop (Work.Spaces.Dz Ψ) s θ
      = Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    have h := Work.FTS.EllipticEst.DzAmgm.Qop_Dz_eq hS hs hθ
    have hq : Work.FTS.EllipticEst.DzAmgm.Qop Ψ
        = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl
    rw [hq] at h
    exact h
  have h4 : Work.Spaces.DzIter 2 (Work.Spaces.Dz Ψ) s θ = Work.Spaces.DzIter 3 Ψ s θ := rfl
  have h5 : Work.Spaces.DzIter 1 (Work.Spaces.Dz Ψ) s θ = Work.Spaces.DzIter 2 Ψ s θ := rfl
  rw [h4, h5] at h1
  linarith [h1, h2]

/-- **The `θ`-energy bounds for the radial iterates `D_z^j Ψ`, `1 ≤ j ≤ 3`.**

On a compact radial interval `[a,b] ⊂ (0,∞)` every `thetaE (D_z^j Ψ)` (`1 ≤ j ≤ 3`) is
dominated by a constant times `1 + Eref Ψ`, and every weighted slice square
`(D_z^j Ψ(s,·))² sEta` is integrable.  The only analytic input is the Poincaré bound
`thetaE_pz_le` for `∂_zΨ`; the levels `j = 2, 3` follow from the algebraic splittings
`D_z²Ψ = D_zΨ + z²∂_z²Ψ` and `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)` (with `Eref`'s third and fourth
summands). -/
theorem sliceEnergyBounds {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a → a < b → ∃ K : ℝ, 0 < K ∧
      (MeasureTheory.IntegrableOn (Eref Ψ) (Set.Icc a b)) ∧
      (∀ s ∈ Set.Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.DzIter j Ψ s θ) ^ 2 * SS θ) Iθ) ∧
      (∀ s ∈ Set.Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        thetaE (Work.Spaces.DzIter j Ψ) s ≤ K * (1 + Eref Ψ s)) := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  have hSG : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul (hSΨ.pzIter 2)
  have hRef : MeasureTheory.IntegrableOn (Eref Ψ) (Set.Icc a b) := by
    have h1 := (ws_thetaE_integrable hSB h.memB 0 (Nat.zero_le k) ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h2 := (ws_thetaE_integrable hSB h.memB 1 hk ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h3 := (ws_thetaE_integrable hSG h.memA 0 (Nat.zero_le k) ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h4 := (ws_thetaE_integrable hSG h.memA 1 hk ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    unfold Eref
    exact ((h1.add h2).add h3).add h4
  obtain ⟨Kp, hKp0, hKp⟩ := thetaE_pz_le hk h ha hab
  -- the square of the radial variable on `[a,b]`
  set Mb : ℝ := max 1 (b ^ 2) with hMbdef
  have hMb1 : (1 : ℝ) ≤ Mb := by rw [hMbdef]; exact le_max_left _ _
  have hs2Mb : ∀ s ∈ Set.Icc a b, s ^ 2 ≤ Mb := by
    intro s hs
    rw [hMbdef]
    rcases le_total 1 b with hb | hb
    · exact le_trans (by nlinarith [hs.1, hs.2, ha]) (le_max_right _ _)
    · have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2, hb, ha]
      exact le_trans hs2 (le_max_left _ _)
  set K1 : ℝ := Kp * Mb + 1 with hK1def
  have hK10 : (0 : ℝ) < K1 := by rw [hK1def]; positivity
  set K2 : ℝ := 2 * K1 + 2 with hK2def
  set K3 : ℝ := 2 * K2 + 2 with hK3def
  set K : ℝ := max K1 (max K2 K3) with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; exact lt_of_lt_of_le hK10 (le_max_left _ _)
  have hK1K : K1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK2K : K2 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3K : K3 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the `j = 1` level
  have hint1 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 1 Ψ s θ) ^ 2 * SS θ) Iθ :=
    fun s hs => (thetaE_const_mul (X := Work.Spaces.pz Ψ) (c := s) (hKp s hs).1).1
  have hle1 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 1 Ψ) s ≤ K1 * (1 + Eref Ψ s) := by
    intro s hs
    have h1 : thetaE (Work.Spaces.DzIter 1 Ψ) s = s ^ 2 * thetaE (Work.Spaces.pz Ψ) s :=
      (thetaE_const_mul (X := Work.Spaces.pz Ψ) (c := s) (hKp s hs).1).2
    have h2 := (hKp s hs).2
    have h3 : s ^ 2 ≤ Mb := hs2Mb s hs
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hKpM : Kp * Mb ≤ K1 := by rw [hK1def]; linarith
    rw [h1]
    calc s ^ 2 * thetaE (Work.Spaces.pz Ψ) s
        ≤ Mb * (Kp * (1 + Eref Ψ s)) :=
          mul_le_mul h3 h2 (thetaE_nonneg _ _) (by positivity)
      _ = Kp * Mb * (1 + Eref Ψ s) := by ring
      _ ≤ K1 * (1 + Eref Ψ s) := mul_le_mul_of_nonneg_right hKpM hEref0
  -- the `j = 2` level
  have hint2 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 2 Ψ s θ) ^ 2 * SS θ) Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact (thetaE_add_le (f := Work.Spaces.DzIter 2 Ψ) (g := Work.Spaces.DzIter 1 Ψ)
      (h := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (s := s)
      (fun θ hθ => DzIter_two_eq hSΨ hs0 hθ)
      (hint1 s hs)
      (by
        have hh := ws_slot_slice hSG h.memA 0 (Nat.zero_le k) hs0
        simpa only [Work.Spaces.DzIter_zero] using hh)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 2 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 2).continuousOn.pow 2).mul ws_contOn_sEta)).1
  have hle2 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 2 Ψ) s ≤ K2 * (1 + Eref Ψ s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsplit := (thetaE_add_le (f := Work.Spaces.DzIter 2 Ψ) (g := Work.Spaces.DzIter 1 Ψ)
      (h := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (s := s)
      (fun θ hθ => DzIter_two_eq hSΨ hs0 hθ)
      (hint1 s hs)
      (by
        have hh := ws_slot_slice hSG h.memA 0 (Nat.zero_le k) hs0
        simpa only [Work.Spaces.DzIter_zero] using hh)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 2 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 2).continuousOn.pow 2).mul ws_contOn_sEta)).2
    have h1 := hle1 s hs
    have h2 := Eref_ge_thetaE_G Ψ s
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hK2eq : K2 = 2 * K1 + 2 := hK2def
    calc thetaE (Work.Spaces.DzIter 2 Ψ) s
        ≤ 2 * thetaE (Work.Spaces.DzIter 1 Ψ) s
            + 2 * thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s := hsplit
      _ ≤ 2 * (K1 * (1 + Eref Ψ s)) + 2 * Eref Ψ s := by linarith
      _ ≤ K2 * (1 + Eref Ψ s) := by rw [hK2eq]; nlinarith [hEref0]
  -- the `j = 3` level
  have hint3 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 3 Ψ s θ) ^ 2 * SS θ) Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact (thetaE_add_le (f := Work.Spaces.DzIter 3 Ψ) (g := Work.Spaces.DzIter 2 Ψ)
      (h := Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (s := s)
      (fun θ hθ => DzIter_three_eq hSΨ hs0 hθ)
      (hint2 s hs)
      (ws_slot_slice hSG h.memA 1 hk hs0)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 3).continuousOn.pow 2).mul ws_contOn_sEta)).1
  have hle3 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 3 Ψ) s ≤ K3 * (1 + Eref Ψ s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsplit := (thetaE_add_le (f := Work.Spaces.DzIter 3 Ψ) (g := Work.Spaces.DzIter 2 Ψ)
      (h := Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (s := s)
      (fun θ hθ => DzIter_three_eq hSΨ hs0 hθ)
      (hint2 s hs)
      (ws_slot_slice hSG h.memA 1 hk hs0)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 3).continuousOn.pow 2).mul ws_contOn_sEta)).2
    have h1 := hle2 s hs
    have h2 := Eref_ge_thetaE_DzG Ψ s
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hK3eq : K3 = 2 * K2 + 2 := hK3def
    calc thetaE (Work.Spaces.DzIter 3 Ψ) s
        ≤ 2 * thetaE (Work.Spaces.DzIter 2 Ψ) s
            + 2 * thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
          hsplit
      _ ≤ 2 * (K2 * (1 + Eref Ψ s)) + 2 * Eref Ψ s := by linarith
      _ ≤ K3 * (1 + Eref Ψ s) := by rw [hK3eq]; nlinarith [hEref0]
  refine ⟨K, hK0, hRef, ?_, ?_⟩
  · intro s hs j hj1 hj3
    interval_cases j
    · exact hint1 s hs
    · exact hint2 s hs
    · exact hint3 s hs
  · intro s hs j hj1 hj3
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    interval_cases j
    · exact le_trans (hle1 s hs) (mul_le_mul_of_nonneg_right hK1K hEref0)
    · exact le_trans (hle2 s hs) (mul_le_mul_of_nonneg_right hK2K hEref0)
    · exact le_trans (hle3 s hs) (mul_le_mul_of_nonneg_right hK3K hEref0)

/-! ## Box integrability of `(∂_z D_z^j Ψ)² sin(2θ)^{-η}` and the moment slices -/

/-- **The box integrability hypothesis of the moment relation.**  For `j ≤ 2` the uncurried
function `(s,θ) ↦ (∂_z D_z^j Ψ(s,θ))² sin(2θ)^{-η}` is integrable on the box `[a,b] × Iθ`:
the radial derivative is `D_z^{j+1}Ψ/s` and the `θ`-energy of `D_z^{j+1}Ψ` is controlled by
`sliceEnergyBounds`. -/
theorem moment_box {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Iθ) := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h a b ha hab
  -- the integrand and its basic properties
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
    ((hSΨ.DzIter j).pz.continuousOn.pow 2).mul ws_contOn_sEta
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Iθ,
      0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  have hsl' : ∀ s ∈ Set.Icc a b, MeasureTheory.Integrable (fun θ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Iθ) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hbase := hsl s hs (j + 1) (by omega) (by omega)
    have hfun : (fun θ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun θ => (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ) := by
      funext θ
      show (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ)
      have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
          = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
      rw [hid, Work.FTS.EllipticEst.sEta, mul_pow]
      have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs0)
      field_simp
    rw [hfun]
    exact hbase.const_mul _
  have hint' : MeasureTheory.Integrable
      (fun s => ∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have haesm : AEStronglyMeasurable
        (fun s => ∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Icc a b)) := by
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
      have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha.le).integral_prod_right'
        (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
      simpa only [Function.uncurry_apply_pair] using h
    have hvol : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hdom : MeasureTheory.Integrable
        (fun s => (a ^ 2)⁻¹ * (K * (1 + Eref Ψ s))) (volume.restrict (Set.Icc a b)) :=
      (((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).add hEref).const_mul K).const_mul _
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hval : (∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = (s ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter (j + 1) Ψ) s := by
      have hfun : (fun θ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = fun θ => (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ) := by
        funext θ
        show (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ)
        have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
            = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
        rw [hid, Work.FTS.EllipticEst.sEta, mul_pow]
        have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs0)
        field_simp
      rw [hfun, MeasureTheory.integral_const_mul]
      rfl
    rw [hval, Real.norm_of_nonneg (mul_nonneg (by positivity) (thetaE_nonneg _ _))]
    have h2 : thetaE (Work.Spaces.DzIter (j + 1) Ψ) s ≤ K * (1 + Eref Ψ s) :=
      hbd s hs (j + 1) (by omega) (by omega)
    have h3 : (s ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < s ^ 2) (by positivity : (0 : ℝ) < a ^ 2)).mpr
        (by nlinarith [hs.1, ha])
    exact mul_le_mul h3 h2 (thetaE_nonneg _ _) (by positivity)
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hcont hnn hsl' hint'

/-- **The slice integrability hypothesis of the moment relation**: for `j ≤ 2` and `z > 0` the
angular slice `θ ↦ D_z^j Ψ(z,θ) sinθcos²θ` is integrable.  For `j = 0` this is
`Psi_slice_sinCos2_integrable`; for `j = 1, 2` it is `ws_absMoment` together with the
`θ`-energy bound of `sliceEnergyBounds`. -/
theorem moment_slice {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ
        * Work.Elliptic.sinCos2 θ) Iθ := by
  intro z hz
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  rcases Nat.eq_or_lt_of_le (Nat.zero_le j) with h0 | h0
  · subst h0
    -- `j = 0`: the slice of `Ψ` itself
    have hbase := Psi_slice_sinCos2_integrable hk h z hz
    have haesm : AEStronglyMeasurable (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Iθ) := by
      have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
        simp only [Work.Elliptic.sinCos2]; fun_prop
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        (hSΨ.continuousOn.mul hcontσ.continuousOn) hz
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have hsg0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.sinCos2]
      exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
        (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsg0]
    exact le_rfl
  · -- `j = 1, 2`: the mean value bound of `ws_absMoment`
    have hj1 : 1 ≤ j := h0
    obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h (z / 2) (z + 1)
      (by linarith) (by linarith)
    have hzmem : z ∈ Set.Icc (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hgm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
        (volume.restrict Iθ) :=
      ws_aesm_slice (hSΨ.DzIter j) hz
    exact (ws_absMoment hgm (hsl z hzmem j hj1 (by omega))).1

/-- **Local integrability of `F_*(D_z^j Ψ)/r` for `j = 2, 3`.**  The moment is bounded by
`π/2 + thetaE (D_z^j Ψ)` (`ws_absMoment`), which is dominated by `1 + Eref Ψ`; dividing by
`r ≥ c > 0` preserves local integrability. -/
theorem moment_div_integrableOn_Icc {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj1 : 2 ≤ j) (hj3 : j ≤ 3) {c d : ℝ}
    (hc : 0 < c) (hcd : c < d) :
    MeasureTheory.IntegrableOn
      (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r) (Set.Icc c d) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h c d hc hcd
  have hvol : (volume : Measure ℝ) (Set.Icc c d) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.Integrable
      (fun r => c⁻¹ * (Real.pi / 2 + K * (1 + Eref Ψ r))) (volume.restrict (Set.Icc c d)) := by
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => Real.pi / 2) (Set.Icc c d) :=
      MeasureTheory.integrableOn_const (C := Real.pi / 2) hvol
    have h2 : MeasureTheory.IntegrableOn (fun r => K * (1 + Eref Ψ r)) (Set.Icc c d) :=
      ((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).add hEref).const_mul K
    exact (h1.add h2).const_mul (c⁻¹)
  have haesm : AEStronglyMeasurable
      (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r)
      (volume.restrict (Set.Icc c d)) := by
    have h1 : AEStronglyMeasurable (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r)
        (volume.restrict (Set.Icc c d)) :=
      aesm_fstar_Icc (hSΨ.DzIter j).continuousOn hc.le
    have h2 : AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Icc c d)) :=
      (continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le hc hx.1))).aestronglyMeasurable
        measurableSet_Icc
    exact (h1.mul h2).congr (Filter.Eventually.of_forall (fun r => by
      show Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r * r⁻¹
        = Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r
      rw [div_eq_mul_inv]))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le hc hr.1
  -- the pointwise bound on the moment
  have hgm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j Ψ r θ)
      (volume.restrict Iθ) := ws_aesm_slice (hSΨ.DzIter j) hr0
  have habs : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| ≤ Real.pi / 2 + K * (1 + Eref Ψ r) := by
    have h1 : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r|
        ≤ ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.Fstar]
      calc |∫ θ in Iθ, Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ|
          ≤ ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ| :=
            abs_integral_le_integral_abs
        _ = ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
            rw [abs_mul]
            congr 1
            rw [Work.Elliptic.sinCos2]
            exact abs_of_nonneg (mul_nonneg (Real.sin_nonneg_of_mem_Icc
              ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _))
    have h2 := (ws_absMoment hgm (hsl r hr j (by omega) (by omega))).2
    have h3 : thetaE (Work.Spaces.DzIter j Ψ) r ≤ K * (1 + Eref Ψ r) :=
      hbd r hr j (by omega) (by omega)
    have h3' : (∫ θ in Iθ, (Work.Spaces.DzIter j Ψ r θ) ^ 2 * SS θ) ≤ K * (1 + Eref Ψ r) := h3
    linarith [h1, h2, h3']
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
  have hnum : 0 ≤ Real.pi / 2 + K * (1 + Eref Ψ r) := by
    nlinarith [hK0, Real.pi_pos, Eref_nonneg Ψ r]
  have h1 : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| / r
      ≤ (Real.pi / 2 + K * (1 + Eref Ψ r)) * r⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right habs (by positivity)
  have h2 : (Real.pi / 2 + K * (1 + Eref Ψ r)) * r⁻¹
      ≤ (Real.pi / 2 + K * (1 + Eref Ψ r)) * c⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ hnum
    rw [inv_le_inv₀ hr0 hc]
    exact hr.1
  have h3 : (Real.pi / 2 + K * (1 + Eref Ψ r)) * c⁻¹
      = c⁻¹ * (Real.pi / 2 + K * (1 + Eref Ψ r)) := by ring
  linarith [h1, h2, h3]

/-- **The chain rule for the moment `F_*(D_z^j Ψ)`**, `j ≤ 2`:
`F_*(D_z^j Ψ)(b) - F_*(D_z^j Ψ)(a) = ∫_a^b F_*(D_z^{j+1} Ψ)(r)/r dr`.  It is
`moment_relation` (`Work.FTS.EllipticEst.moment_relation`) applied to `D_z^j Ψ`. -/
theorem moment_chain {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) b
          - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) r / r := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmain := Work.FTS.EllipticEst.moment_relation (Work.Spaces.DzIter j Ψ)
    (hSΨ.DzIter j) (moment_box hk h j hj) (moment_slice hk h j hj) ha hab
  have hinner : ∀ s ∈ Set.Icc a b,
      (∫ θ in Iθ, Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) s / s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    rw [Work.Elliptic.Fstar]
    have hfun : (fun θ => Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ * Work.Elliptic.sinCos2 θ)
        = fun θ => s⁻¹ * (Work.Spaces.DzIter (j + 1) Ψ s θ * Work.Elliptic.sinCos2 θ) := by
      funext θ
      have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
          = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
      rw [hid]
      field_simp
    rw [hfun, MeasureTheory.integral_const_mul]
    ring
  rw [hmain]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hinner]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le]
  ring

theorem wsMomentChain (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the primitive of `F_*(D_zΨ)/r` vanishes identically
  have hprim1 : ∀ s w : ℝ, 0 < s → s < w →
      (∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) = 0 := by
    intro s w hs hsw
    have h0 := moment_chain hk h 0 (by norm_num) s w hs hsw
    simp only [Work.Spaces.DzIter_zero] at h0
    rw [h.orthPsi w (lt_trans hs hsw), h.orthPsi s hs, sub_self] at h0
    linarith [h0]
  -- `F_*(D_zΨ)` is continuous on `(0,∞)`, being a primitive of `F_*(D_z²Ψ)/r`
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hs0 : 0 < z / 2 := by linarith
    have hInt2 : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) volume (z / 2) (2 * z) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact moment_div_integrableOn_Icc hk h 2 le_rfl (by norm_num) hs0 (by linarith)
    have hcontprim : ContinuousOn (fun w => ∫ r in z / 2..w,
        Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt2 (by
        rw [Set.uIcc_of_le (by linarith)]
        exact ⟨le_rfl, by linarith⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : z / 2 ≤ 2 * z)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      have h1 := moment_chain hk h 1 (by norm_num) (z / 2) w hs0 hw
      linarith [h1]
    have hcontc : ContinuousAt (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (z / 2)
        + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) z :=
      continuousAt_const.add (hcontprim.continuousAt hmem)
    exact (hcontc.congr hev.symm).continuousWithinAt
  have hA1zero : ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith
    have hev : (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      exact hprim1 (z / 2) w hs0 hw
    have hder0 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) 0 z :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
    have hcontA : ContinuousOn (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        (Set.Ioi 0) := hcont1.div continuousOn_id (fun r hr => ne_of_gt hr)
    have hcontAz : ContinuousAt (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) z :=
      hcontA.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hder1 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z / z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hcontAz
      · have hsub : Set.uIcc (z / 2) z ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le (by linarith)]
          exact fun r hr => lt_of_lt_of_le hs0 hr.1
        exact ((hcont1.mono hsub).div continuousOn_id
          (fun r hr => ne_of_gt (hsub hr))).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcontA z hz
    have huniq := hder1.unique hder0
    exact (div_eq_zero_iff.mp huniq).resolve_right (ne_of_gt hz)
  -- the primitive of `F_*(D_z²Ψ)/r` vanishes identically
  have hprim2 : ∀ s w : ℝ, 0 < s → s < w →
      (∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) = 0 := by
    intro s w hs hsw
    have h1 := moment_chain hk h 1 (by norm_num) s w hs hsw
    rw [hA1zero w (lt_trans hs hsw), hA1zero s hs, sub_self] at h1
    linarith [h1]
  -- `F_*(D_z²Ψ)` is continuous on `(0,∞)`, being a primitive of `F_*(D_z³Ψ)/r`
  have hcont2 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hs0 : 0 < z / 2 := by linarith
    have hInt3 : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) volume (z / 2) (2 * z) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact moment_div_integrableOn_Icc hk h 3 (by norm_num) le_rfl hs0 (by linarith)
    have hcontprim : ContinuousOn (fun w => ∫ r in z / 2..w,
        Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt3 (by
        rw [Set.uIcc_of_le (by linarith)]
        exact ⟨le_rfl, by linarith⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : z / 2 ≤ 2 * z)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      have h1 := moment_chain hk h 2 (by norm_num) (z / 2) w hs0 hw
      linarith [h1]
    have hcontc : ContinuousAt (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) (z / 2)
        + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) z :=
      continuousAt_const.add (hcontprim.continuousAt hmem)
    exact (hcontc.congr hev.symm).continuousWithinAt
  have hA2zero : ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith
    have hev : (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      exact hprim2 (z / 2) w hs0 hw
    have hder0 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) 0 z :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
    have hcontA : ContinuousOn (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        (Set.Ioi 0) := hcont2.div continuousOn_id (fun r hr => ne_of_gt hr)
    have hcontAz : ContinuousAt (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) z :=
      hcontA.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hder1 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        (Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z / z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hcontAz
      · have hsub : Set.uIcc (z / 2) z ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le (by linarith)]
          exact fun r hr => lt_of_lt_of_le hs0 hr.1
        exact ((hcont2.mono hsub).div continuousOn_id
          (fun r hr => ne_of_gt (hsub hr))).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcontA z hz
    have huniq := hder1.unique hder0
    exact (div_eq_zero_iff.mp huniq).resolve_right (ne_of_gt hz)
  intro j hj z hz
  interval_cases j
  · exact h.orthPsi z hz
  · exact hA1zero z hz
  · exact hA2zero z hz

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.ws_DzIter_two_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.QangDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The primitive identity for the angular moments

`Qang g j` is a primitive of `x ↦ Qang g (j+1) x / x` on `(0,∞)`, for `j ≤ 3`.  This is the
identity from which both halves of `QangDiff` follow. -/

/-- **The primitive identity for `z₀ ≤ z`.**  For every `j ≤ 3` and `0 < z₀ ≤ z`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`.

The proof integrates the slice formula
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`
(`QangSliceFTC`) against `Ktheta` and swaps the two integrations with Fubini on the box
`uIoc z₀ z ×ˢ uIoc 0 (π/2)`, whose joint integrability is `QangBoxIntegrable`. -/
theorem Qang_primitive_le (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) (hle : z₀ ≤ z) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  -- integral integrability of the two angular slices over `0..π/2`
  have hslice : ∀ {w : ℝ}, 0 < w →
      IntervalIntegrable (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g w θ)
        volume 0 (π/2) := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    refine (QangSliceIntegrable hsm hmem (by omega : j ≤ 4) hw).mono_set ?_
    rw [Work.Spaces.Iθ]
    exact Set.Ioc_subset_Icc_self
  have hIi_z := hslice hz
  have hIi_z₀ := hslice hz₀
  -- Step 1: split the difference of the two θ-integrals
  have h1 : Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
          - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ) := by
    rw [Qang_eq_intervalIntegral g j z, Qang_eq_intervalIntegral g j z₀]
    exact (intervalIntegral.integral_sub hIi_z hIi_z₀).symm
  -- Step 2: factor out the angular weight
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
        - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    ring
  -- Step 3: the slice formula
  have h3 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine ae_imp_uIoc (fun θ hθ1 hθ2 => ?_)
    rw [QangSliceFTC hsm j hz hz₀ ⟨hθ1, hθ2⟩]
  -- Step 4: pull the angular weight inside the inner integral
  have h4 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact (intervalIntegral.integral_const_mul (Work.Elliptic.Ktheta θ)
      (fun x => Work.Spaces.DzIter (j + 1) g x θ / x)).symm
  -- Step 5: Fubini on the box
  have hFbox : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * (Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1))
      (Set.uIoc z₀ z ×ˢ Set.uIoc 0 (π / 2)) :=
    (QangBoxIntegrable hsm hmem hj hz₀ hle).1.congr_fun (fun p _ => by ring)
      ((measurableSet_uIoc).prod measurableSet_uIoc)
  have h5 : (∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) :=
    (MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun x θ => Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter (j + 1) g x θ / x)) hFbox).symm
  -- Step 6: identify the inner integral with `Qang g (j+1) x / x`
  have h6 : (∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hq : Work.Elliptic.Qang g (j + 1) x
        = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ :=
      Qang_eq_intervalIntegral g (j + 1) x
    have hfun : (fun θ : ℝ => Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter (j + 1) g x θ / x))
        = fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x := by
      funext θ; ring
    rw [hfun, hq, intervalIntegral.integral_div]
  rw [h1, h2, h3, h4, h5, h6]

/-- **The primitive identity.**  For every `j ≤ 3` and every `z, z₀ > 0`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`. -/
theorem Qang_primitive (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  rcases le_total z₀ z with hle | hle
  · exact Qang_primitive_le α g hsm hmem hj hz hz₀ hle
  · have h := Qang_primitive_le α g hsm hmem hj hz₀ hz hle
    rw [intervalIntegral.integral_symm z₀ z] at h
    linarith [h]

/-- `z ↦ Qang g (j+1) z / z` is continuous at every `z > 0`, for `j ≤ 2`: this is the
integrand of the primitive identity, and it is continuous because `Qang g (j+1)` is
(`j + 1 ≤ 3`) and `z ≠ 0`. -/
theorem continuousAt_Qang_div {g : ℝ → ℝ → ℝ} {j : ℕ} {z : ℝ}
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0))
    (hz : 0 < z) :
    ContinuousAt (fun x => Work.Elliptic.Qang g (j + 1) x / x) z :=
  (hcont.continuousAt (isOpen_Ioi.mem_nhds hz)).div continuousAt_id (ne_of_gt hz)

/-- `Qang g j` is continuous on `(0,∞)` for `j ≤ 3`: it is (a constant plus) the primitive of
`x ↦ Qang g (j+1) x / x`, which is integrable on every compact subinterval of `(0,∞)`. -/
theorem continuousOn_Qang (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ 2 * z := by linarith
  -- integrability of the integrand on a closed interval around `z`
  obtain ⟨-, hint⟩ := QangBoxIntegrable hsm hmem hj hz2pos hle1
  have hintIcc : MeasureTheory.IntegrableOn (fun x => Work.Elliptic.Qang g (j + 1) x / x)
      (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle1]
    refine (integrableOn_Icc_iff_integrableOn_Ioc (a := z / 2)
      (f := fun x => Work.Elliptic.Qang g (j + 1) x / x)).mpr ?_
    rwa [Set.uIoc_of_le hle1] at hint
  have hcont := intervalIntegral.continuousOn_primitive_interval hintIcc
  -- the primitive is `Qang g j · - Qang g j (z/2)` on the interval
  have hcongr : Set.EqOn (fun x => ∫ t in z / 2..x, Work.Elliptic.Qang g (j + 1) t / t)
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := by
    intro x hx
    have hxpos : 0 < x := by
      rw [Set.uIcc_of_le hle1] at hx
      linarith [hx.1]
    exact (Qang_primitive α g hsm hmem hj hxpos hz2pos).symm
  have hcont2 : ContinuousOn
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := hcont.congr hcongr.symm
  have hnhds : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hle1]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hcat : ContinuousAt
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2)) z :=
    hcont2.continuousAt hnhds
  exact ((hcat.add_const (Work.Elliptic.Qang g j (z / 2))).congr
    (Filter.Eventually.of_forall (fun x => by ring))).continuousWithinAt

/-- **`Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with derivative
`Qang g (j+1) z / z`**: the primitive identity exhibits it as the primitive of a function
which is continuous at `z` (`continuousOn_Qang` at level `j + 1 ≤ 3`). -/
theorem hasDerivAt_Qang (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0)) :
    HasDerivAt (fun z => Work.Elliptic.Qang g j z)
      (Work.Elliptic.Qang g (j + 1) z / z) z := by
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ z := by linarith
  obtain ⟨-, hint⟩ := QangBoxIntegrable hsm hmem (by omega : j ≤ 3) hz2pos hle1
  have hInt : IntervalIntegrable (fun x => Work.Elliptic.Qang g (j + 1) x / x) volume
      (z / 2) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle1]
    rwa [Set.uIoc_of_le hle1] at hint
  have hcontAt := continuousAt_Qang_div hcont hz
  have hcontOn : ContinuousOn (fun x => Work.Elliptic.Qang g (j + 1) x / x) (Set.Ioi 0) :=
    hcont.div continuousOn_id (fun x hx => ne_of_gt hx)
  have hsmAt := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hcontOn z hz
  have hprim : HasDerivAt (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x)
      (Work.Elliptic.Qang g (j + 1) z / z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsmAt hcontAt
  have heq : (fun u => Work.Elliptic.Qang g j u - Work.Elliptic.Qang g j (z / 2))
      =ᶠ[𝓝 z] (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    exact Qang_primitive α g hsm hmem (by omega : j ≤ 3) hu hz2pos
  have h1 := hprim.congr_of_eventuallyEq heq
  have h2 := h1.add_const (Work.Elliptic.Qang g j (z / 2))
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by ring))

/-- `z`-differentiation of the angular moments `Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`
in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity/`SmoothNbhd`):
`Qang g j` is continuous on `(0,∞)` for `j ≤ 3`, and for `j ≤ 2` it is differentiable at every
`z > 0` with `∂_z (Qang g j) z = Qang g (j+1) z / z`.

Route.  For each `θ ∈ (0,π/2)` the slice `z ↦ D_z^j g z θ` is `C^∞` on `Ioi (-1)`
(`Work.FTS.LocData.SmoothQuad.curry_z`), and `z·∂_z(D_z^j g) = D_z^{j+1} g`, so the primitive
formula (FTC) on `z₀..z` gives
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^z D_z^{j+1} g x θ / x dx` for every `θ ∈ (0,π/2)`.
Multiply by `Ktheta θ` and integrate in `θ`: the difference of the two `θ`-integrals is the
`θ`-integral of the difference (each `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ` for
`z > 0`, by Cauchy–Schwarz with `∫_θ (D_z^j g z θ)² < ∞`; the latter follows from `hmem.1` and
the pointwise domination of `(D_z^j g)²` by the `j`-th summand of `HkIntegrand α 4 g`, which is
`Work.Spaces.sq_le_HkIntegrand_z`).  Then Fubini/Tonelli on the box
`[min z z₀, max z z₀] × Iθ`: the joint integrand `(x,θ) ↦ Ktheta θ · D_z^{j+1} g x θ / x` is
integrable there because `|Ktheta| ≤ 3` and Cauchy–Schwarz bounds it by
`(∫∫ (D_z^{j+1} g)²/x²)^{1/2}`, while on the box `1/x² ≤ C·w(x)²·sin(2θ)^{-η}`
(`w ≥ w_min > 0` since `x ≥ min z z₀ > 0`, and `sin(2θ)^{-η} ≥ 1`) and the `(j+1)`-th pure
`D_z` slot of `HkIntegrand α 4 g` is integrable over `Iz × Iθ` by `hmem`; continuity of the
joint integrand on the box gives measurability.  This yields, for all `z, z₀ > 0`,
`Qang g j z - Qang g j z₀ = ∫_{z₀}^z Qang g (j+1) x / x dx`, and also that
`x ↦ Qang g (j+1) x / x` is integrable on each compact subinterval of `(0,∞)`.
Consequently `Qang g j` is continuous on `(0,∞)` (it is a primitive plus a constant), and for
`j ≤ 2` the right-hand integrand `x ↦ Qang g (j+1) x / x` is continuous at `z` (continuity of
`Qang g (j+1)`, obtained at the level `j+1 ≤ 3`), so
`HasDerivAt (Qang g j) (Qang g (j+1) z / z) z`.
(`j ≤ 3` in the continuity part is sharp: continuity of `Qang g 3` uses the Fubini identity at
level 3, hence the 4-th pure `D_z` slot of `HkMem α 4 g`.)
Useful existing siblings (all with the analyticity hypothesis `Spaces.SmoothNbhd`, which must
NOT be used): `Work.Elliptic.Qang_deriv_mul`, `Work.Elliptic.L12Iterate` (and
`Work.EllipticEst.Blocks.L12Gen.L12Iterate_k`), `Work.Elliptic.L12k0`. -/
theorem QangDiff (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 3 → ContinuousOn (Work.Elliptic.Qang g j) (Set.Ioi 0)) := by
  have hcont : ∀ j : ℕ, j ≤ 3 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => continuousOn_Qang α g hsm hmem hj
  refine ⟨?_, hcont⟩
  intro j hj z hz
  exact hasDerivAt_Qang α g hsm hmem hj hz (hcont (j + 1) (by omega))

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.SepFactor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false

/-! ## Separability of the iterated operators -/

/-- `D_z^j` of a separable datum `ρ(z)·Γ(θ)` only differs the radial factor. -/
theorem DzIter_sepGam (α : ℝ) (ρ : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.Gam α θ := by
  have h := Work.FTS.LocData.DzIter_mul_theta_factor j (fun θ => Work.Spaces.Gam α θ)
    (fun z _ => ρ z)
  rw [show (fun z θ : ℝ => ρ z * Work.Spaces.Gam α θ)
      = (fun z θ : ℝ => Work.Spaces.Gam α θ * ρ z) from (by funext z θ; exact mul_comm _ _), h]
  funext z θ
  ring

/-- `D_θ^i` of a separable datum `ρ(z)·Γ(θ)` only differs the angular factor. -/
theorem DthIter_sepGam (α : ℝ) (ρ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => ρ z * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.FTS.LocData.ZFBase.DthIter_mul_left_z i ρ (fun _ θ' => Work.Spaces.Gam α θ')]
  funext z θ
  rw [Work.FTS.LocData.DthIter_gamFn_z_indep α i z 0 θ]

/-- **The mixed derivatives of a separable datum split**: for `f z θ = ρ z · Γ θ`,

  `D_z^j D_θ^i f z θ = (D_z^j ρ)(z)·(D_θ^i Γ)(θ)`. -/
theorem mixed_sepGam (α : ℝ) (ρ : ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => Work.Spaces.DzIter j (fun z _ => ρ z) z θ
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.Spaces.mixed, DthIter_sepGam α ρ i]
  have h := Work.FTS.LocData.DzIter_mul_theta_factor j
    (fun θ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) (fun z _ => ρ z)
  rw [show (fun z θ : ℝ => ρ z
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
      = (fun z θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * ρ z)
      from (by funext z θ; exact mul_comm _ _), h]
  funext z θ
  ring

/-- **`D_z^j ρ` does not depend on the angle.** -/
theorem DzIter_z_only_apply (ρ : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => ρ z) z θ = Work.Spaces.DzIter j (fun z _ => ρ z) z 0 := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z _ => ρ z)) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter j (fun z _ => ρ z)) z 0
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun w => ih w)

/-- Scalar multiples pass through `D_z`-iterates. -/
theorem DzIter_const_mul (c : ℝ) (f : Fn) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-! ## Congruence of the iterates under eventual equality in `z` -/

/-- `D_z`-iterates agree for functions which agree on a neighbourhood of `z`, uniformly in `θ`. -/
theorem eventDzIter_congr {f g : Fn} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = g z' θ') (j : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DzIter j f z' θ' = Work.Spaces.DzIter j g z' θ' := by
  induction j with
  | zero => exact h
  | succ j ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hev : (fun w : ℝ => Work.Spaces.DzIter j f w θ') =ᶠ[𝓝 z']
          (fun w : ℝ => Work.Spaces.DzIter j g w θ') :=
        Filter.eventually_of_mem (hUopen.mem_nhds hz') (fun w hw => hU hw θ')
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq]

/-- Pointwise form of `eventDzIter_congr`. -/
theorem eq_of_eventuallyEq_nhds {g h : ℝ → ℝ} {z : ℝ} (hz : g =ᶠ[𝓝 z] h) : g z = h z :=
  Filter.EventuallyEq.eq_of_nhds hz

theorem DzIter_congr_of_eventuallyEq {f g : Fn} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = g z' θ') (j : ℕ) :
    Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j g z θ := by
  have h' : (fun z' : ℝ => Work.Spaces.DzIter j f z' θ) =ᶠ[𝓝 z]
      (fun z' : ℝ => Work.Spaces.DzIter j g z' θ) :=
    (eventDzIter_congr h j).mono (fun z' hz' => hz' θ)
  exact eq_of_eventuallyEq_nhds (g := fun z' : ℝ => Work.Spaces.DzIter j f z' θ)
    (h := fun z' : ℝ => Work.Spaces.DzIter j g z' θ) (z := z) h'

/-- Pointwise form for functions of `z` alone. -/
theorem DzIter_z_congr_of_eventuallyEq {ρ σ : ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ρ z' = σ z') (j : ℕ) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => ρ z) z θ = Work.Spaces.DzIter j (fun z _ => σ z) z θ :=
  DzIter_congr_of_eventuallyEq (h.mono (fun z' hz' => fun _ => hz')) j

/-! ## The radial factor `locR` near the two ends of `(0,∞)` -/

/-- `locR` vanishes identically on a neighbourhood of any `z ∈ (0, min L (3/4))`. -/
theorem locR_eventuallyEq_zero {α L β z : ℝ} (hL : 0 < L) (hz0 : 0 < z) (hzL : z < L)
    (hzb : z < 3 / 4) : ∀ᶠ z' in 𝓝 z, locR α L β z' = 0 := by
  filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) L from ⟨hz0, hzL⟩),
    isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) (3 / 4) from ⟨hz0, hzb⟩)] with z' hz' hz''
  exact locR_eq_zero_of_le hL (le_of_lt hz'.1) (le_of_lt hz'.2) (le_of_lt hz''.2)

/-- Beyond `max (2L) (7/4)`, `locR` agrees with the (rescaled) plain profile
`-(α/c)·FM.Fstar`. -/
theorem locR_eventuallyEq_far {α L β z : ℝ} (hL : 0 < L) (hz : 2 * L < z) (hzb : 7 / 4 < z) :
    ∀ᶠ z' in 𝓝 z, locR α L β z' = -(α / Work.Spaces.c α) * Work.FM.Fstar z' := by
  filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Ioi.mem_nhds hzb] with z' hz' hz''
  rw [locR_apply, zfarR_eq_FM_Fstar_of_ge hL (le_of_lt hz'), bumpZ_eq_zero_of_ge (le_of_lt hz'')]
  ring

end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Zfar5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `D_z`-jet of `zfarR L` as the Leibniz sum of the jets of its two factors.** -/
theorem DzIter_zfarR_eq_sum (L : ℝ) (j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => zfarR L z) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
            * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ) := by
  have h := Work.FTS.LocData.DzIter_mul_smoothQuad j
    (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) (fun z _ => Work.FM.Fstar z)
    (θ := θ) hz
    (Work.FTS.LocData.ZFBase.contDiffOn_slice_oneSubChi L)
    (Work.FTS.LocData.ZFBase.contDiffOn_slice_FM_Fstar)
  simpa only [zfarR_apply] using h




end Work.FTS.LocDataExt
end
end
