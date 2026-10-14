import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.STHardBound
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotBoundQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.LWP.VorticityAPI
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-! ## `DzdIter` is the iterate of `Zop` -/

/-- `Work.Elliptic.Dzd` and `Work.Spaces.Zop` are the same operator `z ↦ z·u'(z)`, hence so are
their iterates. -/
theorem DzdIter_eq_Zop_iter (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j u = Work.Spaces.Zop^[j] u := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, Function.iterate_succ_apply']
      rfl

/-- Iterating `Zop` commutes with multiplication by a constant.  (Mathlib's
`deriv_const_mul_field` is unconditional.) -/
theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[j] (fun z => c * u z) = fun z => c * Work.Spaces.Zop^[j] u z := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext z
      simp only [Work.Spaces.Zop]
      rw [deriv_const_mul_field]
      ring

/-! ## The boundedness half: `ampA` -/

/-- `ampA α = (2/c(α))·φ` **as functions**; the identity holds for every `z` because both sides
vanish when `c(α) = 0` (`mul_inv` handles the totalised inverse). -/
theorem ampA_eq_const_mul_fA (α : ℝ) :
    Work.FTS.CoercivityFix.Transfer.ampA α
      = fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2) := by
  funext z
  simp only [Work.FTS.CoercivityFix.Transfer.ampA, div_eq_mul_inv]
  rw [mul_inv]
  ring

/-- **The boundedness half.**  All `(z∂_z)`-iterates of `ampA α` up to order `4` are bounded on
`(0,∞)` by `20·K₀`, where `K₀` is the chart bound of `E2Bound.zop_phi_bound`. -/
theorem ampA_dzdIter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hbd⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 4
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    linarith
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro j hj z hz
  have hb : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ := hbd j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j] (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Zop_iter_const_mul]
    _ = |2 / Work.Spaces.c α|
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := abs_mul _ _
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## The integrability half: `ampB` -/

/-- `ampB α = 2·fB` as functions. -/
theorem ampB_eq_two_mul_fB (α : ℝ) :
    Work.FTS.CoercivityFix.Transfer.ampB α = fun z => 2 * (z ^ 2 / (1 + z) ^ 3) := by
  funext z
  simp only [Work.FTS.CoercivityFix.Transfer.ampB, div_eq_mul_inv]
  ring

/-- The `(z∂_z)`-iterates of `ampB α` are twice the iterates of `z²/(1+z)³`, as functions. -/
theorem dzdIter_ampB_eq (α : ℝ) (j : ℕ) :
    Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α)
      = fun z => 2 * Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z := by
  rw [DzdIter_eq_Zop_iter, ampB_eq_two_mul_fB, Zop_iter_const_mul]
  rw [← DzdIter_eq_Zop_iter]

/-- **The integrability half**, given the two closed-form inputs. -/
theorem ampB_sq_w_integrable_of
    (hA : ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = rB j z)
    (hB : ∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (α : ℝ) :
    ∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  intro j hj
  have hG : MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hB j hj
  -- the two integrands agree pointwise on `Ioi 0`
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = 4 * ((rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro z hz
    rw [congrFun (dzdIter_ampB_eq α j) z, hA j hj z hz]
    ring
  have hG' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hG.mono_set Set.Ioi_subset_Ici_self
  have hae : (fun z : ℝ => (Work.Elliptic.DzdIter j
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z : ℝ => 4 * ((rB j z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpoint z hz
  have hF' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (hG'.const_mul 4).congr hae.symm
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ))
      = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  show MeasureTheory.Integrable
    (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2) (volume.restrict Work.Spaces.Iz)
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, ← hmeas]
  exact hF'

/-! ## The main theorem -/

theorem dzdIter_coeff_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) ∧
    (∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :=
  ⟨ampA_dzdIter_bound α hα hα1,
    ampB_sq_w_integrable_of (fun j hj z hz => rB_iter j hj z hz)
      (fun j hj => rB_sq_w_integrable j hj) α⟩

end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedPairAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## 1. Elementary facts about the weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sigθ_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem sigθ_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.AeColl.sigθ θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

theorem wt_nonneg (z : ℝ) : 0 ≤ Work.FTS.EllipticEst.AeColl.wt z := sq_nonneg _

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]

theorem one_le_wt_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.FTS.EllipticEst.AeColl.wt z := by
  have hw := one_le_w_of_pos hz
  have h0 : (0 : ℝ) ≤ Work.Spaces.w z := le_trans zero_le_one hw
  rw [Work.FTS.EllipticEst.AeColl.wt]
  nlinarith [hw, h0]

theorem wt_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.FTS.EllipticEst.AeColl.wt z ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_wt_of_pos hz))

theorem mem_Iz_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z ∈ Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]
  exact Set.mem_Ici.mpr hz

theorem mem_Iz_of_pos {z : ℝ} (hz : 0 < z) : z ∈ Work.Spaces.Iz :=
  mem_Iz_of_nonneg (le_of_lt hz)

/-! ## 2. The `k = 0` form of the `ℋ⁰`-integrand -/

theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : (∑ i ∈ Finset.range (0 + 1), (Work.Spaces.DzIter i f z θ *
      (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by simp
  have h2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (0 + 1),
      if 1 ≤ i ∧ i + j ≤ 0
      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by simp
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]
  by_cases hs0 : Real.sin (2 * θ) = 0
  · have hpow : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs0]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    have hsig0 : Work.FTS.EllipticEst.AeColl.sigθ θ = 0 := by
      rw [Work.FTS.EllipticEst.AeColl.sigθ, hs0]
      exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [hsig0, hpow, div_zero]
    ring
  · have hpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsin : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hpos]; norm_num
    have hsig : Work.FTS.EllipticEst.AeColl.sigθ θ
        = (Real.sin (2 * θ) ^ Work.Spaces.eta)⁻¹ := by
      rw [Work.FTS.EllipticEst.AeColl.sigθ, Real.rpow_neg (le_of_lt hpos)]
    rw [hsig, Work.FTS.EllipticEst.AeColl.wt, mul_pow, div_pow, hsin]
    ring

/-! ## 3. Slices and marginals of an `ℋ⁰`-honest function -/

/-- The angular slice of `f z · ²`, weighted by `wt z · sigθ`, is integrable on `Iθ`. -/
theorem integrableOn_sig_sq_wt_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
  (hmem.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => hkIntegrand_zero_eq α f hθ))

/-- The angular slice of `f z · ²`, weighted only by `sigθ`, is integrable on `(0, π/2)`. -/
theorem integrableOn_sig_mul_sq_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h2 : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hmem (le_of_lt hz)
  have h3 : Integrable (fun θ => (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ *
      (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  have h4 : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine h3.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ _
    have hwt := wt_ne_zero_of_pos hz
    calc (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ)
        = ((Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * Work.FTS.EllipticEst.AeColl.wt z)
            * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) := by ring
      _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ := by
          rw [inv_mul_cancel₀ hwt, one_mul]
      _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2 := by ring
  exact MeasureTheory.IntegrableOn.mono_set h4 (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- The radial marginal of `f² wt sigθ` is integrable. -/
theorem integrableOn_marginal_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      Work.Spaces.Iz :=
  hmem.2.congr (Filter.Eventually.of_forall (fun z =>
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_zero_eq α f hθ)))

/-- The radial marginal of `f² wt sigθ`, as an integrability statement on `(0,∞)`. -/
theorem integrableOn_marginal_Ioi_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (Set.Ioi 0) :=
  MeasureTheory.IntegrableOn.mono_set (integrableOn_marginal_of_HkMem α hmem) Set.Ioi_subset_Ici_self

/-- **AM–GM for the mixed marginal**: the absolute mixed angular marginal of `f` and `g` is
dominated by the sum of the two diagonal marginals (which contain the radial weight `wt z`). -/
theorem abs_mixed_slice_le (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ (∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfz : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hf (le_of_lt hz)
  have hgz : Integrable (fun θ => g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hg (le_of_lt hz)
  have hfz' := MeasureTheory.IntegrableOn.mono_set hfz hsub
  have hgz' := MeasureTheory.IntegrableOn.mono_set hgz hsub
  have hstep1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
    refine integral_mono_of_nonneg ?_ (hfz'.add hgz') ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ (hsub hθ)
      have hw1 := one_le_wt_of_pos hz
      have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
        nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
      calc |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|
          = Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]; ring
        _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hs0
        _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.wt z * (f z θ ^ 2 + g z θ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hs0
            nlinarith [hw1, sq_nonneg (f z θ), sq_nonneg (g z θ)]
        _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
              + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
                * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hstep2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ))
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    integral_add hfz' hgz'
  have hstep3a : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hfz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  have hstep3b : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hgz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  exact le_trans hstep1 (le_trans hstep2.le (add_le_add hstep3a hstep3b))

/-! ## 3b. Further `wt`-weighted comparisons -/

theorem wtB_nonneg (n : ℕ) : 0 ≤ Work.FTS.EllipticEst.AeColl.wtB n := by
  rw [Work.FTS.EllipticEst.AeColl.wtB]; positivity

/-- The angular slice of `σ f²` is integrable on `Iθ` (without the radial weight). -/
theorem integrableOn_sig_mul_sq_Iθ_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  have h2 : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hmem (le_of_lt hz)
  have h3 : Integrable (fun θ => (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ *
      (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  refine h3.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ _
  have hwt := wt_ne_zero_of_pos hz
  calc (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ)
      = ((Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * Work.FTS.EllipticEst.AeColl.wt z)
          * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) := by ring
    _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ := by
        rw [inv_mul_cancel₀ hwt, one_mul]
    _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2 := by ring

/-- **AM–GM for the mixed marginal, in `wt`-weighted form**: multiplying the angular integral
by `wt z` puts the radial weight *inside* the integral, where it can be compared with the two
diagonal `ℋ⁰`-marginals. -/
theorem abs_mixed_slice_wt_le (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ (∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfz : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hf (le_of_lt hz)
  have hgz : Integrable (fun θ => g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hg (le_of_lt hz)
  have hfz' := MeasureTheory.IntegrableOn.mono_set hfz hsub
  have hgz' := MeasureTheory.IntegrableOn.mono_set hgz hsub
  have hstep1 : Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.wt z
          * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ| := by
    rw [MeasureTheory.integral_const_mul]
  have hstep2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.wt z
          * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
    refine integral_mono_of_nonneg ?_ (hfz'.add hgz') ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
      exact mul_nonneg (wt_nonneg z) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ (hsub hθ)
      have hwt0 := wt_nonneg z
      have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
        nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
      calc Work.FTS.EllipticEst.AeColl.wt z
            * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|
          = (Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|))
              * Work.FTS.EllipticEst.AeColl.wt z := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]; ring
        _ ≤ (Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2))
              * Work.FTS.EllipticEst.AeColl.wt z :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hs0) hwt0
        _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
              + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
                * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hstep3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ))
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    integral_add hfz' hgz'
  have hstep4a : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hfz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  have hstep4b : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hgz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  exact le_trans hstep1.le
    (le_trans hstep2 (le_trans hstep3.le (add_le_add hstep4a hstep4b)))

/-! ## 4. Measurability -/

/-- Continuity on the open quadrant gives a.e. strong measurability for the product of the two
restricted measures. -/
theorem aesm_prod_of_continuousOn_Q0 {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable g ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [Measure.prod_restrict]
  exact hmain

/-- The absolute value of an a.e. strongly measurable real function is a.e. strongly
measurable (`|f| = max f (-f)`). -/
theorem aesm_abs {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => |f x|) μ := by
  have h2 : AEStronglyMeasurable (fun x => max (f x) (-1 * f x)) μ :=
    hf.sup (hf.const_mul (-1))
  refine h2.congr (Filter.Eventually.of_forall (fun x => ?_))
  show max (f x) (-1 * f x) = |f x|
  rw [abs_eq_max_neg]
  congr 1
  ring

/-- The radial marginal of a jointly measurable function is a.e. strongly measurable. -/
theorem aesm_marginal {G : ℝ → ℝ → ℝ}
    (hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))) :
    AEStronglyMeasurable (fun z => ∫ θ, G z θ
      ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
  hjoint.integral_prod_right'

/-- The weight `cut n · · wt ·` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_cut_mul_wt (n : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z) (volume.restrict (Set.Ioi (0 : ℝ))) :=
  ((((Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn).mul
      Work.FTS.EllipticEst.AeColl.continuousOn_wt).aestronglyMeasurable measurableSet_Ioi)

/-- The squared radial weight `wt ·` is measurable. -/
theorem measurable_wt : Measurable Work.FTS.EllipticEst.AeColl.wt := by
  have h' : Work.FTS.EllipticEst.AeColl.wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.FTS.EllipticEst.AeColl.wt, Work.Spaces.w]
  rw [h']
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- The transfer coefficient `deriv (χ_n w² z²)/z` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_trtr_coef (n : ℕ) :
    AEStronglyMeasurable
      (fun z => deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcut : Measurable (deriv (Work.FTS.EllipticEst.cut n)) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by norm_num)).measurable
  have hcwf : Measurable Work.FTS.EllipticEst.AeColl.cwf := by
    have h2 : Work.FTS.EllipticEst.AeColl.cwf = fun z : ℝ => 2 * (z - 1) / (1 + z) := by
      funext z; rfl
    rw [h2]
    exact ((measurable_const.mul (measurable_id.sub measurable_const))).div
      (measurable_const.add measurable_id)
  have hcfun : Measurable (Work.FTS.EllipticEst.AeColl.cfun n) := by
    have h : Work.FTS.EllipticEst.AeColl.cfun n
        = fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z * z
            + Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.cwf z := by
      funext z; rfl
    rw [h]
    exact (hcut.mul measurable_id).add
      (((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable).mul hcwf)
  refine ((hcfun.mul measurable_wt).aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (Work.FTS.EllipticEst.AeColl.deriv_cut_wt_zsq hz).symm

/-! ## 5. The uniform bound for the transfer coefficient -/

/-- The transfer coefficient is dominated by the radial weight: there is `C > 0` with
`|deriv (χ_n w² z²) z / z| ≤ C · wt z` for every `z > 0`. -/
theorem trtr_coef_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AeColl.wt z'
        * z' ^ 2) z / z| ≤ C * Work.FTS.EllipticEst.AeColl.wt z := by
  obtain ⟨K, hKpos, hKbd, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  refine ⟨K + 2, by linarith, fun z hz => ?_⟩
  rw [Work.FTS.EllipticEst.AeColl.deriv_cut_wt_zsq hz, abs_mul,
    abs_of_nonneg (wt_nonneg z)]
  exact mul_le_mul_of_nonneg_right
    (Work.FTS.EllipticEst.AeColl.abs_cfun_le (hKbd n) (le_of_lt hz)) (wt_nonneg z)


end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.slot_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The slot algebra for `∂_θ(Uop α (EllResid α F Ψ))` in the class `EllHypQ`

Target: for `k ≥ 2`, `0 < α ≤ 1/4`, `EllHypQ α k F Ψ` and `OrthCond`, and every
`(z,θ) ∈ Iz × Iθ`,

`HkIntegrand α k (∂_θ(Uop α W)) z θ ≤ 18·HkIntegrand α k (∂_θW) z θ
   + 2·HkIntegrand α k (α·D_z∂_θW) z θ`,  `W := EllResid α F Ψ = Ψ - (1/(4α))sin 2θ·L₁₂(F)`.

## The mathematics

`Uop α W = -3W - α·D_zW` has coefficients *constant in* `θ`, so on the open quadrant

  `∂_θ(Uop α W) = -3·∂_θW - α·D_z(∂_θW)`,

and the whole content of the statement is the slotwise AM–GM estimate
`(slot of E)² ≤ 18(slot of f)² + 2α²(slot of g)²` for `E := -3f - αg`, `f := ∂_θW`,
`g := D_z∂_θW`.  This is exactly the statement of `RegQ.HkIntegrand_slot_le`
(proved in `RegQ/pthU_slot_alg.lean`), which needs three inputs:

* the pointwise identity above, i.e. `W ∈ C²` on the open quadrant
  (`RegQ.pth_Uop_eq`);
* `f = ∂_θW ∈ C^k` and `g = D_z∂_θW ∈ C^{k-1}` on the open quadrant.

The point of this file is that **these regularity inputs are available in `EllHypQ`**, contrary
to the naive expectation that `W ∈ C^{k+1}` is needed (it is not, and it is false, cf.
`RegQ/NOTES_pthU_EllResid_certs_FALSE.md`).  The reason is the *radial* structure of the
singular part: `W = Ψ - Λ(z)·sin 2θ` with `Λ = (1/(4α))L₁₂(F)`, so

* `∂_θW = ∂_θΨ - 2cos 2θ·Λ(z)` needs only `Λ ∈ C^k`, which follows from
  `L₁₂(F) ∈ C^k` — available from `SmoothOpen F` + `HkMem α k F` via
  `UopHk.contDiffOn_Fstar_of_smoothOpen_Hk` (`F_* ∈ C^{k-1}`) and the fundamental theorem of
  calculus for the tail integral (`UopHk.contDiffOn_L12_of_smoothOpen_Hk`);
* `D_z∂_θW = z(∂_z∂_θΨ - 2cos 2θ·Λ'(z))` needs only `Λ' ∈ C^{k-1}`, i.e. `Λ ∈ C^k` again;
* `W ∈ C^2` needs only `Λ ∈ C²`, which holds since `k ≥ 2`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

variable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 0. Finite-order smoothness of the partials of a `SmoothQuad` function -/



/-! ## 1. The radial regularity of `L₁₂(F)` -/



/-! ## 2. The pointwise `z`-derivative of `∂_θ(EllResid α F Ψ)` -/


/-! ## 3. The three regularity certificates for the slot algebra -/




/-! ## 4. The target -/


end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.QuadZLeibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

open Work.FTS.H2.Transport3Aux.Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Closure of `SmoothQuad` under the two transport operators -/

/-- `D_z` preserves `SmoothQuad`. -/
theorem smoothQuad_Dz {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
  Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
    (Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hg)

/-! ## Commutation of `D_z` with the `D_θ`-iterates on the open quadrant -/



/-! ## The two Leibniz expansions -/



/-! ## The expansion of the pairing and the removal of `Badz` -/


end Work.FTS.H2.T3Q
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## The angular profile as a function of `(z,θ)` -/






/-! ## Two elementary weighted bounds for the angular factor -/




/-! ## The mixed-derivative pointwise bound -/


/-! ## The radial pointwise bound -/


/-! ## The field lemma -/


end Work.FTS.Nonlinear.N4Fields
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.wmul_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

theorem wmul_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g → Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g → (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) → Work.Spaces.WlInfMem α 4 (fun z θ => f z θ * g z θ) ∧ Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ) ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := Work.FTS.H2.prodW_interior_bound
  refine ⟨50 * C₀, by positivity, ?_⟩
  intro α hα f g hfS hgS hfm hgm hbdy
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  -- the pointwise estimate on the open quadrant
  obtain ⟨hrad, hang⟩ := hC₀b α f g hα.1 hα1 hfS hgS hfm hgm
  set Wf := Work.Spaces.WlInf α 4 f with hWf
  set Wg := Work.Spaces.WlInf α 4 g with hWg
  have hWfnn : 0 ≤ Wf := by rw [hWf]; exact Work.Spaces.WlInf_nonneg α 4 f hfm
  have hWgnn : 0 ≤ Wg := by rw [hWg]; exact Work.Spaces.WlInf_nonneg α 4 g hgm
  have hB : 0 ≤ C₀ * Wf * Wg := mul_nonneg (mul_nonneg hC₀pos.le hWfnn) hWgnn
  -- the slice of `g` at `θ = 0` (resp. `π/2`) is the zero function, hence so is the slice of `f g`
  have hslice : ∀ (θ₀ : ℝ), (∀ z : ℝ, g z θ₀ = 0) → ∀ k : ℕ, ∀ z : ℝ,
      Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ₀ = 0 := by
    intro θ₀ hg k z
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    have hs : (fun z' => (fun z θ => f z θ * g z θ) z' θ₀) = fun _ => (0 : ℝ) := by
      funext z'; simp [hg z']
    rw [hs, iteratedDeriv_const]
    simp
  have hg0 : ∀ z : ℝ, g z 0 = 0 := fun z => (hbdy 0 (by norm_num) z).1
  have hgpi : ∀ z : ℝ, g z (π / 2) = 0 := fun z => (hbdy 0 (by norm_num) z).2
  -- the pointwise bound for the radial terms of the product, on the *closed* domain
  have hPZ : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ| ≤ C₀ * Wf * Wg := by
    intro k hk z hz θ hθ
    rcases eq_or_ne θ 0 with h0 | h0
    · subst h0
      rw [hslice 0 hg0 k z, mul_zero, abs_zero]
      exact hB
    · rcases eq_or_ne θ (π / 2) with hpi | hpi
      · subst hpi
        rw [hslice (π / 2) hgpi k z, mul_zero, abs_zero]
        exact hB
      · exact hrad k hk z hz θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0),
          lt_of_le_of_ne hθ.2 hpi⟩
  -- the pointwise bound for the mixed terms; the angular weight is zero at the boundary
  have hPT : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C₀ * Wf * Wg := by
    intro j k hj hkj z hz θ hθ
    have hα5 : α / 5 ≠ 0 := ne_of_gt (by linarith [hα.1] : (0 : ℝ) < α / 5)
    rcases eq_or_ne θ 0 with h0 | h0
    · subst h0
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero],
        Real.zero_rpow (neg_ne_zero.mpr hα5), mul_div_assoc]
      simp
      exact hB
    · rcases eq_or_ne θ (π / 2) with hpi | hpi
      · subst hpi
        rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi],
          Real.zero_rpow (neg_ne_zero.mpr hα5), mul_div_assoc]
        simp
        exact hB
      · exact hang j k hj hkj z hz θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0),
          lt_of_le_of_ne hθ.2 hpi⟩
  -- the supremum and the counting of the `15` summands of the norm
  have hcount := wlInf_of_pointwise_bounds (α := α) (B := C₀ * Wf * Wg) hB hPZ hPT
  refine ⟨hcount.1, ?_⟩
  calc Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ)
      ≤ 30 * (C₀ * Wf * Wg) := hcount.2
    _ ≤ 50 * C₀ * Wf * Wg := by nlinarith [hB]

end Work.FTS.Nonlinear.N4Fields
end
-- ===== merged: Submission.Work.H2.T1Q.HardBoundQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
lemma ae_Iθ_mem_Ioo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc,
    MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ
    have h1 : θ ∈ Work.Spaces.Iθ := by
      by_contra hcon
      exact hθ (fun h => absurd h hcon)
    have h2 : θ ∉ Set.Ioo 0 (π / 2) := fun hioo => hθ (fun _ => hioo)
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at h1
    rw [Set.mem_Ioo, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · exact Or.inl (le_antisymm h2 h1.1)
    · exact Or.inr (le_antisymm h1.2 (not_lt.mp h2))
  · simpa using (Set.Finite.measure_zero (by simp : ({0, π / 2} : Set ℝ).Finite)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ))

/-- A function which is eventually equal to the constant `1` has vanishing derivative. -/
lemma deriv_eq_zero_of_eventuallyEq_one {χ : ℝ → ℝ} {θ : ℝ}
    (h : χ =ᶠ[𝓝 θ] (fun _ => (1 : ℝ))) : deriv χ θ = 0 := by
  have hd : deriv χ θ = deriv (fun _ : ℝ => (1 : ℝ)) θ := h.deriv_eq
  simpa using hd

/-- The weighted pointwise bound on the `W`-factor of the angular integration by parts:
for `|a| ≤ Kf`, `|b| ≤ Kf` and `|1-q| ≤ 1`,
`|a/2 + (1-q)·cos(2θ)·b| ≤ (3/2)Kf`. -/
lemma Wq_bound {Kf q a b θ : ℝ} (hKf0 : 0 ≤ Kf) (h1 : |a| ≤ Kf) (h2 : |b| ≤ Kf)
    (hq : |1 - q| ≤ 1) :
    |(1 / 2) * a + (1 - q) * Real.cos (2 * θ) * b| ≤ (3 / 2) * Kf := by
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |(1 / 2) * a| ≤ Kf / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have h4 : |(1 - q) * Real.cos (2 * θ) * b| ≤ Kf := by
    rw [abs_mul, abs_mul]
    calc |1 - q| * |Real.cos (2 * θ)| * |b| ≤ 1 * 1 * Kf :=
          mul_le_mul (mul_le_mul hq hc (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _)
            (by norm_num)
      _ = Kf := by ring
  calc |(1 / 2) * a + (1 - q) * Real.cos (2 * θ) * b|
      ≤ |(1 / 2) * a| + |(1 - q) * Real.cos (2 * θ) * b| := abs_add_le _ _
    _ ≤ Kf / 2 + Kf := add_le_add h3 h4
    _ = (3 / 2) * Kf := by ring




/-- **The per-slot bound of the cut-off method.**  From the angular integration by parts with a
cut-off factor `χ`,

`∫_θ sin(2θ)^{-q}·(χ·F)·D_θ(V)·V = -∫_θ sin(2θ)^{-q}·(χ·W + (1/2)·D_θ(χ)·F)·V²`,

the pointwise bounds `|F| ≤ Kf`, `|W| ≤ (3/2)Kf` and `|sin(2θ)·χ'| ≤ B`, and the support
`χ' = 0` off `(0,ζ) ∪ (π/2-ζ, π/2)` one gets

`|∫_θ χ·F·D_θ(V)·V·sin(2θ)^{-q}| ≤ (3/2)Kf·∫_θ V²sin(2θ)^{-q}
   + (Kf·B/2)·(∫_{(0,ζ)} V²sin(2θ)^{-q} + ∫_{(π/2-ζ,π/2)} V²sin(2θ)^{-q})`. -/
lemma slotBound_cutoff {q Kf B ζ : ℝ} {χ F V : ℝ → ℝ}
    (hKf0 : 0 ≤ Kf) (hB0 : 0 ≤ B) (hζ : 0 < ζ) (hζ2 : 2 * ζ ≤ π / 2)
    (hχnn : ∀ θ : ℝ, 0 ≤ χ θ) (hχle : ∀ θ : ℝ, χ θ ≤ 1)
    (hsd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv χ θ|
      ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ))
    (hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf)
    (hWb : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv F θ) + (1 - q) * Real.cos (2 * θ) * F θ|
        ≤ (3 / 2) * Kf)
    (hVint : MeasureTheory.IntegrableOn
      (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ)
    (hAint : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * F θ) * (Real.sin (2 * θ) * deriv V θ) * V θ) Work.Spaces.Iθ)
    (hIBP : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * F θ)
          * (Real.sin (2 * θ) * deriv V θ) * V θ
        = -∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ)
              + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2) :
    |∫ θ in Work.Spaces.Iθ, χ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ
        * (Real.sin (2 * θ)) ^ (-q))|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- rewrite the left-hand side as the left-hand side of the integration by parts
  have hAeq : (∫ θ in Work.Spaces.Iθ, χ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ
        * (Real.sin (2 * θ)) ^ (-q)))
      = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * F θ)
          * (Real.sin (2 * θ) * deriv V θ) * V θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  rw [hAeq, hIBP, abs_neg]
  -- the pointwise comparison with the majorant
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |(Real.sin (2 * θ)) ^ (-q) * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
            + (1 - q) * Real.cos (2 * θ) * F θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
        ≤ (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ) := by
    filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsq : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hs _
    have hV2 : 0 ≤ (V θ) ^ 2 := sq_nonneg _
    have hW := hWb θ hθ
    have hF := hFb θ hθ
    have hinner : |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
          + (1 - q) * Real.cos (2 * θ) * F θ) + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ|
        ≤ (3 / 2) * Kf + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ| := by
      calc |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ|
          ≤ |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ)|
            + |(1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| := abs_add_le _ _
        _ = χ θ * |(1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ|
            + (1 / 2) * |Real.sin (2 * θ) * deriv χ θ| * |F θ| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hχnn θ),
                abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ 1 * ((3 / 2) * Kf) + (1 / 2) * |Real.sin (2 * θ) * deriv χ θ| * Kf := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul (hχle θ) hW (abs_nonneg _) (by linarith)
              · have h2 : 0 ≤ (1 / 2 : ℝ) * |Real.sin (2 * θ) * deriv χ θ| := by positivity
                exact mul_le_mul_of_nonneg_left hF h2
        _ = (3 / 2) * Kf + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ| := by ring
    have hIA : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = (Set.Ioc 0 (2 * ζ)).indicator (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ := by
      by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hIB : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ := by
      by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hnorm : |(Real.sin (2 * θ)) ^ (-q) * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
        = (Real.sin (2 * θ)) ^ (-q)
          * |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| * (V θ) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_nonneg hV2]
    rw [hnorm]
    have hv : 0 ≤ (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := mul_nonneg hV2 hsq
    calc (Real.sin (2 * θ)) ^ (-q) * |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| * (V θ) ^ 2
        ≤ (Real.sin (2 * θ)) ^ (-q) * ((3 / 2) * Kf
            + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ|) * (V θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hsq) hV2
      _ = (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ|
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by ring
      _ ≤ (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf / 2) * (B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ))
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          refine add_le_add le_rfl ?_
          have hv' : 0 ≤ (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := hv
          have hK : 0 ≤ Kf / 2 := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsd θ hθ) hK) hv'
      _ = (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                  (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                  (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ) := by
          rw [← hIA, ← hIB]; ring
  -- the majorant is integrable
  have hmaj : MeasureTheory.Integrable (fun θ => (3 / 2) * Kf
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.add (hVint.const_mul _) (MeasureTheory.Integrable.const_mul ?_ _)
    exact (MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc).add
      (MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ _ => abs_nonneg _)) hmaj hpt
  -- evaluate the integral of the majorant
  have hval : (∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)))
      = (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    have h1 : MeasureTheory.Integrable (fun θ => (Set.Ioc 0 (2 * ζ)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc
    have h2 : MeasureTheory.Integrable (fun θ => (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc
    have hs1 : (∫ θ in Work.Spaces.Iθ, (Set.Ioc 0 (2 * ζ)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        = ∫ θ in Set.Ioc 0 (2 * ζ), (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      congr 1
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left]
      intro θ hθ
      exact ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2⟩
    have hs2 : (∫ θ in Work.Spaces.Iθ, (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        = ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      congr 1
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left]
      intro θ hθ
      exact ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩
    have e1 : (∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf
            * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)))
        = (∫ θ in Work.Spaces.Iθ, (3 / 2) * Kf
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)) :=
      MeasureTheory.integral_add (hVint.const_mul _) ((h1.add h2).const_mul _)
    rw [e1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add h1 h2, hs1, hs2]
  calc |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
            + (1 - q) * Real.cos (2 * θ) * F θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
      ≤ ∫ θ in Work.Spaces.Iθ, |(Real.sin (2 * θ)) ^ (-q)
          * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)) := hmono
    _ = (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := hval




end Work.H2.T1Q
end
-- ===== merged: Submission.Work.H2.T1Q.T1EasyContQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2










end Work.H2.T1Q
end
end
