import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.HkSqZfar
-- ===== merged: Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Product integrability of the `Tk`-slot data of the `A`-slot

The cross-slot identity `TkA_le_cross` is ultimately an identity between integrals over the
half-open strip `(0,∞) × Iθ`, and both Fubini interchanges used in its proof need the slots
involved to be honestly integrable for the product measure
`(volume|_{(0,∞)}).prod (volume|_{Iθ})`.

For a function `F` which is `C^∞` on the open quadrant (`SmoothOpen F`) and honestly in
`ℋ^k` (`HkMem α k F`), this module proves:

* the whole `ℋ^k`-integrand `HkIntegrand α k F` is integrable for the product of the
  restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`
  (`integrable_uncurry_HkIntegrand`) — Tonelli applied to the two halves of the definition of
  `HkMem` (`Work.Spaces.integrable_prod_of_iterated`), the a.e. strong measurability coming
  from the joint continuity of `HkIntegrand` on the open quadrant;
* every single weighted `D_z`-slot `(D_z^i F · w/ sin(2θ)^{η/2})²` with `i ≤ k`
  (`integrable_uncurry_slot_z`) and every mixed slot `(D_z^j D_θ^i F · W)²` with `1 ≤ i`,
  `i + j ≤ k` (`integrable_uncurry_slot_mixed`) is integrable for that product measure, by
  domination against the `ℋ^k`-integrand;
* hence, by monotonicity of the measure (`Integrable.mono_measure`), the same holds for the
  measure `(volume|_{(0,∞)}).prod (volume|_{Iθ})` which the statement uses
  (`integrable_of_Iz_prod`).

The requested theorem `TkA_slotIntegrable` is then the three instances
`F = Az Ψ = z²∂_z²Ψ` (with the `D_z`-slots for `i = 0,1` and the mixed slot `mixed 0 1`)
and `F = Bz Ψ = ∂_θ²Ψ` (with the `D_z`-slots for `i = 0,1`), the hypotheses `hmemA`, `hmemB`
being exactly the `ℋ¹`-memberships.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Continuity of the product weight on the open quadrant -/

/-- The product weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-! ## The `ℋ^k`-integrand is integrable on the closed quadrant -/

/-- **Tonelli for the `ℋ^k`-integrand.**  If `F` is `C^∞` on the open quadrant and
`HkMem α k F`, then the uncurried `HkIntegrand α k F` is integrable for the product of the
restrictions of Lebesgue measure to `Iz` and `Iθ`.  This is the two halves of `HkMem`
(fibrewise integrability and integrability of the fibre integrals) read through
`Work.Spaces.integrable_prod_of_iterated`; the a.e. strong measurability of the joint
integrand is the continuity of `HkIntegrand` on the open quadrant. -/
theorem integrable_uncurry_HkIntegrand {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α k F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α k F z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α k))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
      exact hmem.1 z hz)
    hmem.2).1

/-! ## The single `D_z`-slot is integrable on the closed quadrant -/

/-- **Product integrability of a weighted `D_z`-slot.**  For `F` smooth on the open quadrant
and in `ℋ^k`, and every `i ≤ k`, the square `(D_z^i F · w/sin(2θ)^{η/2})²` is integrable for
the product measure on `Iz × Iθ`: it is pointwise dominated by `HkIntegrand α k F`. -/
theorem integrable_uncurry_slot_z {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_uncurry_HkIntegrand hF hmem)
    ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2) ?_
  filter_upwards with p
  obtain ⟨z, θ⟩ := p
  change ‖(Work.Spaces.DzIter i F z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α k F z θ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi

/-! ## A single mixed slot is integrable on the closed quadrant -/

/-- **Product integrability of a mixed slot.**  For `F` smooth on the open quadrant and in
`ℋ^k`, and every `1 ≤ i`, `i + j ≤ k`, the square `(D_z^j D_θ^i F · W)²` is integrable for
the product measure on `Iz × Iθ`. -/
theorem integrable_uncurry_slot_mixed {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_uncurry_HkIntegrand hF hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · filter_upwards with p
    obtain ⟨z, θ⟩ := p
    change ‖(Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α k F z θ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij

/-! ## Passing to the half-open half-line `(0,∞)` -/


/-! ## Smoothness of the two data of the `A`-slot -/



/-! ## The requested statement -/


end Work.FTS.EllipticEst.AeSlotOneAe.Interp
end
end
-- ===== merged: Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.LocData

/-! ## The second derivative recursion for the coefficient polynomials `Qp` -/

/-- The second derivative recursion for the coefficient polynomials, obtained by
differentiating `(Q_{j+1})' = 4v·Q_j' - 2(1-v²)·Q_j'' + α·Q_j + α(v-1/3)·Q_j'`. -/
theorem Qp_deriv_deriv_succ_eval (j : ℕ) (α v : ℝ) :
    (Qp (j + 1) α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp j α).derivative.eval v
        + 8 * v * (Qp j α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp j α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp j α).derivative.derivative.eval v := by
  simp [Qp]; ring


/-- The third derivative of `Qp 2 α`, explicitly. -/
theorem Qp2_deriv3_eval (α v : ℝ) :
    (Qp 2 α).derivative.derivative.derivative.eval v = (4 + 2 * α) * (12 + 3 * α) := by
  simp [Qp]; ring

/-- **Bound on `(Qp 2 α)'''`** on `|v| ≤ 1`, `α ∈ [0,1]`. -/
theorem Qp2_deriv3_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 := by
  rw [Qp2_deriv3_eval, abs_mul]
  have h1 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have h2 : |12 + 3 * α| ≤ 15 := by rw [abs_le]; constructor <;> linarith
  calc |4 + 2 * α| * |12 + 3 * α| ≤ 6 * 15 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 90 := by norm_num

/-- The second derivative recursion at `j = 2`, i.e. for `Qp 3`. -/
theorem Qp3_deriv2_eval (α v : ℝ) :
    (Qp 3 α).derivative.derivative.eval v
      = (4 + 2 * α) * (Qp 2 α).derivative.eval v
        + 8 * v * (Qp 2 α).derivative.derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v
        + α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v :=
  Qp_deriv_deriv_succ_eval 2 α v

/-- **Bound on `(Qp 3 α)''`.**  With `|(Qp 2)'| ≤ 154/3`, `|(Qp 2)''| ≤ 96` and
`|(Qp 2)'''| ≤ 90`, the recursion gives `|(Qp 3)''| ≤ 6·(154/3) + 8·96 + 2·90 + (4/3)·96 = 1384`. -/
theorem Qp3_deriv2_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 := by
  rw [Qp3_deriv2_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have h4 : |4 + 2 * α| ≤ 6 := abs_four_add_two_mul_le hα0 hα1
  have hS2 : |(Qp 2 α).derivative.eval v| ≤ 154 / 3 := Qp2_deriv_bound hα0 hα1 hv
  have hU2 : |(Qp 2 α).derivative.derivative.eval v| ≤ 96 :=
    Work.FTS.LocDataExt.Qp2_deriv2_bound hα0 hα1 hv
  have hT2 : |(Qp 2 α).derivative.derivative.derivative.eval v| ≤ 90 :=
    Qp2_deriv3_bound hα0 hα1
  have hA : |(4 + 2 * α) * (Qp 2 α).derivative.eval v| ≤ 6 * (154 / 3) :=
    abs_mul_le_of (A := 6) (B := 154 / 3) h4 hS2 (by norm_num)
  have hB : |8 * v * (Qp 2 α).derivative.derivative.eval v| ≤ 8 * 1 * 96 := by
    rw [show 8 * v * (Qp 2 α).derivative.derivative.eval v
        = (8 * v) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 8 * 1) (B := 96)
      (by rw [abs_mul]; norm_num; exact hv) hU2 (by norm_num)
  have hC : |(-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v|
      ≤ 2 * 1 * 90 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 2 α).derivative.derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 90)
      (by rw [abs_mul]; norm_num; exact h1) hT2 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v| ≤ 1 * (4 / 3) * 96 := by
    rw [show α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 2 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 96)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hU2 (by norm_num)
  have hsp1 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v
      + 8 * v * (Qp 2 α).derivative.derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v)
      (α * (v - 1 / 3) * (Qp 2 α).derivative.derivative.eval v)
  have hsp2 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v
      + 8 * v * (Qp 2 α).derivative.derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 2 α).derivative.derivative.derivative.eval v)
  have hsp3 := abs_add_le ((4 + 2 * α) * (Qp 2 α).derivative.eval v)
      (8 * v * (Qp 2 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-! ## `Qp 4` -/

/-- The derivative recursion at `j = 3`, i.e. for `Qp 4`. -/
theorem Qp4_deriv_eval (α v : ℝ) :
    (Qp 4 α).derivative.eval v
      = 4 * v * (Qp 3 α).derivative.eval v
        + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
        + α * (Qp 3 α).eval v
        + α * (v - 1 / 3) * (Qp 3 α).derivative.eval v :=
  Work.FTS.LocDataExt.Qp_deriv_succ_eval 3 α v

/-- **Bound on `(Qp 4 α)'`.**  From `|(Qp 3)| ≤ 10300/81`, `|(Qp 3)'| ≤ 13072/27` and
`|(Qp 3)''| ≤ 1384`: `4·(13072/27) + 2·1384 + 10300/81 + (4/3)·(13072/27) = 443660/81`. -/
theorem Qp4_deriv_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 := by
  rw [Qp4_deriv_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS3 : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hU3 : |(Qp 3 α).derivative.derivative.eval v| ≤ 1384 := Qp3_deriv2_bound hα0 hα1 hv
  have hQ3 : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |4 * v * (Qp 3 α).derivative.eval v| ≤ 4 * 1 * (13072 / 27) := by
    rw [show 4 * v * (Qp 3 α).derivative.eval v
        = (4 * v) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 4 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact hv) hS3 (by norm_num)
  have hB : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v| ≤ 2 * 1 * 1384 := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 1384)
      (by rw [abs_mul]; norm_num; exact h1) hU3 (by norm_num)
  have hC : |α * (Qp 3 α).eval v| ≤ 1 * (10300 / 81) :=
    abs_mul_le_of (A := 1) (B := 10300 / 81) (by rwa [abs_of_nonneg hα0]) hQ3 (by norm_num)
  have hD : |α * (v - 1 / 3) * (Qp 3 α).derivative.eval v| ≤ 1 * (4 / 3) * (13072 / 27) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).derivative.eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 13072 / 27)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hS3 (by norm_num)
  have hsp1 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v
      + α * (Qp 3 α).eval v) (α * (v - 1 / 3) * (Qp 3 α).derivative.eval v)
  have hsp2 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v
      + (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v) (α * (Qp 3 α).eval v)
  have hsp3 := abs_add_le (4 * v * (Qp 3 α).derivative.eval v)
      ((-2) * (1 - v ^ 2) * (Qp 3 α).derivative.derivative.eval v)
  linarith [hsp1, hsp2, hsp3, hA, hB, hC, hD]

/-- **The sharp bound on `Qp 4 α`** (the `LocDataExt.Qp4_eval_bound` constant, made explicit). -/
theorem Qp4_eval_bound_sharp {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 4 α).eval v| ≤ 276496 / 243 := by
  rw [Work.FTS.LocDataExt.Qp4_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hS3 : |(Qp 3 α).derivative.eval v| ≤ 13072 / 27 :=
    Work.FTS.LocDataExt.Qp3_deriv_bound hα0 hα1 hv
  have hQ3 : |(Qp 3 α).eval v| ≤ 10300 / 81 := Qp3_eval_bound hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v| ≤ 2 * 1 * (13072 / 27) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 3 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 13072 / 27)
      (by rw [abs_mul]; norm_num; exact h1) hS3 (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 3 α).eval v| ≤ 1 * (4 / 3) * (10300 / 81) := by
    rw [show α * (v - 1 / 3) * (Qp 3 α).eval v
        = (α * (v - 1 / 3)) * (Qp 3 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 10300 / 81)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ3 (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 3 α).derivative.eval v + α * (v - 1 / 3) * (Qp 3 α).eval v|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (13072 / 27) + 1 * (4 / 3) * (10300 / 81) := add_le_add hA hB
    _ = 276496 / 243 := by norm_num

/-! ## `Qp 5` -/

/-- The recursion at `j = 4`, i.e. for `Qp 5`. -/
theorem Qp5_eval (α v : ℝ) :
    (Qp 5 α).eval v
      = (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).eval v :=
  Qp_succ_eval 4 α v

/-- **Bound on `Qp 5 α` on `[-1,1]`.**  `|Qp 5| ≤ 2·(443660/81) + (4/3)·(276496/243)
= 9091864/729 < 10⁵`. -/
theorem Qp5_eval_bound {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hv : |v| ≤ 1) :
    |(Qp 5 α).eval v| ≤ 100000 := by
  rw [Qp5_eval]
  have h1 : |1 - v ^ 2| ≤ 1 := abs_one_sub_sq_le_one hv
  have h2 : |v - 1 / 3| ≤ 4 / 3 := abs_sub_third_le hv
  have hD4 : |(Qp 4 α).derivative.eval v| ≤ 443660 / 81 := Qp4_deriv_bound hα0 hα1 hv
  have hQ4 : |(Qp 4 α).eval v| ≤ 276496 / 243 := Qp4_eval_bound_sharp hα0 hα1 hv
  have hA : |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v| ≤ 2 * 1 * (443660 / 81) := by
    rw [show (-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        = ((-2) * (1 - v ^ 2)) * (Qp 4 α).derivative.eval v by ring]
    exact abs_mul_le_of (A := 2 * 1) (B := 443660 / 81)
      (by rw [abs_mul]; norm_num; exact h1) hD4 (by norm_num)
  have hB : |α * (v - 1 / 3) * (Qp 4 α).eval v| ≤ 1 * (4 / 3) * (276496 / 243) := by
    rw [show α * (v - 1 / 3) * (Qp 4 α).eval v
        = (α * (v - 1 / 3)) * (Qp 4 α).eval v by ring]
    exact abs_mul_le_of (A := 1 * (4 / 3)) (B := 276496 / 243)
      (abs_mul_le_of (A := 1) (B := 4 / 3) (by rwa [abs_of_nonneg hα0]) h2 (by norm_num))
      hQ4 (by norm_num)
  calc |(-2) * (1 - v ^ 2) * (Qp 4 α).derivative.eval v
        + α * (v - 1 / 3) * (Qp 4 α).eval v|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ 2 * 1 * (443660 / 81) + 1 * (4 / 3) * (276496 / 243) := add_le_add hA hB
    _ = 9091864 / 729 := by norm_num
    _ ≤ 100000 := by norm_num

/-! ## The coefficient bound for `j ≤ 5`, and the main statement -/

/-- **The coefficient bound `|Tfun j α θ| ≤ 100000` for `j ≤ 5`**, extending
`Work.FTS.LocDataExt.Tfun_abs_le4` by one order. -/
theorem Tfun_abs_le5 (j : ℕ) (hj : j ≤ 5) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    |Work.Spaces.Tfun j α θ| ≤ 100000 := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact Work.FTS.LocDataExt.Tfun_abs_le4 j (by omega) α hα hα1 θ
  · subst heq
    have hq : |(Qp 5 α).eval (Real.cos (2 * θ))| ≤ 100000 :=
      Qp5_eval_bound (le_of_lt hα) hα1
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    rw [Tfun_eq_Qp 5 α]
    simpa using hq

/-- The angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` on `Iθ`, extended by one order (to `i ≤ 6`).
The proved `i ≤ 5` version `Work.FTS.LocDataExt.DthIter_Gam_abs_le5` reduces the statement to
a bound `|Tfun (i-1) α θ| ≤ 100000`, so it suffices to bound `Qp 5 α` on `|v| ≤ 1`,
`α ∈ [0,1]` through the recursion `Qp (j+1) = -2(1-X²)·Qp j' + α·(X-1/3)·Qp j` and its first two
derivatives, and then to re-run the final assembly of that file
(`Work.Spaces.dthU_iter_Gam_abs_bound`). -/
theorem DthIter_Gam_abs_le6 (i : ℕ) (hi : i ≤ 6) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 100000 * Work.Spaces.Gam α θ := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG0]
    linarith
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Tfun_abs_le5 (i - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i h α hα 100000 hT θ hθ
    rw [DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
    calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG0]

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.FM_Fstar_jet_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The fifth `D_z`-iterate of the profile in closed form -/

/-- The pointwise form of the fifth `D_z`-iterate of `FM.Fstar` off the pole `z = -1`,
obtained from the delivered `PhiZ_eq` (at order `4`) and `Phi_div_deriv_four`. -/
theorem DzIter_FM_Fstar_five_eq {w : ℝ} (hw : w ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ
      = 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5) / (1 + w) ^ 7 := by
  have hstep : Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ
      = w * deriv (fun u : ℝ => Work.FTS.LocData.PhiR 4 u / (1 + u) ^ 6) w := by
    show Work.Spaces.Dz (Work.Spaces.DzIter 4 (fun z _ => Work.FM.Fstar z)) w θ = _
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with u
    rw [Work.FTS.LocData.PhiZ_eq 4 (by norm_num) u θ]
    rfl
  rw [hstep, Work.FTS.LocDataExt.Phi_div_deriv_four hw]

/-! ## The derivative of the closed form -/

/-- The derivative of the rational function of `DzIter_FM_Fstar_five_eq`. -/
theorem FMFstar_six_deriv {z : ℝ} (hz1 : z ≠ -1) :
    deriv (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
        / (1 + w) ^ 7) z
      = 2 * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
          / (1 + z) ^ 8 := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz1 (by linarith)
  have hp7 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 h1
  have hp72 : ((1 + z) ^ 7) ^ 2 ≠ 0 := pow_ne_zero 2 hp7
  have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
  have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
  have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
  have hsub5 : (5 : ℕ) - 1 = 4 := by norm_num
  have hsub7 : (7 : ℕ) - 1 = 6 := by norm_num
  have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
      refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
      simp [hsub2]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hcu : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 3) (3 * z ^ 2) z := by
      refine (((hasDerivAt_id' (x := z)).pow 3).congr_deriv ?_)
      simp [hsub3]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hqu : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 4) (4 * z ^ 3) z := by
      refine (((hasDerivAt_id' (x := z)).pow 4).congr_deriv ?_)
      simp [hsub4]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hfif : HasDerivAt (fun w : ℝ => w ^ 5) (5 * z ^ 4) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 5) (5 * z ^ 4) z := by
      refine (((hasDerivAt_id' (x := z)).pow 5).congr_deriv ?_)
      simp [hsub5]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hQ : HasDerivAt (fun w : ℝ => 1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
      (-57 + 604 * z - 906 * z ^ 2 + 228 * z ^ 3 - 5 * z ^ 4) z := by
    have h57 : HasDerivAt (fun w : ℝ => 57 * w) 57 z :=
      hasDerivAt_const_mul (c := (57 : ℝ)) (x := z)
    have h302a : HasDerivAt (fun w : ℝ => 302 * w ^ 2) (302 * (2 * z)) z := hsq.const_mul (302 : ℝ)
    have h302b : HasDerivAt (fun w : ℝ => 302 * w ^ 3) (302 * (3 * z ^ 2)) z := hcu.const_mul (302 : ℝ)
    have h57b : HasDerivAt (fun w : ℝ => 57 * w ^ 4) (57 * (4 * z ^ 3)) z := hqu.const_mul (57 : ℝ)
    have hlin : HasDerivAt (fun w : ℝ => 1 - 57 * w) (0 - 57) z :=
      (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h57
    exact ((((hlin.add h302a).sub h302b).add h57b).sub hfif).congr_deriv (by ring)
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 7) (7 * (1 + z) ^ 6) z := by
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 7) (7 * (1 + z) ^ 6) z := by
      refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 7).congr_deriv ?_)
      simp [hsub7]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hnum : HasDerivAt (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)) (2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5) + 2 * z * (-57 + 604 * z - 906 * z ^ 2 + 228 * z ^ 3 - 5 * z ^ 4)) z := by
    have h2w : HasDerivAt (fun w : ℝ => 2 * w) 2 z := hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    exact h2w.mul hQ
  have hq : HasDerivAt (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5) / (1 + w) ^ 7) (2 * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1) / (1 + z) ^ 8) z := by
    refine (hnum.fun_div hden hp7).congr_deriv ?_
    field_simp [h1, hp7, hp72]
    ring
  exact hq.deriv

/-! ## The sixth `D_z`-iterate of the profile -/

/-- The closed form of the sixth `D_z`-iterate of `FM.Fstar` at `z ≠ -1`. -/
theorem FMFstar_six_eq {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ
      = 2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
          / (1 + z) ^ 8 := by
  have hstep : Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ
      = z * deriv (fun w : ℝ => Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  rw [hstep]
  have hfun : (fun w : ℝ => Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ) =ᶠ[𝓝 z]
      (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
        / (1 + w) ^ 7) := by
    filter_upwards [(isOpen_ne (x := (-1 : ℝ))).mem_nhds hz] with w hw
    exact DzIter_FM_Fstar_five_eq hw θ
  rw [Filter.EventuallyEq.deriv_eq hfun, FMFstar_six_deriv hz]
  ring

/-! ## The order-`6` decay -/

/-- **The sixth `D_z`-iterate of the plain profile decays like `1/z`.** -/
theorem DzIter_FM_Fstar_six_le {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ| ≤ 10080 / z := by
  rw [FMFstar_six_eq (by linarith : z ≠ -1) θ]
  have hz0 : (0 : ℝ) < z := by linarith
  have hz0' : (0 : ℝ) ≤ z := by linarith
  have hNUM :
      |z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1| ≤ 5040 * z ^ 6 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [pow_nonneg hz0' 2, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5, pow_nonneg hz0' 6, hz]
    · nlinarith [pow_nonneg hz0' 2, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5, pow_nonneg hz0' 6, hz]
  have hnum2 : |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)|
      ≤ 2 * z * (5040 * z ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left hNUM (by positivity)
  calc |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
        / (1 + z) ^ 8|
      = |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)|
          / (1 + z) ^ 8 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 8)]
    _ ≤ (2 * z * (5040 * z ^ 6)) / (1 + z) ^ 8 :=
        div_le_div_of_nonneg_right hnum2 (by positivity)
    _ = 10080 * z ^ 7 / (1 + z) ^ 8 := by ring
    _ ≤ 10080 / z := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 8) hz0]
        have h8 : z ^ 8 ≤ (1 + z) ^ 8 := by
          have h := pow_le_pow_left₀ hz0' (by linarith : z ≤ 1 + z) 8
          simpa using h
        nlinarith [h8]

/-! ## The order-`6` jet bound -/

theorem FM_Fstar_jet_le6 :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ C / z := by
  refine ⟨10080, by norm_num, fun j hj z hz θ => ?_⟩
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    exact DzIter_FM_Fstar_six_le hz θ
  · have hj5 : j ≤ 5 := by omega
    rcases eq_or_lt_of_le hj5 with h5 | h5
    · subst h5
      exact (Work.FTS.LocDataExt.DzIter_FM_Fstar_five_le hz θ).trans
        (div_le_div_of_nonneg_right (by norm_num : (1440 : ℝ) ≤ 10080) (by linarith))
    · have hj4 : j ≤ 4 := by omega
      exact (Work.FTS.LocDataExt.DzIter_FM_Fstar_le_four5 hj4 hz θ).trans
        (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 10080) (by linarith))

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.GalClass6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false

/-- **The localised datum lies in `GalClass α`**, from its `RegQ α 6`-regularity, its decay
`DecayAll 6` and the vanishing of `L₁₂(·)(0)`. -/
theorem galClass_locG6_of (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (hreg : Work.FTS.Nonlin.RegQ α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)))
    (hdec : Work.Spaces.DecayAll 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)))
    (hl12 : Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0) :
    Work.FTS.Nonlin.GalClass α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hv : Work.Spaces.VanishTheta (Work.FTS.LocData.hLoc α) :=
    (Work.FTS.LocData.hLoc_vanishing α hα).1
  refine ⟨hreg, ?_, ?_, hdec, hl12⟩
  · exact Work.FTS.LocData.vanishTheta_locG α L β hα hα1
      (fun z => ⟨hv.1 z, hv.2 z⟩)
  · exact Work.FTS.LocData.zero_slice_locG α L β hα hα1
      (fun z θ hz => Work.FTS.LocData.hLoc_eq_zero_of_le α hz θ) hL

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.HkSq_zfar_Fstar_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option maxHeartbeats 1600000

/-! ## The two pointwise inputs -/

/-- `(a·X)² ≤ a²·R` from `X² ≤ R` (for an arbitrary real `a`, since `a² ≥ 0`). -/
private theorem sq_mul_le_sq {a X R : ℝ} (h : X ^ 2 ≤ R) : (a * X) ^ 2 ≤ a ^ 2 * R := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg a)

/-- **The radial input of the order-`6` majorant**: the `D_z`-jets of the far factor
`(α/c)·zfarR L` are bounded by `(α/c)²A²·64/(1+z)²` after multiplication with the radial weight
`w` and squaring.

For `z ≥ L` this is the jet bound `hAz` together with `w(z)²/z² ≤ 64/(1+z)²` (which uses
`z ≥ L ≥ 1`); for `z < L` the cut-off vanishes on a neighbourhood of `z`, so every jet of
`zfarR L` vanishes at `z`. -/
private theorem hB_zfar6_pos (α L : ℝ) {A : ℝ} (_hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => (α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- below `L` the cut-off vanishes on a neighbourhood of `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [Work.FTS.LocDataExt.zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have hnn : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using hnn
    · -- above `L` use the jet bound and `w²/z² ≤ 64/(1+z)²`
      push Not at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
          (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1' : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1' 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hstep : ((α / Work.Spaces.c α)
        * (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
            * Work.Spaces.w z)) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
    sq_mul_le_sq hmain
  calc ((α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
        * Work.Spaces.w z) ^ 2
      = ((α / Work.Spaces.c α)
          * (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
              * Work.Spaces.w z)) ^ 2 := by ring
    _ ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) := hstep
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-- **The pointwise `ℋ⁶`-majorant of the far part** `zfar L F_*`, from the order-`6` jet bound
of `zfarR L` and the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²`: the `ℋ⁶`-integrand is dominated by
`((7 + 49Rθ)·(α/c)²A²·64)·angMaj α θ/(1+z)²`.

This is the generic separable majorant `LocDataExt.HkIntegrand_sepGam_le` at `k = 6` applied to
the factorisation `LocDataExt.zfar_Fstar_eq`. -/
private theorem maj_zfar_Fstar6 (α : ℝ) (hα : 0 < α) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∀ L : ℝ, 1 ≤ L → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64)
            * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  intro L hL z hz θ hθ
  have hB := hB_zfar6_pos α L hA hL (fun j hj z hz θ => hAz L hL j hj z hz θ)
  have hmain := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => (α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (R := (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) (Rθ := Rθ)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg A)) (by norm_num)) hRθ hB hΓ hz hθ
  rw [Work.FTS.LocDataExt.zfar_Fstar_eq α L]
  simpa using hmain

/-! ## The far-tail bound -/

theorem HkSq_zfar_Fstar_le6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C * α / L := by
  set Ang : ℝ := ∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ with hAngdef
  have hAng0 : 0 ≤ Ang := by
    rw [hAngdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Work.FTS.LocData.angMaj_nonneg hθ)
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hRθ0 : (0 : ℝ) ≤ (7 : ℝ) + 49 * Rθ := by linarith
  refine ⟨((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hRθ0 (by positivity)) hAng0
  · intro L hL
    have hLpos : 0 < L := by linarith
    set K : ℝ := ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) with hKdef
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg hRθ0 (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg A)) (by norm_num))
    have hmaj := maj_zfar_Fstar6 α hα hA hRθ hAz hΓ
    have hslice : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ :=
      (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
    have hmajint : ∀ z ∈ Work.Spaces.Iz, L ≤ z →
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) ≤ K * Ang / z ^ 2 := by
      intro z hz hzL
      have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
        intro θ hθ
        rw [hKdef]
        exact hmaj L hL z hz θ hθ
      have hle : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
          (hslice z hz) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpt θ hθ
      have hval : (∫ θ in Work.Spaces.Iθ, K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
          = K * Ang / (1 + z) ^ 2 := by
        rw [show (fun θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
            = fun θ => (K / (1 + z) ^ 2) * Work.FTS.LocData.angMaj α θ from by
          funext θ; ring]
        rw [MeasureTheory.integral_const_mul, hAngdef]
        ring
      have hzpos : 0 < z := lt_of_lt_of_le hLpos hzL
      have hden : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hzpos]
      have hz2 : (0 : ℝ) < z ^ 2 := by positivity
      have hstep : K * Ang / (1 + z) ^ 2 ≤ K * Ang / z ^ 2 := by
        have hB : ((1 + z) ^ 2)⁻¹ ≤ (z ^ 2)⁻¹ := by
          have h := one_div_le_one_div_of_le hz2 hden
          simpa [one_div] using h
        calc K * Ang / (1 + z) ^ 2 = (K * Ang) * ((1 + z) ^ 2)⁻¹ := by ring
          _ ≤ (K * Ang) * (z ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hB (mul_nonneg hK0 hAng0)
          _ = K * Ang / z ^ 2 := by ring
      linarith [hle, hval.le, hval.ge, hstep]
    -- the far-tail dominance, then `HkSqZfar`
    have hMnn : (0 : ℝ) ≤ K * Ang := mul_nonneg hK0 hAng0
    have hdom : Work.Stability.FarTailDom α 6 (Real.sqrt (K * Ang)) L
        (Work.Construction.Fstar α) := by
      intro z hz hzL
      rw [Real.sq_sqrt hMnn]
      exact hmajint z hz hzL
    have hkey := Work.Stability.HkSqZfar (α := α) (k := 6) (M := Real.sqrt (K * Ang))
      (Z := L) (f := Work.Construction.Fstar α) hLpos (Real.sqrt_nonneg _) hdom
    rw [Real.sq_sqrt hMnn] at hkey
    refine hkey.trans ?_
    -- the constants: `K ≤ (7 + 49Rθ)·100A²·64·α`
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
    have hq : (α / Work.Spaces.c α) ^ 2 ≤ 100 * α := by
      have hc10' : (1 : ℝ) / Work.Spaces.c α ≤ 10 := by
        rw [div_le_iff₀ hcpos]
        linarith
      have hc100 : ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ 100 := by
        have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
        have h2 : ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ (10 : ℝ) ^ 2 :=
          pow_le_pow_left₀ h1 hc10' 2
        have h3 : (10 : ℝ) ^ 2 = 100 := by norm_num
        rwa [h3] at h2
      have he : (α / Work.Spaces.c α) ^ 2
          = α ^ 2 * ((1 : ℝ) / Work.Spaces.c α) ^ 2 := by
        rw [div_pow]
        ring
      have h3 : α ^ 2 * ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ α ^ 2 * 100 :=
        mul_le_mul_of_nonneg_left hc100 (sq_nonneg α)
      have h4 : (α / Work.Spaces.c α) ^ 2 ≤ α ^ 2 * 100 := by
        rw [he]
        exact h3
      nlinarith [h4, hα2, hα.le]
    have hstep : (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 ≤ (100 * α) * A ^ 2 * 64 := by
      have h1 : (α / Work.Spaces.c α) ^ 2 * A ^ 2 ≤ (100 * α) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hq hA2
      exact mul_le_mul_of_nonneg_right h1 (by norm_num)
    have hKle : K ≤ ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α := by
      rw [hKdef]
      have hfin := mul_le_mul_of_nonneg_left hstep hRθ0
      calc ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64)
          ≤ ((7 : ℝ) + 49 * Rθ) * ((100 * α) * A ^ 2 * 64) := hfin
        _ = ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α := by ring
    have hKAng : K * Ang ≤ ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang * α := by
      have h := mul_le_mul_of_nonneg_right hKle hAng0
      calc K * Ang ≤ (((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α) * Ang := h
        _ = ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang * α := by ring
    exact div_le_div_of_nonneg_right hKAng (le_of_lt hLpos)

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.Small6Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Membership in `ℋ⁶` by domination -/

/-- **Membership in `ℋ⁶` by domination**: if the `ℋ⁶`-integrand of `h` is continuous on the open
quadrant and dominated by the integrable majorant `K·angMaj α θ/(1+z)²`, then `h ∈ ℋ⁶`. -/
theorem HkMem_h_of_majorant6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hsh : Work.FTS.LocData.SmoothQuad h)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 6 h := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _ hsh
  refine Work.FTS.LocData.HkMem_of_majorant (f := h)
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6 hcont ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · intro z hz θ hθ
    exact hK z hz θ hθ

/-! ## The `ℋ⁶`-norm of `locG α L β h` -/

/-- **The order-`6` `ℋ⁶`-bound on the localised perturbation**, for an arbitrary bump `h`: if
`C₀` bounds `L·HkSq α 6 (zfar L F_*)` and `C₁` bounds `HkSq α 6 h`, then

  `HkNorm α 6 (locG α L β h) ≤ √(2C₀α/L) + √2·|β|·√C₁`.

This is the order-`6` instance of `Work.FTS.LocData.HkNorm_locG_le_gen`. -/
theorem HkNorm_locG_le_gen6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    {L β C₀ C₁ : ℝ} (hL : 1 ≤ L) (hsh : Work.FTS.LocData.SmoothQuad h)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁)
    (hmemT : Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)))
    (hmemH : Work.Spaces.HkMem α 6 h)
    (hC₀ : Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α))
      ≤ C₀ * α / L)
    (hC₁ : Work.Spaces.HkSq α 6 h ≤ C₁) :
    Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by
  have hmeqb : Work.Spaces.HkMem α 6 (fun z θ => β * h z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 β hmemH
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h)
      ≤ 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁ := by
    have hxy : Work.FTS.LocData.locG α L β h
        = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
      funext z θ
      exact Work.FTS.LocData.locG_eq_zfar α L β h z θ
    rw [hxy]
    have hAB := Work.FTS.LocData.HkSq_add_le (α := α) (k := 6)
      (a := fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
      (b := fun z θ => β * h z θ)
      (Work.FTS.LocData.smoothQuad_neg (Work.FTS.LocData.SmoothQuad_zfar_Fstar α L))
      (Work.FTS.LocData.smoothQuad_const_mul β hsh)
      (Work.FTS.LocData.HkMem_neg α 6 hmemT) hmeqb
    have h1 : Work.Spaces.HkSq α 6
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        = Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
      Work.FTS.LocData.HkSq_neg α 6 _
    have h2 : Work.Spaces.HkSq α 6 (fun z θ => β * h z θ) = β ^ 2 * Work.Spaces.HkSq α 6 h :=
      Work.FTS.LocData.HkSq_const_mul α 6 β hmemH
    have hb : 2 * (β ^ 2 * Work.Spaces.HkSq α 6 h) ≤ 2 * β ^ 2 * C₁ := by
      nlinarith [sq_nonneg β, hC₁]
    linarith [hAB, h1.le, h1.ge, h2.le, h2.ge, hC₀, hb]
  have hmono : Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h))
      ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := Real.sqrt_le_sqrt hsq
  have hLpos : 0 < L := by linarith
  have h2C₀ : (0 : ℝ) ≤ 2 * (C₀ * α / L) := by
    have : 0 ≤ C₀ * α / L := div_nonneg (mul_nonneg hC₀nn hα.le) hLpos.le
    linarith
  have h2C₁ : (0 : ℝ) ≤ 2 * β ^ 2 * C₁ := by
    have : 0 ≤ β ^ 2 * C₁ := mul_nonneg (sq_nonneg β) hC₁nn
    linarith
  have hsplit : Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := by
    have h1 : 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁
        ≤ (Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2 := by
      have ha := Real.sq_sqrt h2C₀
      have hb := Real.sq_sqrt h2C₁
      have ha' := Real.sqrt_nonneg (2 * (C₀ * α / L))
      have hb' := Real.sqrt_nonneg (2 * β ^ 2 * C₁)
      nlinarith [ha, hb, ha', hb']
    calc Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
        ≤ Real.sqrt ((Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) :=
          Real.sqrt_sq (by positivity)
  have hscal : Real.sqrt (2 * β ^ 2 * C₁) = Real.sqrt 2 * |β| * Real.sqrt C₁ := by
    rw [show (2 : ℝ) * β ^ 2 * C₁ = 2 * β ^ 2 * C₁ by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * β ^ 2) C₁,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (β ^ 2), Real.sqrt_sq_eq_abs]
  calc Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h)
      = Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.LocData.locG α L β h)) := rfl
    _ ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := hmono
    _ ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := hsplit
    _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by rw [hscal]

/-! ## The `ε`-smallness at order `6` -/

/-- **THE ORDER-`6` SMALLNESS (generic bump).**  For every `ε > 0` there is `L₀` such that for
every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, `L₁₂(locG α L β h)(0) = 0` and
`HkNorm α 6 (locG α L β h) ≤ ε`.  This is `Work.FTS.LocData.locData_small_general` at order `6`;
the two facts about the far part are the hypotheses `hC₀` (`α/L`-decay of `HkSq α 6`) and `hZT`
(membership in `ℋ⁶`). -/
theorem locData6_small_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad h)
    (hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ ≤ K ^ 2 * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    (hD : 0 < Work.Construction.L12 h 0)
    (hlin : ∀ L β : ℝ, 1 ≤ L → Work.Construction.L12 (Work.FTS.LocData.locG α L β h) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 h 0)
    (hC₀ : ∃ C₀ : ℝ, ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C₀ * α / L)
    (hZT : ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α))) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (Work.FTS.LocData.locG α L β h) 0 = 0 ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.LocData.locG α L β h) ≤ ε := by
  intro ε hε
  obtain ⟨C₀, hC₀'⟩ := hC₀
  have hmemH : Work.Spaces.HkMem α 6 h := HkMem_h_of_majorant6 α hα hα1 hsm hmaj
  set C₁ : ℝ := Work.Spaces.HkSq α 6 h with hC₁def
  have hC₁ : Work.Spaces.HkSq α 6 h ≤ C₁ := le_of_eq hC₁def.symm
  have hC₁nn : (0 : ℝ) ≤ C₁ := by rw [hC₁def]; exact Work.Spaces.HkSq_nonneg α 6 h
  obtain ⟨D, hDdef, hDpos⟩ : ∃ D : ℝ, D = Work.Construction.L12 h 0 ∧ 0 < D :=
    ⟨_, rfl, hD⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h : 0 ≤ C₀ * α / 1 :=
      le_trans (Work.Spaces.HkSq_nonneg α 6 _) (by simpa using hC₀' 1 le_rfl)
    nlinarith [hα]
  have hεpos : 0 < ε := hε
  set L₀ : ℝ := max 1 (max (8 * C₀ * α / ε ^ 2)
    (max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)))) with hL₀
  refine ⟨L₀, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 8 * C₀ * α / ε ^ 2 ≤ L := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    exact this
  have hL3 : 4 * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_left _ _) h1
  have hL4 : 8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_right _ _) h1
  have hLpos : 0 < L := by linarith
  refine ⟨Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D,
    ?_, ?_, ?_⟩
  · -- `|β| ≤ ε`
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := Work.FTS.LocData.L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hden : 0 < ε * D := mul_pos hεpos hDpos
    have h3 : 4 * α / L ≤ ε * D := by
      rw [div_le_iff₀ hLpos]
      have h3' : 4 * α ≤ ε * D * L := by
        rw [div_le_iff₀ hden] at hL3
        linarith [hL3]
      linarith [h3']
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    linarith [hN, h3]
  · -- the `L₁₂`-orthogonality at `z = 0`
    rw [hlin L _ hL1]
    rw [show Work.Construction.L12 h 0 = D from hDdef.symm]
    rw [div_mul_cancel₀ _ (ne_of_gt hDpos)]
    ring
  · -- the `ℋ⁶`-bound
    refine le_trans (HkNorm_locG_le_gen6 α hα hα1 hL1 hsm hC₀nn hC₁nn (hZT L hL1) hmemH
      (hC₀' L hL1) hC₁) ?_
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := Work.FTS.LocData.L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hβb : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D|
        ≤ 4 * α / (L * D) := by
      rw [abs_div, abs_of_pos hDpos]
      rw [show 4 * α / (L * D) = (4 * α / L) / D by field_simp]
      rw [div_le_iff₀ hDpos, div_mul_cancel₀ _ (ne_of_gt hDpos)]
      exact hN
    have harg1 : 2 * (C₀ * α / L) ≤ (ε / 2) ^ 2 := by
      have h2 : 8 * C₀ * α ≤ ε ^ 2 * L := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at hL2
        linarith [hL2]
      rw [show (2 : ℝ) * (C₀ * α / L) = 2 * C₀ * α / L by ring]
      rw [div_le_iff₀ hLpos]
      nlinarith [h2]
    have hsqrt1 : Real.sqrt (2 * (C₀ * α / L)) ≤ ε / 2 := by
      calc Real.sqrt (2 * (C₀ * α / L)) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt harg1
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    have hβterm : Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁ ≤ ε / 2 := by
      have h2 : 0 ≤ Real.sqrt 2 * Real.sqrt C₁ :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
            (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁
          = (Real.sqrt 2 * Real.sqrt C₁) * |Work.Construction.L12 (Work.Stability.zfar L
              (Work.Construction.Fstar α)) 0 / D| := by ring
        _ ≤ (Real.sqrt 2 * Real.sqrt C₁) * (4 * α / (L * D)) :=
            mul_le_mul_of_nonneg_left hβb h2
        _ = (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) * (ε / (2 * L)) := by
            field_simp
            ring
        _ ≤ L * (ε / (2 * L)) := mul_le_mul_of_nonneg_right hL4 (by positivity)
        _ = ε / 2 := by field_simp
    linarith [hsqrt1, hβterm]

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.ZfarMaj6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The radial bound of the far summand** `-(α/c)·zfarR L z` at order `6`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar6 (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hsplit : ((-(α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2
      = (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 := by
    ring
  rw [hsplit]
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- the cut-off vanishes near `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [Work.FTS.LocDataExt.zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using this
    · push_neg at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
          (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1 : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp <;> ring
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  calc (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-- **The pointwise `ℋ⁶`-majorant of the far summand of the localised datum**: with the order-`6`
jet bound of `zfarR L` and the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²`, the `ℋ⁶`-integrand of
`(-(α/c)·zfarR L)·Γ` is dominated by `((7 + 49·Rθ)·(α/c)²A²·64)·angMaj α θ/(1+z)²`. -/
theorem HkIntegrand_zfar6_le (α L : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
        (fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          * Work.Spaces.Gam α θ) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  refine ⟨((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64), by positivity,
    fun z hz θ hθ => ?_⟩
  have hB := hB_zfar6 α L hA hL hAz
  exact Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (R := (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) (Rθ := Rθ) (by positivity) hRθ
    (fun j hj z hz' θ' => hB j hj z hz' θ') hΓ hz hθ

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.decayAll_locG6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial profile `FM.Fstar z = 2z/(1+z)²`: closed form of the derivatives -/

/-- `F_*` is a rational function whose only pole is at `z = -1`, hence analytic (order `⊤`) on
the half-line `(-1,∞)`. -/
private theorem contDiffOn_Fstar_analytic :
    ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  change ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2))
    (Set.Ioi (-1))
  exact h

/-- **The one-step derivative of the closed form**: with
`φ_j(w) = 2·(-1)^j·j!·(w-j)/(1+w)^(j+2)`, one has `φ_j' = φ_{j+1}`. -/
private theorem hasDerivAt_Fstar_formula (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ))
        / (1 + w) ^ (j + 2))
      (2 * (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) * (z - ((j + 1 : ℕ) : ℝ))
        / (1 + z) ^ (j + 1 + 2)) z := by
  have hz' : (1 : ℝ) + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ)))
      (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - ((j : ℕ) : ℝ)) 1 z :=
      (hasDerivAt_id z).sub_const ((j : ℕ) : ℝ)
    have h2 := h.const_mul (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ))
    simpa [mul_assoc] using h2
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 2))
      (((j + 2 : ℕ) : ℝ) * (1 + z) ^ (j + 1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow (j + 2)
    rw [show (fun w : ℝ => (1 + w) ^ (j + 2)) = (fun w : ℝ => 1 + w) ^ (j + 2) from by
      funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hdiv := hnum.div hden (pow_ne_zero _ hz')
  convert hdiv using 1
  · have h1 : (1 + z) ^ (j + 1 + 2) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
      rw [show j + 1 + 2 = (j + 1) + 2 by omega, pow_add]
    have h2 : ((1 + z) ^ (j + 2)) ^ 2 = (1 + z) ^ (j + 2) * (1 + z) ^ (j + 2) := pow_two _
    have h3 : (1 + z) ^ (j + 2) = (1 + z) ^ (j + 1) * (1 + z) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    rw [h1, h2, h3]
    have hu : (1 + z) ^ (j + 1) ≠ 0 := pow_ne_zero _ hz'
    field_simp
    rw [show (-1 : ℝ) ^ (j + 1) = -(-1) ^ j by rw [pow_succ]; ring]
    rw [show ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) by
      rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring

/-- **The closed form of the iterated derivatives of the plain profile**:
`∂^j F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` on `(-1,∞)`. -/
private theorem deriv_iter_Fstar_eq (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    deriv^[j] (fun z => Work.FM.Fstar z) z
      = 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
      rw [Function.iterate_zero_apply]
      simp only [Work.FM.Fstar]
      norm_num
  | succ n ih =>
      have hEqOn : Set.EqOn (deriv^[n] (fun z => Work.FM.Fstar z))
          (fun w : ℝ => 2 * (-1 : ℝ) ^ n * (n.factorial : ℝ) * (w - (n : ℝ))
            / (1 + w) ^ (n + 2)) (Set.Ioi (-1)) := fun w hw => ih hw
      rw [Function.iterate_succ_apply', hEqOn.deriv isOpen_Ioi hz]
      exact (hasDerivAt_Fstar_formula n hz).deriv

/-! ## The decay bounds -/

/-- **`∂^j F_*` decays like `1/z`**: `|∂^j F_* z| ≤ 2·j!·(j+1)/(1+z)` for `z ≥ 1`. -/
private theorem Fstar_deriv_abs_le (j : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |deriv^[j] (fun z => Work.FM.Fstar z) z|
      ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) / (1 + z) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hpos : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (j + 2) := pow_pos hpos _
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  rw [deriv_iter_Fstar_eq j hzI]
  have habs : |2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2)|
      = 2 * (j.factorial : ℝ) * |z - (j : ℝ)| / (1 + z) ^ (j + 2) := by
    rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hfac]
    ring
  rw [habs, div_le_div_iff₀ hden hpos]
  have hkey : |z - (j : ℝ)| ≤ ((j : ℝ) + 1) * (1 + z) := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [abs_le]
    constructor <;> nlinarith [hz, hj]
  have hstep1 : 2 * (j.factorial : ℝ) * |z - (j : ℝ)| * (1 + z)
      ≤ 2 * (j.factorial : ℝ) * (((j : ℝ) + 1) * (1 + z)) * (1 + z) := by
    gcongr
  have hstep2 : 2 * (j.factorial : ℝ) * (((j : ℝ) + 1) * (1 + z)) * (1 + z)
      = 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ 2 := by ring
  have hstep3 : 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ 2
      ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) * (1 + z) ^ (j + 2) := by
    have hle : (1 + z) ^ 2 ≤ (1 + z) ^ (j + 2) :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by omega : 2 ≤ j + 2)
    have hnn : (0 : ℝ) ≤ 2 * (j.factorial : ℝ) * ((j : ℝ) + 1) := by positivity
    exact mul_le_mul_of_nonneg_left hle hnn
  linarith [hstep1, hstep2.le, hstep2.ge, hstep3]

/-- **The weighted derivatives `z^k ∂^k F_*` decay like `1/z`**:
`|z^k ∂^k F_* z| ≤ 2·k!·(k+1)/(1+z)` for `z ≥ 1`. -/
private theorem Fstar_zpow_deriv_abs_le (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z|
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / (1 + z) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hpos : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hpos _
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hmain : |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z|
      = 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ k), deriv_iter_Fstar_eq k hzI,
      abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hfac]
    ring
  rw [hmain, div_le_div_iff₀ hden hpos]
  have hkey : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) := by
    have hj : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz, hj]
  have hzk : z ^ k ≤ (1 + z) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have hmul : z ^ k * |z - (k : ℝ)| ≤ (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) :=
    mul_le_mul hzk hkey (abs_nonneg _) (by positivity)
  have hstep1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| * (1 + z)
      ≤ 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z) := by
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| * (1 + z)
        = (2 * (k.factorial : ℝ)) * (z ^ k * |z - (k : ℝ)|) * (1 + z) := by ring
    have h2 : 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z)
        = (2 * (k.factorial : ℝ)) * ((1 + z) ^ k * (((k : ℝ) + 1) * (1 + z))) * (1 + z) := by
      ring
    rw [h1, h2]
    gcongr
  have hstep2 : 2 * (k.factorial : ℝ) * (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z)) * (1 + z)
      = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by
    rw [pow_add]
    ring
  linarith [hstep1, hstep2.le, hstep2.ge]

/-! ## The two radial limits -/

/-- A function dominated by `C/(1+z)` eventually tends to `0` at `∞`. -/
private theorem tendsto_of_abs_le_div (f : ℝ → ℝ) (C : ℝ)
    (h : ∀ᶠ z in atTop, |f z| ≤ C / (1 + z)) : Tendsto f atTop (𝓝 0) := by
  have h1z : Tendsto (fun z : ℝ => (1 : ℝ) + z) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have hup : Tendsto (fun z : ℝ => C / (1 + z)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1z
  have habs : Tendsto (fun z : ℝ => |f z|) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ h
    filter_upwards with z
    exact abs_nonneg (f z)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- **The plain derivatives of the profile decay**: `∂^j F_* z → 0` as `z → ∞`. -/
private theorem tendsto_deriv_iter_Fstar (j : ℕ) :
    Tendsto (fun z : ℝ => deriv^[j] (fun z => Work.FM.Fstar z) z) atTop (𝓝 0) := by
  refine tendsto_of_abs_le_div _ (2 * (j.factorial : ℝ) * ((j : ℝ) + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact Fstar_deriv_abs_le j hz

/-- **The weighted derivatives of the profile decay**: `z^k ∂^k F_* z → 0` as `z → ∞`. -/
private theorem tendsto_zpow_deriv_iter_Fstar (k : ℕ) :
    Tendsto (fun z : ℝ => z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z) atTop (𝓝 0) := by
  refine tendsto_of_abs_le_div _ (2 * (k.factorial : ℝ) * ((k : ℝ) + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact Fstar_zpow_deriv_abs_le k hz

/-- **The `D_z`-iterates of the profile decay**: `D_z^b F_* z → 0` as `z → ∞`, for every angle
(the second variable of `fun z _ => F_* z` is a dummy). -/
private theorem tendsto_DzIter_Fstar (b : ℕ) (θ : ℝ) :
    Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ)
      atTop (𝓝 0) := by
  rw [show (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ)
      = fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 from
    funext (fun z => Work.FTS.LocDataExt.DzIter_z_only_apply (fun z => Work.FM.Fstar z) b z θ)]
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ hθ => contDiffOn_Fstar_analytic
  have hpt : ∀ z : ℝ, 1 ≤ z → (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z))
      = Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 := by
    intro z hz
    rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z
      (by simp only [Set.mem_Ioi]; linarith) 0 Work.Spaces.zero_mem_Iθ]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    congr 1
    rw [Work.FTS.GalBasis.pzIter_apply_eq_iterate_deriv]
  have hterm : ∀ k ∈ Finset.range (b + 1), Tendsto (fun z : ℝ => (Work.Spaces.scoef b k : ℝ)
      * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z)) atTop (𝓝 (0 : ℝ)) := by
    intro k hk
    simpa using (tendsto_zpow_deriv_iter_Fstar k).const_mul (Work.Spaces.scoef b k : ℝ)
  have hsum : Tendsto (fun z : ℝ => ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
      * (z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (s := Finset.range (b + 1)) (a := fun _ => (0 : ℝ)) hterm
    simpa using this
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact hpt z hz

/-! ## Transfer of iterated derivatives along equality in a right half-line -/

/-- Iterated plain `z`-derivatives of two functions which agree on the open half-line
`(Z,∞)` agree at every point of that half-line. -/
private theorem deriv_iter_eq_of_gt {ρ σ : ℝ → ℝ} {Z : ℝ} (h : ∀ z, Z < z → ρ z = σ z) :
    ∀ j : ℕ, ∀ z, Z < z → deriv^[j] ρ z = deriv^[j] σ z := by
  intro j
  induction j with
  | zero => intro z hz; exact h z hz
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine Filter.EventuallyEq.deriv_eq ?_
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih z' hz')

/-- Iterated weighted `z`-derivatives `D_z^j` of two `θ`-independent functions which agree on
the open half-line `(Z,∞)` agree at every point of that half-line (all `θ`). -/
private theorem DzIter_zonly_eq_of_gt {ρ σ : ℝ → ℝ} {Z : ℝ}
    (h : ∀ z, Z < z → ρ z = σ z) :
    ∀ j : ℕ, ∀ z, Z < z → ∀ θ, Work.Spaces.DzIter j (fun z _ => ρ z) z θ
      = Work.Spaces.DzIter j (fun z _ => σ z) z θ := by
  intro j
  induction j with
  | zero => intro z hz θ; exact h z hz
  | succ n ih =>
      intro z hz θ
      show Work.Spaces.Dz (Work.Spaces.DzIter n (fun z _ => ρ z)) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter n (fun z _ => σ z)) z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih z' hz' θ)

/-! ## The factorisations of `locG` along the two families of iterated derivatives -/

/-- The plain iterated derivatives of the perturbation factor through its radial factor `locR`
and the angular factor `Γ`. -/
private theorem pzIter_pthIter_locG (α L β : ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i
        (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))) z θ
      = deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
        * deriv^[i] (Work.Spaces.Gam α) θ := by
  have h1 : Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  have h2 : Work.Spaces.pthIter i (fun z θ => Work.FTS.LocDataExt.locR α L β z
        * Work.Spaces.Gam α θ)
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * deriv^[i] (Work.Spaces.Gam α) θ := by
    funext z θ
    exact Work.FTS.GalBasis.pthIter_mul_zonly_thetaonly i _ _ z θ
  have h3 : Work.Spaces.pzIter j (fun z θ => Work.FTS.LocDataExt.locR α L β z
        * deriv^[i] (Work.Spaces.Gam α) θ)
      = fun z θ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
          * deriv^[i] (Work.Spaces.Gam α) θ := by
    funext z θ
    exact Work.FTS.GalBasis.pzIter_mul_zonly_thetaonly j _ _ z θ
  rw [h1, h2, h3]

/-- The mixed iterated derivatives of the perturbation factor through `locR` and `Γ`. -/
private theorem mixed_locG (α L β : ℝ) (b a : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b a (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ
      = Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
        * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.FTS.LocDataExt.locG_eq_locR_Gam α L β,
    Work.FTS.LocDataExt.mixed_sepGam α (Work.FTS.LocDataExt.locR α L β) b a]

/-! ## The two limits of the radial factor `locR` -/

/-- **The plain `z`-derivatives of the radial factor decay.**  Beyond the localisation scale
`locR` is the constant multiple `-(α/c)·FM.Fstar` of the plain profile, whose derivatives tend
to `0`. -/
private theorem tendsto_deriv_iter_locR (α L β : ℝ) (hL : 0 < L) (j : ℕ) :
    Tendsto (fun z : ℝ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z) atTop (𝓝 0) := by
  have hbase : Tendsto (fun z : ℝ => -(α / Work.Spaces.c α)
      * deriv^[j] (fun w => Work.FM.Fstar w) z) atTop (𝓝 0) := by
    simpa using (tendsto_deriv_iter_Fstar j).const_mul (-(α / Work.Spaces.c α))
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (max (2 * L) (7 / 4))] with z hz
  have hfun : ∀ z' : ℝ, max (2 * L) (7 / 4) < z' →
      Work.FTS.LocDataExt.locR α L β z'
        = -(α / Work.Spaces.c α) * Work.FM.Fstar z' :=
    fun z' hz' => Work.FTS.LocDataExt.locR_eq_of_ge hL
      (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz'))
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz'))
  exact ((deriv_iter_eq_of_gt hfun j z hz).trans
    (Work.FTS.GalBasis.iterate_deriv_const_mul j (-(α / Work.Spaces.c α))
      (fun w => Work.FM.Fstar w) z)).symm

/-- **The weighted `z`-derivatives `D_z^b` of the radial factor decay.**  Same reduction as
above, with the `D_z`-iterates. -/
private theorem tendsto_DzIter_locR (α L β : ℝ) (hL : 0 < L) (b : ℕ) (θ : ℝ) :
    Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z)
      z θ) atTop (𝓝 0) := by
  have hbase : Tendsto (fun z : ℝ => -(α / Work.Spaces.c α)
      * Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ) atTop (𝓝 0) := by
    simpa using (tendsto_DzIter_Fstar b θ).const_mul (-(α / Work.Spaces.c α))
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (max (2 * L) (7 / 4))] with z hz
  have hfun : ∀ z' : ℝ, max (2 * L) (7 / 4) < z' →
      Work.FTS.LocDataExt.locR α L β z'
        = -(α / Work.Spaces.c α) * Work.FM.Fstar z' :=
    fun z' hz' => Work.FTS.LocDataExt.locR_eq_of_ge hL
      (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz'))
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz'))
  have hcm := congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul (-(α / Work.Spaces.c α))
    (fun z _ => Work.FM.Fstar z) b) z) θ
  exact ((DzIter_zonly_eq_of_gt hfun b z hz θ).trans hcm).symm

/-! ## The deliverable -/

/-- **The order-`6` localised datum decays**: every plain partial derivative `∂_z^j∂_θ^i` and
every mixed derivative `D_z^bD_θ^a` with `i + j ≤ 6` resp. `a + b ≤ 6` tends to `0` as
`z → ∞`, at every fixed angle `θ ∈ [0,π/2]`. -/
theorem decayAll_locG6 (α L β : ℝ) (hL : 1 ≤ L) :
    Work.Spaces.DecayAll 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · intro j i hij θ hθ
    rw [show (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i
          (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))) z θ)
        = fun z : ℝ => deriv^[j] (Work.FTS.LocDataExt.locR α L β) z
            * deriv^[i] (Work.Spaces.Gam α) θ from
      funext (fun z => pzIter_pthIter_locG α L β j i z θ)]
    simpa using (tendsto_deriv_iter_locR α L β hL0 j).mul_const
      (deriv^[i] (Work.Spaces.Gam α) θ)
  · intro a b hab θ hθ
    rw [show (fun z : ℝ => Work.Spaces.mixed b a
          (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ)
        = fun z : ℝ => Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
            * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ from
      funext (fun z => mixed_locG α L β b a z θ)]
    simpa using (tendsto_DzIter_locR α L β hL0 b θ).mul_const
      (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.hLoc_majorant6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.LocData6.hLoc_majorant6` — the order-`6` pointwise majorant of `hLoc α`

`hLoc α = bumpZ(z)·Γ(θ)` is separable; at order `6` the only new radial ingredient is that the
`D_z`-jets of the bump are bounded up to order `6` (the delivered order-`5` bound
`LocDataExt.DzIter_bumpZ_bound5` stops at `5`).  The angular input is *not* proved here: it is
supplied as the hypothesis `hΓ` of the statement (`(D_θ^iΓ)² ≤ 10¹⁰·Γ²`, `i ≤ 6`).

The assembly is the generic separable majorant `LocDataExt.HkIntegrand_sepGam_le` at `k = 6`,
which is where the order-`6` structure of the target statement lives.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The bump at order `6` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `6` are bounded. -/
theorem DzIter_bumpZ_bound6 :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 7,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 7,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by `HkIntegrand_sepGam_le` for the bump `bumpZ`, at order `6`. -/
theorem hB_bumpZ6 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound6
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-! ## The order-`6` majorant -/

theorem hLoc_majorant6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨R, hR, hB⟩ := hB_bumpZ6
  refine ⟨(7 + 49 * 10 ^ 10) * R, by positivity, fun z hz θ hθ => ?_⟩
  have hmain := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => Work.FTS.LocData.bumpZ z) (R := R) (Rθ := (10 : ℝ) ^ 10)
    hR (by positivity) hB hΓ hz hθ
  have hfun : (fun z θ => Work.FTS.LocData.bumpZ z * Work.Spaces.Gam α θ)
      = Work.FTS.LocData.hLoc α := by
    funext z θ
    rw [Work.FTS.LocData.hLoc_apply]
  rw [hfun] at hmain
  refine hmain.trans_eq ?_
  push_cast
  ring

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.oneSubChi_jet_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weighted derivatives of `1 - χ`, up to order `6`

The order-`5` chapter (`Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5`) proves
`|x ^ k · ∂^k (1 - χ)(x)| ≤ M` for `k ≤ 5` by a crude argument: for `k = 0` the bound is `1`,
and for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is `C^∞`) and
vanishes off `|x| ≤ 2`, hence bounded on the compact `[-2,2]`.  Nothing in that argument uses
the order `5`, so we get order `6` by adding the single case `k = 6` to the order-`5` bound. -/

/-- **The weighted derivatives of `1 - χ` are bounded up to order `6`.**  There is a constant
`M` dominating `|x ^ k · ∂^k (1 - χ)(x)|` for all `k ≤ 6` and all `x : ℝ`. -/
theorem OneSubChi_deriv_bound6 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 6, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  obtain ⟨M5, hM5nn, hM5⟩ := Work.FTS.LocDataExt.OneSubChi_deriv_bound5
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  -- the new case `k = 6`
  have hkey6 : ∃ M6 : ℝ, 0 ≤ M6 ∧ ∀ x : ℝ,
      |x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ M6 := by
    have hcont : Continuous (fun x : ℝ =>
        x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
      (continuous_id.pow 6).mul (hsm.continuous_iteratedDeriv 6 (by simp))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun x : ℝ =>
        x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
      hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : |x| ≤ 2
    · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
        rw [Set.mem_Icc, ← abs_le]; exact hx
      have hbound := hC x hxmem
      rw [Real.norm_eq_abs] at hbound
      exact le_trans hbound (le_max_left _ _)
    · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so its derivatives vanish there
      have hx2 : 2 < |x| := not_le.mp hx
      have hvan : iteratedDeriv 6 Work.Stability.chi x = 0 := by
        have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
            (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
          filter_upwards [hmem] with y hy
          exact Work.Stability.chi_eq_zero (le_of_lt hy)
        rw [hev.iteratedDeriv_eq 6, Work.Spaces.iteratedDeriv_zero_fun 6 x]
      have hg6 : iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = - iteratedDeriv 6 Work.Stability.chi x := by
        rw [iteratedDeriv_const_sub (by norm_num : 0 < 6) (1 : ℝ)]
        simp
      rw [hg6, hvan]
      simp
  obtain ⟨M6, hM6nn, hM6⟩ := hkey6
  refine ⟨M5 + M6, by linarith, fun k hk x => ?_⟩
  by_cases h : k ≤ 5
  · exact le_trans (hM5 k h x) (by linarith)
  · have hk6 : k = 6 := by omega
    subst hk6
    exact le_trans (hM6 x) (by linarith)


/-- **The `D_z`-jets of the cut-off factor `1 - χ(z/L)` are bounded uniformly in the scale
`L ≥ 1`, up to order `6`.**  This extends the delivered
`Work.FTS.LocDataExt.oneSubChi_jet_le5` (orders `≤ 5`, `z ∈ Iz = Ici 0`) by one order: the same
Stirling expansion `DzIterZ_eq_sum_scoef` + dilation `IteratedDeriv_comp_div` +
`abs_sum_scoef_mul_le`, with the extra input `|x^k · ∂^k(1-χ)(x)| ≤ M` for `k ≤ 6`
(`OneSubChi_deriv_bound6`) and `bell 6 = 203 ≤ 300` in place of `bell_le c hc`, `c ≤ 5`. -/
theorem oneSubChi_jet_le6 :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound6
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨300 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the θ-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c
          (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (Work.FTS.LocData.DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`, uniformly in `L`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk6 : k ≤ 6 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      Work.FTS.LocData.IteratedDeriv_comp_div
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k
            (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk6 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 300 := by
    have h : Work.Spaces.bell c ≤ 300 := by interval_cases c <;> decide
    exact_mod_cast h
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 300 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData6

set_option maxHeartbeats 1600000

/-- The binomial sum in closed form, order-`6` copy: `∑_{b≤j} (j choose b) = 2^j`. -/
private theorem sum_range_choose_real6 (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = 2 ^ j := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- **The assembly**: from a bound `Cu` for the `D_z`-jets of the cut-off factor
`1 - χ(·/L)` (uniform in the scale `L ≥ 1`) up to order `6` and a bound `Cv/z` for the
`D_z`-jets of `FM.Fstar` up to order `6`, the jets of `zfarR L = (1 - χ(·/L))·FM.Fstar`
decay like `(64·Cu·Cv)/z` on `[L, 2L]`, uniformly in `L ≥ 1`.

The proof is the order-`6` instance of the Leibniz computation of
`Work.FTS.LocDataExt.zfarR_jet_le5_of_jets`: by the Leibniz rule the `j`-th jet (`j ≤ 6`) is
`∑_{b≤j} (j choose b)·(jet_b u)·(jet_{j-b} v)`, both factors of every summand are at order
`≤ 6` (so each is `≤ (j choose b)·Cu·Cv/z`), and summing with the binomial theorem and
`2^6 = 64` gives the claim. -/
theorem zfarR_jet_le6_of_jets {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 6 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 →
      ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ 64 * Cu * Cv / z := by
  intro L hL j hj z hz θ
  have hz1 : 1 ≤ z := le_trans hL hz.1
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz0 : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hCu1
  have hCvz : 0 ≤ Cv / z := div_nonneg (le_of_lt hCv) (le_of_lt hzpos)
  rw [Work.FTS.LocDataExt.DzIter_zfarR_eq_sum L j hz0 θ]
  have hstep : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
        ≤ (j.choose b : ℝ) * (Cu * (Cv / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have h1 : b ≤ 6 := le_trans hbj hj
    have h2 : j - b ≤ 6 := by omega
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (hCu L hL b h1 z hz0 θ) (hCvM (j - b) h2 z hz1 θ)
      (abs_nonneg _) hCu0
  calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.DzIter b (fun z _ => 1 - Work.Stability.chi (z / L)) z θ
          * Work.Spaces.DzIter (j - b) (fun z _ => Work.FM.Fstar z) z θ)|
      ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Cu * (Cv / z)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)
    _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * (Cu * (Cv / z)) := by
        rw [Finset.sum_mul]
    _ = 2 ^ j * (Cu * (Cv / z)) := by rw [sum_range_choose_real6]
    _ ≤ 64 * Cu * Cv / z := by
        have h64 : (2 : ℝ) ^ j ≤ 64 := by
          have h : (2 : ℝ) ^ j ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
          norm_num at h
          exact h
        have hnn : 0 ≤ Cu * (Cv / z) := mul_nonneg hCu0 hCvz
        calc 2 ^ j * (Cu * (Cv / z)) ≤ 64 * (Cu * (Cv / z)) :=
              mul_le_mul_of_nonneg_right h64 hnn
          _ = 64 * Cu * Cv / z := by ring

end Work.FTS.LocData6
end
