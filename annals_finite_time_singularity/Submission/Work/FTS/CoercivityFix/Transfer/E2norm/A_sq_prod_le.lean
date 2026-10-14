import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.MinImports
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.C0_sq_le4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


private lemma E2 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^4 = 3*π/16 := by
  rw [integral_cos_pow (n := 2)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero,
    integral_cos_sq]
  ring

private lemma E3 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^6 = 5*π/32 := by
  rw [integral_cos_pow (n := 4)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  rw [E2]; ring

private lemma E4 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^8 = 35*π/256 := by
  rw [integral_cos_pow (n := 6)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  rw [E3]; ring







private lemma continuousOn_w_Ioi : ContinuousOn Spaces.w (Set.Ioi (0 : ℝ)) := by
  unfold Spaces.w
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (ne_of_gt hx))




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Ef_le_EfEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.GamDivCSqInt_le_five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-! ## Two elementary bounds on the angular interval -/

/-- The pointwise `L²`-weighted AM–GM estimate behind the sharp constant:
`F² ≤ (22/7)(F-G)² + (22/15)G²` for all reals `F, G`.

The two coefficients are chosen so that `(22/7 - 1)(F-G)² - 2(F-G)G + (22/15 - 1)G²`
`= (15(F-G) - 7G)²/105 ≥ 0`; this makes `(22/7)·(7/10)² + (22/15)·(9/4) = 121/25 < 5`. -/
theorem sq_le_two_thirds (F G : ℝ) :
    F ^ 2 ≤ (22 / 7) * (F - G) ^ 2 + (22 / 15) * G ^ 2 := by
  nlinarith [sq_nonneg (15 * (F - G) - 7 * G)]

/-- `|K θ| ≤ 3` on the angular interval, since `K θ = 3 sin θ cos²θ` and both `sin` and
`cos` are bounded by `1` in absolute value. -/
theorem abs_K_le_three {θ : ℝ} :
    |Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hc2 : |Real.cos θ| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ), hc]
  rw [Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]
  nlinarith [hs, hc2, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]

/-- The sharp angular `L²` bound for `Γ/c`: `∫_θ (Γ(θ)/c)² dθ ≤ 5`.

`GammaL2Bnd α` (in `Submission/Work/Coercivity/Defs.lean`) is
`∫ θ in Spaces.Iθ, (Γ(θ)/c - K(θ))² ≤ (7/10)²`, and `integral_Iθ_Ksq_le`
(in `Submission/Work/Coercivity/L2CoercivityTransport.lean`) is
`∫ θ in Spaces.Iθ, K(θ)² ≤ 9/4`.  Writing `Γ/c = (Γ/c - K) + K` and expanding the square
gives `∫(Γ/c)² ≤ (∫(Γ/c-K)²) + 2∫(Γ/c-K)K + ∫K²`, and Cauchy–Schwarz in `L²`
(`cs_integral_mul`, same file) bounds the cross term by `√(∫(Γ/c-K)²)·√(∫K²)`, so that
`∫_θ (Γ/c)² ≤ (7/10 + 3/2)² = 4.84 ≤ 5`.

All the integrability side conditions are automatic: on `Spaces.Iθ = [0,π/2]`
`Gam α θ / c α` and `K θ` are bounded (e.g. `Gam_div_c_bound` in
`Submission/Work/Coercivity/Basic.lean` gives `|Γ/c| ≤ 10` for `0 < α ≤ 1`) and `Iθ` has
finite measure (`instance : IsFiniteMeasure (volume.restrict Spaces.Iθ)` in
`L2CoercivityTransport.lean`).

Here the cross term is handled by the *pointwise* weighted AM–GM inequality
`2(F-G)G ≤ λ(F-G)² + G²/λ` with `λ = 15/7` (`sq_le_two_thirds`) rather than by an
abstract `L²` Cauchy–Schwarz; the numerical constant is the same. -/
theorem GamDivCSqInt_le_five (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΓ : GammaL2Bnd α) :
    ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5 := by
  have hae : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), θ ∈ Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  -- measurability of the three integrands
  have hmeasF : Measurable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) := by
    unfold Spaces.Gam; fun_prop
  have hmeasFG : Measurable (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) := by
    unfold Spaces.Gam Spaces.K; fun_prop
  have hmeasG : Measurable (fun θ : ℝ => (Spaces.K θ) ^ 2) := by
    unfold Spaces.K; fun_prop
  -- a.e. bounds
  have hFbdd' : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      |Spaces.Gam α θ / Spaces.c α| ≤ 10 :=
    hae.mono (fun θ hθ => Gam_div_c_bound hα hα1 hθ)
  have hKbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), |Spaces.K θ| ≤ 3 :=
    hae.mono (fun _ _ => abs_K_le_three)
  have hFbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      ‖(Spaces.Gam α θ / Spaces.c α) ^ 2‖ ≤ 100 := by
    filter_upwards [hFbdd'] with θ h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (Spaces.Gam α θ / Spaces.c α),
      abs_nonneg (Spaces.Gam α θ / Spaces.c α), h]
  have hFGbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      ‖(Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2‖ ≤ 169 := by
    filter_upwards [hFbdd', hKbdd] with θ h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h3 : |Spaces.Gam α θ / Spaces.c α - Spaces.K θ| ≤ 13 := by
      calc |Spaces.Gam α θ / Spaces.c α - Spaces.K θ|
          ≤ |Spaces.Gam α θ / Spaces.c α| + |Spaces.K θ| := abs_sub _ _
        _ ≤ 10 + 3 := by linarith
        _ = 13 := by norm_num
    nlinarith [sq_abs (Spaces.Gam α θ / Spaces.c α - Spaces.K θ),
      abs_nonneg (Spaces.Gam α θ / Spaces.c α - Spaces.K θ), h3]
  have hGbdd : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), ‖(Spaces.K θ) ^ 2‖ ≤ 9 := by
    filter_upwards [hKbdd] with θ h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (Spaces.K θ), abs_nonneg (Spaces.K θ), h]
  -- integrability (bounded functions on a finite measure space)
  have hFsq_int : Integrable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2)
      (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasF.aestronglyMeasurable 100 hFbdd
  have hFGsq_int : Integrable (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasFG.aestronglyMeasurable 169 hFGbdd
  have hGsq_int : Integrable (fun θ : ℝ => (Spaces.K θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    Integrable.of_bound hmeasG.aestronglyMeasurable 9 hGbdd
  -- splitting the integral of the weighted sum
  have hsplit : (∫ θ in Spaces.Iθ, ((22 / 7) * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2
        + (22 / 15) * (Spaces.K θ) ^ 2))
      = (22 / 7) * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2)
        + (22 / 15) * (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) := by
    rw [integral_add (hFGsq_int.const_mul (22 / 7)) (hGsq_int.const_mul (22 / 15)),
      integral_const_mul, integral_const_mul]
  -- the pointwise AM–GM inequality, integrated
  have hmono : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
      ≤ (22 / 7) * (∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2)
        + (22 / 15) * (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) := by
    rw [← hsplit]
    refine integral_mono_ae hFsq_int
      ((hFGsq_int.const_mul (22 / 7)).add (hGsq_int.const_mul (22 / 15)))
      (Eventually.of_forall fun θ => sq_le_two_thirds _ _)
  -- the two hypotheses on the pieces
  have hA : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 ≤ 49 / 100 := by
    have hΓ' : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2
        ≤ ((7 : ℝ) / 10) ^ 2 := hΓ
    have h7 : ((7 : ℝ) / 10) ^ 2 = 49 / 100 := by norm_num
    linarith [hΓ', h7]
  have hB : ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 9 / 4 := integral_Iθ_Ksq_le
  have hAnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hBnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  -- `(22/7) · (49/100) + (22/15) · (9/4) = 121/25 < 5`
  linarith [hmono, hA, hB, hAnn, hBnn]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.projCorr_sepIntegral_le_five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- The `(z,θ)`-separated integral of the projector correction with the sharp angular
bound.  The integrand factorises as `(1/(1+z)²) · (Γ(θ)/c)²`, and both factors are
integrable over the respective restricted measures:
`∫_z 1/(1+z)² = 1` (`integral_Iz_one_div_sq`) with `integrable_Iz_one_div_sq`, and
`(Γ/c)²` is integrable on `Iθ` since `Iθ` has finite measure and `|Γ/c| ≤ 10` pointwise
(`Gam_div_c_bound`).  Hence Fubini (`integral_prod_sep`, for the product of the restricted
measures, which is `volume.restrict (Iz ×ˢ Iθ)` by `volume_restrict_prod`) gives
`∫∫ (Γ(θ)/c)²/(1+z)² = (∫_z 1/(1+z)²)·(∫_θ (Γ/c)²) = ∫_θ (Γ/c)² ≤ 5`.

This is the sharp replacement for the *pointwise* bound `(Γ/c)² ≤ 100` used in
`ProjTransport_sq_integral_le` (`L2CoercivityTransport.lean`); it is the step that turns
the crude constant `2000` into `58` in the projector estimate. -/
theorem projCorr_sepIntegral_le_five (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hG : ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 5) :
    ∫ p : ℝ × ℝ, (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ)) ≤ 5 := by
  have haint : Integrable (fun z : ℝ => 1 / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := integrable_Iz_one_div_sq
  have hbint : Integrable (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) Spaces.Iθ :=
      ((continuousOn_Gam α hα).div_const _).pow 2
    simpa only [Spaces.Iθ, IntegrableOn] using hcont.integrableOn_Icc
  have hcongr : (fun p : ℝ × ℝ =>
        (Spaces.Gam α p.2 / Spaces.c α) ^ 2 / (1 + p.1) ^ 2)
      = fun p : ℝ × ℝ =>
        (1 / (1 + p.1) ^ 2) * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 := by
    funext p; ring
  rw [hcongr,
    integral_prod_sep (fun z : ℝ => 1 / (1 + z) ^ 2)
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α) ^ 2) haint hbint,
    integral_Iz_one_div_sq, one_mul]
  exact hG

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.radial_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Linearity of the iterates of `D_z = z ∂_z` -/



/-! ## Elementary bounds for the weight `z ↦ 1/(1+z)²` -/

theorem rb_inv_sq_le_inv_sq {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : 1 / b ^ 2 ≤ 1 / a ^ 2 := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem rb_continuousOn_inv_one_add_sq (s : Set ℝ) (h : ∀ z ∈ s, 0 < 1 + z) :
    ContinuousOn (fun z : ℝ => 1 / (1 + z) ^ 2) s := by
  refine ContinuousOn.div continuousOn_const
    (((continuousOn_const (c := (1 : ℝ))).add continuousOn_id).pow 2) ?_
  intro z hz
  have hz1 := h z hz
  positivity

theorem rb_integrableOn_inv_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioc (0 : ℝ) 1) :=
  ((rb_continuousOn_inv_one_add_sq (Set.Icc (0 : ℝ) 1) (fun z hz => by linarith [hz.1])).integrableOn_compact
    isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

theorem rb_integral_Ioc_inv_one_add_sq_le :
    ∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2 ≤ 1 := by
  have hle : ∀ z ∈ Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2 ≤ (1 : ℝ) := by
    intro z hz
    have h := rb_inv_sq_le_inv_sq (a := (1 : ℝ)) (b := 1 + z) (by norm_num) (by linarith [hz.1])
    simpa using h
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; simp)
  have hmono : ∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2
      ≤ ∫ z in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hInt1 ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
    exact hle z hz
  have hone : (∫ z in Set.Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by
    rw [MeasureTheory.setIntegral_const]
    simp
  linarith [hmono, hone]

theorem rb_integrableOn_Ioi_inv_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  rw [IntegrableOn] at hbase ⊢
  refine hbase.mono' (((rb_continuousOn_inv_one_add_sq (Set.Ioi (1 : ℝ))
    (fun z hz => by have hz1 : (1 : ℝ) < z := hz; linarith)).aestronglyMeasurable
      measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz1 : (1 : ℝ) < z := hz
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (1 + z) ^ 2)]
  have hrw : z ^ (-(2 : ℝ)) = (z ^ 2)⁻¹ := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0),
      Real.rpow_natCast]
  rw [hrw, inv_eq_one_div]
  exact rb_inv_sq_le_inv_sq hz0 (by linarith)

theorem rb_integral_Ioi_inv_one_add_sq_le :
    ∫ z in Set.Ioi (1 : ℝ), 1 / (1 + z) ^ 2 ≤ 1 := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hle : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))), 1 / (1 + z) ^ 2 ≤ z ^ (-(2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz1 : (1 : ℝ) < z := hz
    have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
    have hrw : z ^ (-(2 : ℝ)) = (z ^ 2)⁻¹ := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0),
        Real.rpow_natCast]
    rw [hrw, inv_eq_one_div]
    exact rb_inv_sq_le_inv_sq hz0 (by linarith)
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hbase hle
  rw [integral_Ioi_rpow_of_lt (a := -(2 : ℝ)) (c := 1) (by norm_num) (by norm_num)] at hmono
  norm_num at hmono
  simpa only [one_div] using hmono

theorem rb_integrableOn_inv_one_add_sq_Iz :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) Spaces.Iz := by
  have h0 : IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact rb_integrableOn_inv_one_add_sq.union rb_integrableOn_Ioi_inv_one_add_sq
  rw [show Spaces.Iz = Set.Ici (0 : ℝ) from rfl, IntegrableOn]
  rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rw [IntegrableOn] at h0
  exact h0

theorem rb_integral_Iz_inv_one_add_sq_le :
    ∫ z in Spaces.Iz, 1 / (1 + z) ^ 2 ≤ 2 := by
  have hIntIoc := rb_integrableOn_inv_one_add_sq
  have hIntIoi := rb_integrableOn_Ioi_inv_one_add_sq
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => (not_le.mpr hz2) hz1.2)
  have hdecomp : ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2
      = (∫ z in Set.Ioc (0 : ℝ) 1, 1 / (1 + z) ^ 2)
        + ∫ z in Set.Ioi (1 : ℝ), 1 / (1 + z) ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIntIoc hIntIoi
  have hIz : (∫ z in Spaces.Iz, 1 / (1 + z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  rw [hIz, hdecomp]
  have h1 := rb_integral_Ioc_inv_one_add_sq_le
  have h2 := rb_integral_Ioi_inv_one_add_sq_le
  linarith


/-! ## The weighted iterates of `Wcoef` -/




/-! ## The product of a radial factor with the coefficient `pcoef` -/






/-! ## The Hardy bound and the integrability of `(L₁₂ g)² w²` -/


/-! ## The core radial estimate for `L₁₂ g` -/



/-! ## The weight identities for `Wt` and the pointwise domination of `D_θ f` -/







/-! ## Integrability of the `D_θ f`-density -/


/-! ## The squared angular moments -/








end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_T2_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary auxiliary facts -/


/-- Almost every `θ ∈ Iθ` lies in the open interval: the two endpoints are null. -/
private theorem ae_Ioo_theta :
    ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (π / 2) → θ ∈ Set.Ioo 0 (π / 2))}
      = ({0} : Set ℝ) ∪ {π / 2} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff,
      not_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases not_and_or.mp h3 with h | h
      · left; exact le_antisymm (not_lt.mp h) h1
      · right; exact le_antisymm h2 (not_lt.mp h)
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl 0, by positivity⟩, by simp⟩
      · exact ⟨⟨by positivity, le_refl _⟩, by simp⟩
  rw [hset]
  exact MeasureTheory.measure_union_null (by rw [Real.volume_singleton])
    (by rw [Real.volume_singleton])


/-- Almost every point of the quadrant has `θ` in the open interval. -/
private theorem ae_prod_mem_univ_Ioo :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
  refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (μ := volume.restrict Spaces.Iz) (ν := volume.restrict Spaces.Iθ)
    (s := Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
    (hs := MeasurableSet.univ.prod measurableSet_Ioo)).mpr ?_
  exact Filter.Eventually.of_forall (fun z =>
    ae_Ioo_theta.mono (fun θ hθ => Set.mem_prod.mpr ⟨Set.mem_univ z, hθ⟩))

/-- Almost every point of the quadrant has `θ` in the open interval. -/
private theorem ae_prod_Ioo :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p.2 ∈ Set.Ioo 0 (π / 2) :=
  ae_prod_mem_univ_Ioo.mono (fun _ hp => (Set.mem_prod.mp hp).2)



/-! ## The tensor Cauchy–Schwarz in `ℝ≥0∞` -/


/-! ## The three factors of the majorant -/



/-! ## A.e. strong measurability of the integrand -/

/-- `(z,θ) ↦ D_θΓ(θ)` is measurable. -/
private theorem measurable_DthGam_prv (α : ℝ) : Measurable (fun θ : ℝ => DthGam α 0 θ) := by
  show Measurable (fun θ : ℝ => Real.sin (2 * θ) * deriv (fun t : ℝ => Spaces.Gam α t) θ)
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul
    (measurable_deriv (fun t : ℝ => Spaces.Gam α t))


/-! ## The pointwise comparison of the integrand with the factorised majorant -/


/-! ## The main estimate -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_T4_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Pointwise algebra -/

/-- Pointwise identity: the integrand of `wip (thetaW α) (T4 α f) (Dth f)` is
`(C0 f / c α)` times `T4W α f`. -/
theorem T4_integrand_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    T4 α f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2
      = (C0 f / Spaces.c α) * T4W α f p := by
  rw [T4, thetaW, T4W, T4g]
  ring

/-- The pointwise Cauchy–Schwarz domination: on the quadrant,
`|T4W α f| ≤ 2α |T4A α · T4B α f|`. -/
theorem T4W_abs_le (α : ℝ) (hα : 0 < α) (hΓ2 : GammaPointwiseBnd α) (f : ℝ → ℝ → ℝ)
    {p : ℝ × ℝ} (hz : p.1 ∈ Spaces.Iz) (hθ : p.2 ∈ Spaces.Iθ) :
    |T4W α f p| ≤ 2 * α * |T4A α p * T4B α f p| := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hΓnn : 0 ≤ Spaces.Gam α p.2 := by
    rw [Spaces.Gam]
    exact Real.rpow_nonneg (mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
      (sq_nonneg _)) _
  have hgnn : 0 ≤ T4g p.1 := T4g_nonneg hz
  have hhnn : 0 ≤ T4h α p.2 := T4h_nonneg α p.2 hsin
  have hwnn : 0 ≤ Spaces.w p.1 := w_nonneg hz
  have hsγ : 0 ≤ (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hsin _
  have hw2 : 0 ≤ (Spaces.w p.1) ^ 2 := sq_nonneg _
  have hDθ : |DthGam α p.1 p.2| ≤ 2 * α * Spaces.Gam α p.2 := by
    rw [DthGam_eq]
    exact hΓ2 p.2 hθ
  have hsq : T4h α p.2 * T4h α p.2 = (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
    rw [← sq, T4h_sq α p.2 hsin]
  have hX : 0 ≤ T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) * (Spaces.w p.1) ^ 2
      * |Spaces.Dth f p.1 p.2| := by positivity
  have hleft : |T4W α f p|
      = |DthGam α p.1 p.2| * (T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
          * (Spaces.w p.1) ^ 2 * |Spaces.Dth f p.1 p.2|) := by
    rw [T4W]
    simp only [abs_mul]
    rw [abs_of_nonneg hgnn, abs_of_nonneg hsγ, abs_of_nonneg hw2]
    ring
  have hr1 : |T4A α p * T4B α f p|
      = Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1
          * (T4h α p.2 * Spaces.w p.1 * |Spaces.Dth f p.1 p.2|) := by
    rw [T4A, T4B]
    simp only [abs_mul]
    rw [abs_of_nonneg hΓnn, abs_of_nonneg hgnn, abs_of_nonneg hhnn, abs_of_nonneg hwnn]
  have hright : |T4A α p * T4B α f p|
      = Spaces.Gam α p.2 * (T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
          * (Spaces.w p.1) ^ 2 * |Spaces.Dth f p.1 p.2|) := by
    rw [hr1, ← hsq]
    ring
  rw [hleft, hright]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDθ hX

/-! ## The two scalar estimates -/

/-- Measurability of the angular integrand. -/
theorem measurable_Gam_sq_sin (α : ℝ) :
    Measurable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
  have h1 : Measurable (fun θ : ℝ => Spaces.Gam α θ) := measurable_Gam α
  have h2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
  have h := (h1.mul h1).mul h2
  convert h using 1
  funext θ
  simp only [Pi.mul_apply]
  rw [pow_two]

/-- **The angular estimate.** `∫_θ Γ(θ)² sin(2θ)^{-γ} ≤ 120/(17α)`, with the integrand
integrable.  Since `Γ²  ≤ sin(2θ)^{2α/3}` (`Gam_sq_le_sin_two`) the integrand is bounded
by `sin(2θ)^{-q}` with `q = 1 - 17α/30`, and `q ∈ (0,1)` for `α ≤ 1`. -/
theorem Gam_sq_sin_neg_gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      Spaces.Iθ ∧
    ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ 120 / (17 * α) := by
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  obtain ⟨hint, hval⟩ := integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hne : 2 * α / 3 + -(Spaces.gam α) ≠ 0 := by
    rw [Spaces.gam]
    intro h
    linarith
  have hpoint : ∀ θ ∈ Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h1 := Gam_sq_le_sin_two α hα θ hθ
    have h2 : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
      rw [← Real.rpow_add' hsin hne]
      congr 1
      rw [Spaces.gam]
      ring
    calc (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hsin _)
      _ = _ := h2
  have hnnpt : ∀ θ ∈ Spaces.Iθ, 0 ≤ (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hnnpt θ hθ
  constructor
  · refine Integrable.mono' hint (measurable_Gam_sq_sin α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnnpt θ hθ)]
    exact hpoint θ hθ
  · have hmono := integral_mono_of_nonneg hnn hint (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpoint θ hθ)
    calc ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := hmono
      _ ≤ 4 / (1 - (1 - 17 * α / 30)) := hval
      _ = 120 / (17 * α) := by
          field_simp
          ring

/-- **The radial estimate.** `∫_z (2z²/(1+z)³)² w(z)² = 4`, with the integrand
integrable: the integrand equals `4/(1+z)²` for `z ≠ 0`, and `∫_0^∞ 4/(1+z)² = 4`. -/
theorem gz_sq_w_sq_integral :
    IntegrableOn (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz ∧
    ∫ z in Spaces.Iz, (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2 = 4 := by
  have hzpos : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    rw [Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Set.Ici (0 : ℝ) → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_Ici, Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨h1, h2⟩
        exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl
        exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  have hae : (fun z : ℝ => (2 * z ^ 2 / (1 + z) ^ 3) ^ 2 * (Spaces.w z) ^ 2)
      =ᵐ[volume.restrict Spaces.Iz] (fun z : ℝ => 4 * (1 / (1 + z) ^ 2)) := by
    filter_upwards [hzpos] with z hz
    rw [Spaces.w]
    field_simp
    ring
  constructor
  · exact (integrable_Iz_one_div_sq.const_mul 4).congr hae.symm
  · rw [integral_congr_ae hae, integral_const_mul, integral_Iz_one_div_sq]
    norm_num

/-! ## Cauchy–Schwarz on the product space -/

/-- Cauchy–Schwarz in the form used below: for two `L²` functions `A, B` (squares
integrable, a.e. strongly measurable), the product is integrable and
`|∫ A·B| ≤ √(∫A²)·√(∫B²)`. -/
theorem integrable_mul_abs_integral_le_sqrt {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (A B : ℝ × ℝ → ℝ)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hA2 : Integrable (fun p => A p ^ 2) μ) (hB2 : Integrable (fun p => B p ^ 2) μ) :
    Integrable (fun p => A p * B p) μ ∧
      |∫ p, A p * B p ∂μ| ≤ Real.sqrt (∫ p, A p ^ 2 ∂μ) * Real.sqrt (∫ p, B p ^ 2 ∂μ) := by
  have hAB : Integrable (fun p => A p * B p) μ := by
    refine Integrable.mono' (g := fun p => (1 / 2) * (A p ^ 2 + B p ^ 2)) ?_
      (hA.mul hB) ?_
    · refine ((hA2.add hB2).const_mul (1 / 2)).congr (Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply]
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : 2 * |A p| * |B p| ≤ A p ^ 2 + B p ^ 2 := by
        have h := two_mul_le_add_sq (|A p|) (|B p|)
        rw [sq_abs, sq_abs] at h
        linarith
      linarith
  refine ⟨hAB, ?_⟩
  have hAmlp : MemLp A 2 μ := (memLp_two_iff_integrable_sq hA).mpr hA2
  have hBmlp : MemLp B 2 μ := (memLp_two_iff_integrable_sq hB).mpr hB2
  have hcs := cs_integral_mul hAmlp hBmlp
  have hAn : 0 ≤ ∫ p, A p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg (A p)
  have hBn : 0 ≤ ∫ p, B p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg (B p)
  have h2 : |∫ p, A p * B p ∂μ| ^ 2 ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) := by
    rw [sq_abs]
    exact hcs
  calc |∫ p, A p * B p ∂μ| = Real.sqrt (|∫ p, A p * B p ∂μ| ^ 2) :=
        (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt ((∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ)) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∫ p, A p ^ 2 ∂μ) * Real.sqrt (∫ p, B p ^ 2 ∂μ) := Real.sqrt_mul hAn _

/-! ## Integrability and values of the two `L²` factors -/

theorem integrable_T4A_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Integrable (fun p : ℝ × ℝ => (T4A α p) ^ 2) T4P := by
  have hz : Integrable (fun z : ℝ => (T4g z) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict Spaces.Iz) := gz_sq_w_sq_integral.1
  have hθ : Integrable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (volume.restrict Spaces.Iθ) := (Gam_sq_sin_neg_gam α hα hα1).1
  refine (hz.mul_prod hθ).congr ?_
  filter_upwards [ae_prod_quadrant] with p hp
  exact (T4A_sq_eq α hp.2).symm

theorem integral_T4A_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ p : ℝ × ℝ, (T4A α p) ^ 2 ∂T4P = 4 * T4J α := by
  have hz : Integrable (fun z : ℝ => (T4g z) ^ 2 * (Spaces.w z) ^ 2)
      (volume.restrict Spaces.Iz) := gz_sq_w_sq_integral.1
  have hθ : Integrable (fun θ : ℝ => (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (volume.restrict Spaces.Iθ) := (Gam_sq_sin_neg_gam α hα hα1).1
  have hpt : (fun p : ℝ × ℝ => (T4A α p) ^ 2) =ᵐ[T4P]
      fun p => ((T4g p.1) ^ 2 * (Spaces.w p.1) ^ 2)
        * ((Spaces.Gam α p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
    filter_upwards [ae_prod_quadrant] with p hp
    exact T4A_sq_eq α hp.2
  have hzval : (∫ z in Spaces.Iz, (T4g z) ^ 2 * (Spaces.w z) ^ 2) = 4 :=
    gz_sq_w_sq_integral.2
  rw [integral_congr_ae hpt,
    show T4P = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) from rfl,
    integral_prod_sep _ _ hz hθ, hzval]
  rw [T4J]



/-! ## A.e. strong measurability and integrability of `T4W` -/





/-! ## The final arithmetic -/


/-! ## The main theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.cs_place_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly


end Work.FTS.CoercivityFix.Assembly

end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The two one-dimensional factors -/

/-- The radial factor `(z/(1+z)³)²` of `A²`. -/
private def cwAz (z : ℝ) : ℝ := (z / (1 + z) ^ 3) ^ 2

/-- The angular factor `(3 K(θ) sin(2θ)^{η/2})²` of `A²`. -/
private def cwAt (θ : ℝ) : ℝ :=
  (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2

private lemma cwAz_eq (z : ℝ) : cwAz z = z ^ 2 / (1 + z) ^ 6 := by
  simp only [cwAz]
  rw [div_pow, ← pow_mul]

/-- The radial factor is integrable on `Iz`, being the integrand of `C0D`. -/
private lemma cwAz_integrable : Integrable cwAz (volume.restrict Work.Spaces.Iz) :=
  Work.Coercivity.integrable_Iz_zsq_div_six.congr
    (Filter.Eventually.of_forall fun z => (cwAz_eq z).symm)

/-- `∫_z (z/(1+z)³)² = 1/30`. -/
private lemma cwAz_integral : ∫ z in Work.Spaces.Iz, cwAz z = 1 / 30 := by
  rw [← Work.Coercivity.integral_Iz_zsq_div_six]
  exact setIntegral_congr_fun measurableSet_Ici (fun z _ => cwAz_eq z)

/-- `∫_z (z/(1+z)³)² ≤ 1/16`. -/
private lemma cwAz_integral_le : ∫ z in Work.Spaces.Iz, cwAz z ≤ 1 / 16 := by
  rw [cwAz_integral]; norm_num

/-- Nonnegativity of the angular factor. -/
private lemma cwAt_nonneg (θ : ℝ) : 0 ≤ cwAt θ := by
  simpa only [cwAt] using
    sq_nonneg (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))

private lemma cwAt_continuous : Continuous cwAt := by
  have hrpow : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).comp (by fun_prop)
  have hK : Continuous fun θ : ℝ => 3 * Work.Spaces.K θ := by
    rw [show (fun θ : ℝ => 3 * Work.Spaces.K θ)
        = fun θ : ℝ => 3 * (3 * Real.sin θ * Real.cos θ ^ 2) from rfl]
    fun_prop
  exact (hK.mul hrpow).pow 2

/-- The angular factor is integrable on the interval `Iθ`. -/
private lemma cwAt_integrable : Integrable cwAt (volume.restrict Work.Spaces.Iθ) :=
  cwAt_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- On `Iθ` the angular factor is bounded by `81`: indeed `|3 K(θ)| ≤ 9` and
`sin(2θ)^{η/2} ∈ [0,1]` there. -/
private lemma cwAt_le_eighty_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : cwAt θ ≤ 81 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsinθ0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, hπ]⟩
  have hsinθ1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hcos0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, hπ]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_nonneg hs0 _
  have hr1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := Real.rpow_le_one hs0 hs1 hη
  have hKabs : |3 * Work.Spaces.K θ| ≤ 9 := by
    have hKnn : 0 ≤ 3 * Work.Spaces.K θ := by
      rw [Work.Spaces.K]; nlinarith [hsinθ0, hcos0]
    rw [abs_of_nonneg hKnn, Work.Spaces.K]
    nlinarith [hsinθ0, hsinθ1, hcos0, hcos2]
  have hbound : |3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 9 := by
    rw [abs_mul]
    calc |3 * Work.Spaces.K θ| * |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)|
        ≤ 9 * 1 := mul_le_mul hKabs (by rw [abs_of_nonneg hr0]; exact hr1)
          (abs_nonneg _) (by norm_num)
      _ = 9 := by norm_num
  have hx9 := abs_le.mp hbound
  have hsq : (3 * Work.Spaces.K θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (9 : ℝ) ^ 2 := sq_le_sq' hx9.1 hx9.2
  norm_num at hsq
  simpa only [cwAt] using hsq

/-- `∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`. -/
private lemma cwAt_integral_le : ∫ θ in Work.Spaces.Iθ, cwAt θ ≤ 162 := by
  have hmono := setIntegral_mono_on (f := cwAt) (g := fun _ : ℝ => (81 : ℝ))
      cwAt_integrable (integrable_const 81) measurableSet_Icc
      (fun θ hθ => cwAt_le_eighty_one hθ)
  calc ∫ θ in Work.Spaces.Iθ, cwAt θ
      ≤ ∫ θ in Work.Spaces.Iθ, (81 : ℝ) := hmono
    _ = volume.real Work.Spaces.Iθ * 81 := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ 2 * 81 := mul_le_mul_of_nonneg_right Work.Coercivity.volumeReal_Iθ_le_two (by norm_num)
    _ = 162 := by norm_num

/-! ## The product bound -/

theorem A_sq_prod_le :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    ∫ p, (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ 16 := by
  -- `A²` factors into its radial and angular parts.
  have hfactor : ∀ z θ : ℝ,
      (3 * Work.Spaces.K θ * (z / (1 + z) ^ 3) * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = cwAz z * cwAt θ := by
    intro z θ
    simp only [cwAz, cwAt]
    ring
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
        * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (cwAz_integrable.mul_prod cwAt_integrable).congr
      (Filter.Eventually.of_forall fun p => (hfactor p.1 p.2).symm)
  refine ⟨hInt, ?_⟩
  calc ∫ p, (3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
          * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = ∫ p, cwAz p.1 * cwAt p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun p => hfactor p.1 p.2)
    _ = (∫ z in Work.Spaces.Iz, cwAz z) * (∫ θ in Work.Spaces.Iθ, cwAt θ) :=
        Work.Coercivity.integral_prod_sep cwAz cwAt cwAz_integrable cwAt_integrable
    _ ≤ (1 / 16) * 162 :=
        mul_le_mul cwAz_integral_le cwAt_integral_le
          (setIntegral_nonneg (s := Set.Icc 0 (π / 2)) (μ := volume) measurableSet_Icc
            (fun θ _ => cwAt_nonneg θ))
          (by norm_num)
    _ ≤ 16 := by norm_num

end

end Work.FTS.CoercivityFix.Transfer.E2norm
end
