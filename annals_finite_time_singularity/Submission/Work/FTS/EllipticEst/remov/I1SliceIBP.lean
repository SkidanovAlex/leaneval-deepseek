/-
Work module for the Elgindi finite-time singularity project (area: `FTS/EllipticEst/remov`).

# The angular integration by parts on a single `θ`-slice (`slice_ibp_sigma_fts`)

This is the *buildable* home of the lemmas needed by
`Submission/Work/FTS/EllipticEst/remov/I1_weighted_bound.lean`.  The statement
`slice_ibp_sigma_fts` is a verbatim copy (same name modulo namespace) of
`Work.FTS.EllipticEst.AngSecond.slice_ibp_sigma`, whose proof skeleton lives in
`Submission/Work/FTS/EllipticEst/AngSecond/slice_ibp_sigma.lean` and whose only missing
ingredients were the three helper lemmas `sigD_hasDerivAt`, `slice_boundary_tendsto` and
`slice_integrands_integrable`.  Those three are proved here (under our own names, so that no
other agent's file is touched), and the proof of `slice_ibp_sigma` is reproduced verbatim
against them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs
import Submission.Work.FTS.EllipticEst.AngSecond.sigE_hasDerivAt
import Submission.Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds
import Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sin_rpow_le_majorant_pi
import Submission.Work.FTS.H2.STBounds2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The angular weight `σ θ = sin(2θ)^{-η}` (a copy of `AngSecond.sigE`). -/
abbrev sigE := Work.FTS.EllipticEst.AngSecond.sigE

/-- `σ'` (a copy of `AngSecond.sigD`). -/
abbrev sigD := Work.FTS.EllipticEst.AngSecond.sigD

/-- `σ''` (a copy of `AngSecond.sigDD`). -/
abbrev sigDD := Work.FTS.EllipticEst.AngSecond.sigDD

/-- `cos(2θ)` (a copy of `AngSecond.c2`). -/
abbrev c2 := Work.FTS.EllipticEst.AngSecond.c2

/-! ## 1. The majorant `(π/4)^p (θ^{-p} + (π/2-θ)^{-p})` -/

/-- The majorant of `sin(2θ)^{-p}` is integrable on `Iθ` for `0 ≤ p < 1`. -/
theorem integrableOn_majorant_fts (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IntegrableOn (fun θ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      (Set.Icc 0 (Real.pi / 2)) := by
  rcases eq_or_lt_of_le hp0 with h | h
  · subst h
    have hfun : (fun θ : ℝ => (Real.pi / 4) ^ (0 : ℝ)
        * (θ ^ (-(0 : ℝ)) + (Real.pi / 2 - θ) ^ (-(0 : ℝ)))) = fun _ => (2 : ℝ) := by
      funext θ
      norm_num
    rw [hfun]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · exact Work.Spaces.integrableOn_majorant_rpow p h hp1

/-- The pointwise majorant of `sin(2θ)^{-η}` for `0 ≤ η`. -/
theorem sin_rpow_le_majorant_fts (η : ℝ) (hη0 : 0 ≤ η) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  rcases eq_or_lt_of_le hη0 with h | h
  · subst h
    simp [Real.rpow_zero]
  · exact Work.Spaces.sin_rpow_le_majorant_pi η θ h hθ

/-! ## 2. The derivative of `σ'` -/

theorem sigD_hasDerivAt_fts (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => sigD η t) (sigDD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := hlin.cos
  have hpow : HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(1 + η)))
      ((Real.cos (2 * θ) * 2) * (-(1 + η)) * Real.sin (2 * θ) ^ (-(1 + η) - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hspos))
  have hprod := (hcos.mul hpow).const_mul (-2 * η)
  have hfun : (fun t => sigD η t)
      = fun y => -2 * η * (((fun t => Real.cos (2 * t))
          * fun t => Real.sin (2 * t) ^ (-(1 + η))) y) := by
    funext y
    simp only [Pi.mul_apply, Work.FTS.EllipticEst.AngSecond.sigD_apply]
    ring
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [Work.FTS.EllipticEst.AngSecond.sigDD_apply,
    Work.FTS.EllipticEst.AngSecond.sigE_apply]
  have h2 : Real.sin (2 * θ) ^ (-(1 + η) - 1) = Real.sin (2 * θ) ^ (-(2 + η)) := by
    congr 1
    ring
  have h1 : Real.sin (2 * θ) ^ (-(1 + η))
      = Real.sin (2 * θ) ^ (-η) / Real.sin (2 * θ) := by
    rw [eq_div_iff hspos.ne', ← Real.rpow_add_one hspos.ne']
    congr 1
    ring
  rw [h1, h2]
  field_simp
  ring

/-! ## 3. The endpoint limits of the two antiderivatives -/


/-- A one-sided squeeze: an eventually nonnegative function dominated eventually by a function
tending to `0` tends to `0`. -/
theorem tendsto_zero_of_eventually_le {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, 0 ≤ f t) (hfg : ∀ᶠ t in l, f t ≤ g t) (hg : Tendsto g l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hf] with t ht
    linarith
  · have h := (tendsto_order.mp hg).2 b hb
    filter_upwards [h, hfg] with t ht hle
    linarith

/-- The two endpoint limits of the antiderivatives `f·f'·σ` and `f²·σ'`. -/
theorem slice_boundary_tendsto_fts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    Tendsto (fun θ => f θ * deriv f θ * sigE η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ * deriv f θ * sigE η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨C, hC0, hd1, hd2, hb0, hbpi⟩ :=
    Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds f hf h0 h1
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  have h4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hη1' : (0 : ℝ) < 1 - η := by linarith
  -- the two relevant one-sided neighbourhoods of the endpoints
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT h4]
    exact self_mem_nhdsWithin
  have hmemπ : Set.Ioo (Real.pi / 4) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    have h : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
        = nhdsWithin (Real.pi / 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (nhdsWithin_Ioo_eq_nhdsLT (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2)).symm
    rw [h]
    exact self_mem_nhdsWithin
  -- elementary limits
  have hl1 : Tendsto (fun θ : ℝ => θ ^ (1 - η)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun θ : ℝ => θ ^ (1 - η)) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ (1 - η))) := by
      simpa only [id_eq] using
        (continuous_id.tendsto (0 : ℝ)).rpow tendsto_const_nhds (Or.inr hη1')
    rw [Real.zero_rpow (ne_of_gt hη1')] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hl2 : Tendsto (fun θ : ℝ => θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hl3 : Tendsto (fun θ : ℝ => θ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using ((continuous_id.tendsto (0 : ℝ)).pow 2).mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2)) (nhds 0) := by
    have h1 : Continuous fun θ : ℝ => Real.pi / 2 - θ := by fun_prop
    simpa using h1.tendsto (Real.pi / 2)
  have hm1 : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - η))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - η)) (nhds (Real.pi / 2))
        (nhds ((0 : ℝ) ^ (1 - η))) := hsub.rpow tendsto_const_nhds (Or.inr hη1')
    rw [Real.zero_rpow (ne_of_gt hη1')] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm2 : Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    hsub.mono_left nhdsWithin_le_nhds
  have hm3 : Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using (hsub.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))).pow 2
  -- `|σ|` bound near `0`
  have hsigE_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi / 4) ^ η * θ ^ (-η) + 1 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have h2 : (Real.pi / 2 - θ) ^ (-η) ≤ (Real.pi / 4) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos h4 (by linarith [hθ.2]) (by linarith : -η ≤ 0)
    have h3 : (Real.pi / 4) ^ η * (Real.pi / 4) ^ (-η) = 1 := by
      rw [← Real.rpow_add h4, add_neg_cancel, Real.rpow_zero]
    calc (Real.sin (2 * θ)) ^ (-η)
        ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          sin_rpow_le_majorant_fts η hη0 hθ'
      _ ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 4) ^ (-η)) := by
          have h5 : (0 : ℝ) ≤ (Real.pi / 4) ^ η := Real.rpow_nonneg (le_of_lt h4) _
          have h6 : θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)
              ≤ θ ^ (-η) + (Real.pi / 4) ^ (-η) := by linarith
          exact mul_le_mul_of_nonneg_left h6 h5
      _ = (Real.pi / 4) ^ η * θ ^ (-η) + 1 := by rw [mul_add, h3]
  -- `|σ|` bound near `π/2`
  have hsigE_le' : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (-η) + 1 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
    have h2 : θ ^ (-η) ≤ (Real.pi / 4) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos h4 (by linarith [hθ.1]) (by linarith : -η ≤ 0)
    have h3 : (Real.pi / 4) ^ η * (Real.pi / 4) ^ (-η) = 1 := by
      rw [← Real.rpow_add h4, add_neg_cancel, Real.rpow_zero]
    calc (Real.sin (2 * θ)) ^ (-η)
        ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          sin_rpow_le_majorant_fts η hη0 hθ'
      _ ≤ (Real.pi / 4) ^ η * ((Real.pi / 4) ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
          have h5 : (0 : ℝ) ≤ (Real.pi / 4) ^ η := Real.rpow_nonneg (le_of_lt h4) _
          have h6 : θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)
              ≤ (Real.pi / 4) ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by linarith
          exact mul_le_mul_of_nonneg_left h6 h5
      _ = (Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (-η) + 1 := by rw [mul_add, h3, add_comm]
  -- `|σ'|` bound near `0`
  have hsigD_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |sigD η θ| ≤ 2 * η * ((Real.pi / 4) ^ (1 + η) * θ ^ (-(1 + η)) + 1) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hθ' : θ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hmaj := Work.Spaces.sin_rpow_le_majorant_pi (1 + η) θ (by positivity) hθ'
    have h2 : (Real.pi / 2 - θ) ^ (-(1 + η)) ≤ (Real.pi / 4) ^ (-(1 + η)) :=
      Real.rpow_le_rpow_of_nonpos h4 (by linarith [hθ.2]) (by linarith : -(1 + η) ≤ 0)
    have h3 : (Real.pi / 4) ^ (1 + η) * (Real.pi / 4) ^ (-(1 + η)) = 1 := by
      rw [← Real.rpow_add h4, add_neg_cancel, Real.rpow_zero]
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    simp only [Work.FTS.EllipticEst.AngSecond.sigD_apply, abs_mul]
    rw [show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg hη0,
      abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
    have hstep : (2 * η * |Real.cos (2 * θ)|) * Real.sin (2 * θ) ^ (-(1 + η))
        ≤ (2 * η * 1) * ((Real.pi / 4) ^ (1 + η)
            * (θ ^ (-(1 + η)) + (Real.pi / 2 - θ) ^ (-(1 + η)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hcos (by positivity)) hmaj
        (Real.rpow_nonneg hspos.le _) (by positivity)
    refine le_trans hstep ?_
    have h6 : (Real.pi / 4) ^ (1 + η) * (θ ^ (-(1 + η)) + (Real.pi / 2 - θ) ^ (-(1 + η)))
        ≤ (Real.pi / 4) ^ (1 + η) * (θ ^ (-(1 + η)) + (Real.pi / 4) ^ (-(1 + η))) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt h4) _)
      linarith
    refine le_trans (mul_le_mul_of_nonneg_left h6 (by positivity)) ?_
    have hX : (Real.pi / 4) ^ (1 + η) * (θ ^ (-(1 + η)) + (Real.pi / 4) ^ (-(1 + η)))
        = (Real.pi / 4) ^ (1 + η) * θ ^ (-(1 + η)) + 1 := by rw [mul_add, h3]
    rw [hX]
    exact le_of_eq (by ring)
  -- `|σ'|` bound near `π/2`
  have hsigD_le' : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |sigD η θ| ≤ 2 * η * ((Real.pi / 4) ^ (1 + η) * (Real.pi / 2 - θ) ^ (-(1 + η)) + 1) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hθ' : θ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
    have hmaj := Work.Spaces.sin_rpow_le_majorant_pi (1 + η) θ (by positivity) hθ'
    have h2 : θ ^ (-(1 + η)) ≤ (Real.pi / 4) ^ (-(1 + η)) :=
      Real.rpow_le_rpow_of_nonpos h4 (by linarith [hθ.1]) (by linarith : -(1 + η) ≤ 0)
    have h3 : (Real.pi / 4) ^ (1 + η) * (Real.pi / 4) ^ (-(1 + η)) = 1 := by
      rw [← Real.rpow_add h4, add_neg_cancel, Real.rpow_zero]
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    simp only [Work.FTS.EllipticEst.AngSecond.sigD_apply, abs_mul]
    rw [show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg hη0,
      abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
    have hstep : (2 * η * |Real.cos (2 * θ)|) * Real.sin (2 * θ) ^ (-(1 + η))
        ≤ (2 * η * 1) * ((Real.pi / 4) ^ (1 + η)
            * (θ ^ (-(1 + η)) + (Real.pi / 2 - θ) ^ (-(1 + η)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hcos (by positivity)) hmaj
        (Real.rpow_nonneg hspos.le _) (by positivity)
    refine le_trans hstep ?_
    have h6 : (Real.pi / 4) ^ (1 + η) * (θ ^ (-(1 + η)) + (Real.pi / 2 - θ) ^ (-(1 + η)))
        ≤ (Real.pi / 4) ^ (1 + η) * ((Real.pi / 4) ^ (-(1 + η))
            + (Real.pi / 2 - θ) ^ (-(1 + η))) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt h4) _)
      linarith
    refine le_trans (mul_le_mul_of_nonneg_left h6 (by positivity)) ?_
    have hX : (Real.pi / 4) ^ (1 + η) * ((Real.pi / 4) ^ (-(1 + η))
          + (Real.pi / 2 - θ) ^ (-(1 + η)))
        = (Real.pi / 4) ^ (1 + η) * (Real.pi / 2 - θ) ^ (-(1 + η)) + 1 := by
      rw [mul_add, h3, add_comm]
    rw [hX]
    exact le_of_eq (by ring)
  -- the `f`-bound
  have hFmin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ C * min θ (Real.pi / 2 - θ) := by
    intro θ hθ
    have hI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]; exact hb0 θ hI
    · rw [min_eq_right h]; exact hbpi θ hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `f·f'·σ → 0` at `0⁺`
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ =>
      C ^ 2 * (Real.pi / 4) ^ η * θ ^ (1 - η) + C ^ 2 * θ)
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hI : θ ∈ Work.Spaces.Iθ :=
        ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hspos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hsige : sigE η θ = (Real.sin (2 * θ)) ^ (-η) := rfl
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hsige,
        abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
      have hfd : |deriv f θ| ≤ C := hd1 θ hθIoo
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθIoo
      have hmin : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
      have hfm' : |f θ| ≤ C * θ := le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hs := hsigE_le θ hθ
      have hR : (0 : ℝ) ≤ (Real.pi / 4) ^ η * θ ^ (-η) + 1 :=
        add_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt h4) _)
          (Real.rpow_nonneg (le_of_lt hθ.1) _)) zero_le_one
      calc |f θ| * |deriv f θ| * Real.sin (2 * θ) ^ (-η)
          ≤ (C * θ) * C * ((Real.pi / 4) ^ η * θ ^ (-η) + 1) := by
            refine mul_le_mul (mul_le_mul hfm' hfd (abs_nonneg _)
              (mul_nonneg hC0 (le_of_lt hθ.1))) hs (Real.rpow_nonneg hspos.le _)
              (mul_nonneg (mul_nonneg hC0 (le_of_lt hθ.1)) hC0)
        _ = C ^ 2 * (Real.pi / 4) ^ η * θ ^ (1 - η) + C ^ 2 * θ := by
            have hp : θ ^ (1 - η) = θ ^ (-η) * θ := by
              rw [← Real.rpow_add_one (ne_of_gt hθ.1) (-η)]
              congr 1
              ring
            rw [hp]
            ring
    · have h := (hl1.const_mul (C ^ 2 * (Real.pi / 4) ^ η)).add (hl2.const_mul (C ^ 2))
      simpa using h
  · -- `f·f'·σ → 0` at `(π/2)⁻`
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ =>
      C ^ 2 * (Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (1 - η) + C ^ 2 * (Real.pi / 2 - θ))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hI : θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hspos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
      have hsige : sigE η θ = (Real.sin (2 * θ)) ^ (-η) := rfl
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hsige,
        abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
      have hfd : |deriv f θ| ≤ C := hd1 θ hθIoo
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθIoo
      have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
      have hfm' : |f θ| ≤ C * (Real.pi / 2 - θ) :=
        le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hs := hsigE_le' θ hθ
      have hR : (0 : ℝ) ≤ (Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (-η) + 1 :=
        add_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt h4) _)
          (Real.rpow_nonneg (by linarith [hθ.2]) _)) zero_le_one
      calc |f θ| * |deriv f θ| * Real.sin (2 * θ) ^ (-η)
          ≤ (C * (Real.pi / 2 - θ)) * C
              * ((Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (-η) + 1) := by
            refine mul_le_mul (mul_le_mul hfm' hfd (abs_nonneg _)
              (mul_nonneg hC0 (by linarith [hθ.2]))) hs
              (Real.rpow_nonneg hspos.le _) (mul_nonneg (mul_nonneg hC0 (by linarith [hθ.2])) hC0)
        _ = C ^ 2 * (Real.pi / 4) ^ η * (Real.pi / 2 - θ) ^ (1 - η)
              + C ^ 2 * (Real.pi / 2 - θ) := by
            have hp : (Real.pi / 2 - θ) ^ (1 - η)
                = (Real.pi / 2 - θ) ^ (-η) * (Real.pi / 2 - θ) := by
              rw [← Real.rpow_add_one (by linarith [hθ.2]) (-η)]
              congr 1
              ring
            rw [hp]
            ring
    · have h := (hm1.const_mul (C ^ 2 * (Real.pi / 4) ^ η)).add (hm2.const_mul (C ^ 2))
      simpa using h
  · -- `f²·σ' → 0` at `0⁺`
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ =>
      2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η) * θ ^ (1 - η) + 2 * η * C ^ 2 * θ ^ 2)
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hI : θ ∈ Work.Spaces.Iθ :=
        ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθIoo
      have hmin : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
      have hfm' : |f θ| ≤ C * θ := le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hf2 : f θ ^ 2 ≤ (C * θ) ^ 2 := by
        nlinarith [abs_nonneg (f θ), sq_abs (f θ), hfm', hC0, hθ.1]
      have hsd := hsigD_le θ hθ
      have hR : (0 : ℝ) ≤ 2 * η * ((Real.pi / 4) ^ (1 + η) * θ ^ (-(1 + η)) + 1) :=
        mul_nonneg (by positivity) (add_nonneg (mul_nonneg
          (Real.rpow_nonneg (le_of_lt h4) _) (Real.rpow_nonneg (le_of_lt hθ.1) _)) zero_le_one)
      calc f θ ^ 2 * |sigD η θ|
          ≤ (C * θ) ^ 2 * (2 * η * ((Real.pi / 4) ^ (1 + η) * θ ^ (-(1 + η)) + 1)) := by
            refine mul_le_mul hf2 hsd (abs_nonneg _) (sq_nonneg _)
        _ = 2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η) * θ ^ (1 - η) + 2 * η * C ^ 2 * θ ^ 2 := by
            have hp : θ ^ (1 - η) = θ ^ (-(1 + η)) * θ ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hθ.1]
              congr 1
              ring
            rw [hp]
            ring
    · have h := (hl1.const_mul (2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η))).add
          (hl3.const_mul (2 * η * C ^ 2))
      simpa using h
  · -- `f²·σ' → 0` at `(π/2)⁻`
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ =>
      2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η) * (Real.pi / 2 - θ) ^ (1 - η)
        + 2 * η * C ^ 2 * (Real.pi / 2 - θ) ^ 2)
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hI : θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθIoo
      have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
      have hfm' : |f θ| ≤ C * (Real.pi / 2 - θ) :=
        le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hf2 : f θ ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := by
        nlinarith [abs_nonneg (f θ), sq_abs (f θ), hfm', hC0, hθ.2, Real.pi_pos]
      have hsd := hsigD_le' θ hθ
      have hR : (0 : ℝ) ≤ 2 * η * ((Real.pi / 4) ^ (1 + η)
          * (Real.pi / 2 - θ) ^ (-(1 + η)) + 1) :=
        mul_nonneg (by positivity) (add_nonneg (mul_nonneg
          (Real.rpow_nonneg (le_of_lt h4) _) (Real.rpow_nonneg (by linarith [hθ.2]) _))
          zero_le_one)
      calc f θ ^ 2 * |sigD η θ|
          ≤ (C * (Real.pi / 2 - θ)) ^ 2
              * (2 * η * ((Real.pi / 4) ^ (1 + η) * (Real.pi / 2 - θ) ^ (-(1 + η)) + 1)) := by
            refine mul_le_mul hf2 hsd (abs_nonneg _) (sq_nonneg _)
        _ = 2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η) * (Real.pi / 2 - θ) ^ (1 - η)
              + 2 * η * C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
            have hp : (Real.pi / 2 - θ) ^ (1 - η)
                = (Real.pi / 2 - θ) ^ (-(1 + η)) * (Real.pi / 2 - θ) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith [hθ.2])]
              congr 1
              ring
            rw [hp]
            ring
    · have h := (hm1.const_mul (2 * η * C ^ 2 * (Real.pi / 4) ^ (1 + η))).add
          (hm3.const_mul (2 * η * C ^ 2))
      simpa using h



/-- **Integrability of the five pieces of the angular integration by parts.** -/
theorem slice_integrands_integrable_fts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    IntegrableOn (fun θ => deriv f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)))
          Work.Spaces.Iθ := by
  obtain ⟨C, hC0, hd1, hd2, hb0, hbpi⟩ :=
    Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds f hf h0 h1
  have h4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hIoo : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → θ ∈ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hsig_int : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-η) (by linarith) (by linarith)).1
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hres : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hsig_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsinD_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 + η)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsin2_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hf_aesm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hf.continuousOn.mono fun θ hθ => hIoo θ hθ).aestronglyMeasurable measurableSet_Ioo
  have hfd_aesm : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv f).aestronglyMeasurable
  have hfdd_aesm : AEStronglyMeasurable (deriv (deriv f))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv (deriv f)).aestronglyMeasurable
  have hsinD_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 + η)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsigD_aesm : AEStronglyMeasurable (fun θ : ℝ => sigD η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change AEStronglyMeasurable (fun θ : ℝ =>
      -2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))) _
    have hcos_cont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_cos.comp (show Continuous fun θ : ℝ => (2 : ℝ) * θ from
        continuous_const.mul continuous_id)).continuousOn
    have hmain : AEStronglyMeasurable (fun θ : ℝ => -2 * η * (Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + η)))) (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((hcos_cont.mul hsinD_cont).const_mul (-2 * η)).aestronglyMeasurable measurableSet_Ioo
    simpa only [mul_assoc] using hmain
  have hsig_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsig_cont.aestronglyMeasurable measurableSet_Ioo
  have hsinD_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsinD_cont.aestronglyMeasurable measurableSet_Ioo
  have hsin2_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsin2_cont.aestronglyMeasurable measurableSet_Ioo
  have hcos2_aesm : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
      ).aestronglyMeasurable measurableSet_Ioo
  have hFmin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ C * min θ (Real.pi / 2 - θ) := by
    intro θ hθ
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]; exact hb0 θ (hIoo θ hθ)
    · rw [min_eq_right h]; exact hbpi θ (hIoo θ hθ)
  have hsigD_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |-2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))|
        ≤ 2 * η * (Real.sin (2 * θ)) ^ (-(1 + η)) := by
    intro θ hθ
    have hspos := hsin_pos θ hθ
    simp only [abs_mul]
    rw [show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg hη0,
      abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
    have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2η : (0 : ℝ) ≤ 2 * η := by positivity
    calc 2 * η * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η))
        ≤ 2 * η * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc h2η)
            (Real.rpow_nonneg hspos.le _)
      _ = 2 * η * (Real.sin (2 * θ)) ^ (-(1 + η)) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `(f')² σ`
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.mono_set Set.Ioo_subset_Icc_self |>.const_mul (C ^ 2)) ?_ ?_
    · exact (hfd_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      simp only [Work.FTS.EllipticEst.AngSecond.sigE_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)),
        abs_of_nonneg (Real.rpow_nonneg (hsin_pos θ hθ).le _)]
      have hfd : |deriv f θ| ≤ C := hd1 θ hθ
      have h1 : deriv f θ ^ 2 ≤ C ^ 2 :=
        calc deriv f θ ^ 2 = |deriv f θ| ^ 2 := (sq_abs (deriv f θ)).symm
          _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfd 2
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hsin_pos θ hθ).le _)
  · -- `f f'' σ`
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.mono_set Set.Ioo_subset_Icc_self |>.const_mul (C ^ 2 * (Real.pi / 2))) ?_ ?_
    · exact (hf_aesm.mul hfdd_aesm).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      simp only [Work.FTS.EllipticEst.AngSecond.sigE_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (hsin_pos θ hθ).le _)]
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθ
      have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 := by
        have := min_le_left θ (Real.pi / 2 - θ); linarith [hθ.2]
      have hfm' : |f θ| ≤ C * (Real.pi / 2) := le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hfd : |deriv (deriv f) θ| ≤ C := hd2 θ hθ
      have h1 : |f θ| * |deriv (deriv f) θ| ≤ C ^ 2 * (Real.pi / 2) := by
        calc |f θ| * |deriv (deriv f) θ| ≤ (C * (Real.pi / 2)) * C :=
              mul_le_mul hfm' hfd (abs_nonneg _) (mul_nonneg hC0 (by positivity))
          _ = C ^ 2 * (Real.pi / 2) := by ring
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hsin_pos θ hθ).le _)
  · -- `f f' σ'`
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.mono_set Set.Ioo_subset_Icc_self |>.const_mul (2 * η * C ^ 2 * (Real.pi / 4))) ?_ ?_
    · exact (hf_aesm.mul hfd_aesm).mul hsigD_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      simp only [Work.FTS.EllipticEst.AngSecond.sigD_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        show |(-2 * η : ℝ)| = 2 * η by rw [abs_of_nonpos (by nlinarith [hη0])]; ring,
        abs_of_nonneg (Real.rpow_nonneg (hsin_pos θ hθ).le _)]
      have hspos := hsin_pos θ hθ
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθ
      have hmin := Work.FTS.H2.min_le_sin θ (hIoo θ hθ)
      have hfm' : |f θ| ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) :=
        le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hfd : |deriv f θ| ≤ C := hd1 θ hθ
      have hsd := hsigD_le θ hθ
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : |f θ| * |deriv f θ| * (2 * η * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η)))
          ≤ 2 * η * C ^ 2 * (Real.pi / 4) * (Real.sin (2 * θ)) ^ (-η) := by
        have h2 : |f θ| * |deriv f θ| ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) * C :=
          mul_le_mul hfm' hfd (abs_nonneg _) (mul_nonneg hC0 (by positivity))
        have h3 : (Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(1 + η))
            = (Real.sin (2 * θ)) ^ (-η) := by
          rw [mul_comm, ← Real.rpow_add_one hspos.ne' (-(1 + η))]
          congr 1
          ring
        have h2η : (0 : ℝ) ≤ 2 * η := by positivity
        calc |f θ| * |deriv f θ| * (2 * η * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η)))
            ≤ (C * ((Real.pi / 4) * Real.sin (2 * θ)) * C)
                * (2 * η * 1 * (Real.sin (2 * θ)) ^ (-(1 + η))) := by
              have hcosb : 2 * η * |Real.cos (2 * θ)| ≤ 2 * η * 1 :=
                mul_le_mul_of_nonneg_left hcos h2η
              refine mul_le_mul h2
                (mul_le_mul_of_nonneg_right hcosb (Real.rpow_nonneg hspos.le _))
                (mul_nonneg (mul_nonneg h2η (abs_nonneg _)) (Real.rpow_nonneg hspos.le _))
                (mul_nonneg (mul_nonneg hC0 (by positivity)) hC0)
          _ = 2 * η * C ^ 2 * (Real.pi / 4) * (Real.sin (2 * θ)) ^ (-η) := by
              rw [← h3]
              ring
      exact h1
  · -- `f² σ`
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.mono_set Set.Ioo_subset_Icc_self |>.const_mul (C ^ 2 * (Real.pi / 2) ^ 2)) ?_ ?_
    · exact (hf_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      simp only [Work.FTS.EllipticEst.AngSecond.sigE_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
        abs_of_nonneg (Real.rpow_nonneg (hsin_pos θ hθ).le _)]
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθ
      have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 := by
        have := min_le_left θ (Real.pi / 2 - θ); linarith [hθ.2]
      have hfm' : |f θ| ≤ C * (Real.pi / 2) := le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have h1 : f θ ^ 2 ≤ C ^ 2 * (Real.pi / 2) ^ 2 := by
        have h2 : |f θ| ≤ C * (Real.pi / 2) := hfm'
        nlinarith [abs_nonneg (f θ), sq_abs (f θ), h2, hC0]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hsin_pos θ hθ).le _)
  · -- `f² cos²(2θ) σ''`
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.mono_set Set.Ioo_subset_Icc_self |>.const_mul (C ^ 2 * (Real.pi / 4) ^ 2)) ?_ ?_
    · exact ((hf_aesm.pow 2).mul hcos2_aesm).mul hsin2_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      have hc : Real.cos (2 * θ) ^ 2 ≤ 1 := by
        have h := Real.abs_cos_le_one (2 * θ)
        nlinarith [abs_nonneg (Real.cos (2 * θ)), sq_abs (Real.cos (2 * θ)), h]
      have hfm : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hFmin θ hθ
      have hmin := Work.FTS.H2.min_le_sin θ (hIoo θ hθ)
      have hfm' : |f θ| ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) :=
        le_trans hfm (mul_le_mul_of_nonneg_left hmin hC0)
      have hmn : (0 : ℝ) ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
      simp only [Work.FTS.EllipticEst.AngSecond.c2_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
        abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))),
        abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
      have h1 : f θ ^ 2 * Real.cos (2 * θ) ^ 2
          ≤ (C * ((Real.pi / 4) * Real.sin (2 * θ))) ^ 2 := by
        have h2 : f θ ^ 2 ≤ (C * ((Real.pi / 4) * Real.sin (2 * θ))) ^ 2 := by
          have h3 : |f θ| ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) := hfm'
          calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs (f θ)).symm
            _ ≤ (C * ((Real.pi / 4) * Real.sin (2 * θ))) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) h3 2
        calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 ≤ f θ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hc (sq_nonneg _)
          _ = f θ ^ 2 := mul_one _
          _ ≤ _ := h2
      have h3 : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
          = (Real.sin (2 * θ)) ^ (-η) := by
        have h4' : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
          (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
        rw [h4', ← Real.rpow_add hspos]
        congr 1
        ring
      calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
          ≤ (C * ((Real.pi / 4) * Real.sin (2 * θ))) ^ 2
              * (Real.sin (2 * θ)) ^ (-(2 + η)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hspos.le _)
        _ = C ^ 2 * (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
            rw [← h3]
            ring

theorem slice_ibp_sigma_fts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
  suffices key : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * c2 θ ^ 2
            * Real.sin (2 * θ) ^ (-(2 + η))) by
    simpa only [Work.FTS.EllipticEst.AngSecond.sigE_apply, Work.FTS.EllipticEst.AngSecond.c2_apply] using key
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hI1, hI2, hI3, hI4, hI5⟩ := slice_integrands_integrable_fts η hη0 hη1 f hf h0 h1
  obtain ⟨hb1, hb2, hb3, hb4⟩ := slice_boundary_tendsto_fts η hη0 hη1 f hf h0 h1
  -- `f` is `C²` at interior points, so its first and second derivatives exist there.
  have hcd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 2 f θ := by
    intro θ hθ
    have hmem : Work.Spaces.Iθ ∈ 𝓝 θ :=
      Filter.mem_of_superset (Ioo_mem_nhds hθ.1 hθ.2)
        (fun x hx => show x ∈ Work.Spaces.Iθ from ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    exact (hf θ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).contDiffAt hmem
  have hdf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd θ hθ).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) θ) θ := fun θ hθ =>
    (((hcd θ hθ).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- Integrability of `f² σ''`.
  have hI6 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => 4 * η * (f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))))
        Work.Spaces.Iθ :=
      (hI4.const_mul (4 * η)).add (hI5.const_mul (4 * η * (1 + η)))
    refine h.congr_fun_ae ?_
    filter_upwards with θ
    simp only [Work.FTS.EllipticEst.AngSecond.sigDD_apply, Work.FTS.EllipticEst.AngSecond.sigE_apply, Work.FTS.EllipticEst.AngSecond.c2_apply]
    ring
  -- The first integration by parts.
  have hA_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t * deriv f t * sigE η t)
        (deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
          + f θ * deriv f θ * sigD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hddf θ hθ)).mul (Work.FTS.EllipticEst.AngSecond.sigE_hasDerivAt η hθ)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hA_int : IntervalIntegrable (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ :=
      (hI1.add hI2).add hI3
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hA_zero : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t * deriv f t * sigE η t)
      (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
        + f θ * deriv f θ * sigD η θ) hA_deriv hA_int hb1 hb2
  have hA_split : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      = (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ) := by
    have h12 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ := hI1.add hI2
    rw [MeasureTheory.integral_add h12 hI3, MeasureTheory.integral_add hI1 hI2]
  -- The second integration by parts.
  have hB_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t ^ 2 * sigD η t)
        (2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hdf θ hθ)).mul (sigD_hasDerivAt_fts η hθ)
    have hfun : (f * f) * (fun t : ℝ => sigD η t)
        = fun t : ℝ => f t ^ 2 * sigD η t := by
      funext t
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hB_int : IntervalIntegrable (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ :=
      (hI3.const_mul 2).add hI6
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hB_zero : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t ^ 2 * sigD η t)
      (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ)
      hB_deriv hB_int hb3 hb4
  -- Expand `σ''`.
  have hI6_eq : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ)
      = 4 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ,
            f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))) := by
    have hfun : (fun θ => f θ ^ 2 * sigDD η θ)
        = (fun θ => 4 * η * (f θ ^ 2 * sigE η θ)
            + 4 * η * (1 + η) * (f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)))) := by
      funext θ
      simp only [Work.FTS.EllipticEst.AngSecond.sigDD_apply, Work.FTS.EllipticEst.AngSecond.sigE_apply, Work.FTS.EllipticEst.AngSecond.c2_apply]
      ring
    rw [hfun, MeasureTheory.integral_add (hI4.const_mul (4 * η))
      (hI5.const_mul (4 * η * (1 + η))),
      MeasureTheory.integral_const_mul (4 * η) (fun θ => f θ ^ 2 * sigE η θ),
      MeasureTheory.integral_const_mul (4 * η * (1 + η))
        (fun θ => f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)))]
  have hB_split : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ) := by
    rw [MeasureTheory.integral_add (hI3.const_mul 2) hI6,
      MeasureTheory.integral_const_mul 2 (fun θ => f θ * deriv f θ * sigD η θ)]
  -- Assemble.
  set a := ∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ with ha
  set b := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ with hb
  set c := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ with hc
  set d := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ with hd
  set e := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * c2 θ ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))
    with he
  have h1' : a + b + c = 0 := by
    rw [← hA_split]; exact hA_zero
  have h2' : 2 * c + (4 * η * d + 4 * η * (1 + η) * e) = 0 := by
    rw [← hI6_eq, ← hB_split]; exact hB_zero
  have hmain : a = -b + 2 * η * d + 2 * η * (1 + η) * e := by linarith
  exact hmain

end Work.FTS.EllipticEst.remov
