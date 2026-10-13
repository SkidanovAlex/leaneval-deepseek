import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `low_order_split`

The two low-order angular terms `∫∫ w²(∂_θΨ)²` and `∫∫ w²Ψ²` of a datum of the weak class
`TT.EllWeakPos α k F Ψ` are *separately* controlled by the `η`-weighted second angular
derivative `∫∫ w² (∂_θθΨ)² sin(2θ)^{-η}` — the form of the estimate consumed by
`ESW.Assembly` (whereas `TT.ESW.low_order_le` gives the bound for the *sum* of the two
integrands).

The proof is slicewise.  For `z > 0` the slice `u = Ψ z ·` satisfies the hypotheses of
`TT.ESW.slice_deriv_bound` and `TT.ESW.slice_value_bound` (`TT.ESW.slice_class_facts`,
`TT.ESW.exists_interior_zero_of_moment` + Rolle for the interior critical point, and the
right-endpoint limit `TT.ESW.slice_tendsto_pi_half`), so that with `E(z) = ∫_θ (∂_θθΨ z θ)²`,

  `∫_θ (∂_θΨ z θ)² ≤ (π/2)² E(z)`,   `∫_θ Ψ(z,θ)² ≤ (π/2)⁴ E(z)`,

and `E(z) ≤ ∫_θ (∂_θθΨ z θ)² σ(θ)` because `σ ≥ 1`.  Multiplying by `w(z)² ≥ 0` and
integrating the two pointwise bounds against the integrable RHS
(`TT.ESW.integrable_w_sq_thetaEnergy`) gives the two separate inequalities, with constants
`(π/2)²` and `(π/2)⁴` whose sum is `< 20`.
-/

/-- **The split form of the one-dimensional low-order slice bound.**  A `C²` function on
`(0, π/2)` with vanishing angular moment, right endpoint limit `0` and finite `η`-weighted
second derivative satisfies the two low-order bounds separately, with the constants `(π/2)²`
and `(π/2)⁴`. -/
theorem slice_split_low_order {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hπ : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hval : u (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0)
    (h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) ∧
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨θ₁, hθ₁, hzero⟩ := exists_interior_zero_of_moment hsm.continuousOn hint hmom
  have hcontIcc : ContinuousOn u (Set.Icc θ₁ (Real.pi / 2)) :=
    continuousOn_Icc_of_tendsto hsm.continuousOn hπ hval hθ₁
  obtain ⟨θ₀, hθ₀, hcrit⟩ :=
    exists_deriv_eq_zero hθ₁.2 hcontIcc (by rw [hzero, hval])
  have hd := slice_deriv_bound hsm ⟨lt_trans hθ₁.1 hθ₀.1, hθ₀.2⟩ hcrit h2
  have hv := slice_value_bound hsm hθ₁ hzero hd
  set E : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 with hE
  set J : ℝ := ∫ s in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) s) ^ 2 * Work.FTS.EllipticEst.sEta s with hJ
  have hEJ : E ≤ J := by
    rw [hE, hJ]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _) h2 ?_
    exact Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => by
      have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
      nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)]
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  have hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * E :=
    fun θ hθ => by rw [hE]; exact hd θ hθ
  have hvb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2) ^ 3 * E :=
    fun θ hθ => by rw [hE]; exact hv θ hθ
  have hb1 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * E := by
    have hmono : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) * E) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (MeasureTheory.integrable_const ((Real.pi / 2) * E))
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hdb)
    have hconst : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) * E))
        = (Real.pi / 2) * E * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) * E * (Real.pi / 2) := by rw [← hconst]; exact hmono
      _ = (Real.pi / 2) ^ 2 * E := by ring
  have hb0 : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) ≤ (Real.pi / 2) ^ 4 * E := by
    have hmono : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 3 * E) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (MeasureTheory.integrable_const ((Real.pi / 2) ^ 3 * E))
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hvb)
    have hconst : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 3 * E))
        = (Real.pi / 2) ^ 3 * E * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 3 * E * (Real.pi / 2) := by rw [← hconst]; exact hmono
      _ = (Real.pi / 2) ^ 4 * E := by ring
  constructor
  · calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * E := hb1
      _ ≤ (Real.pi / 2) ^ 2 * J := mul_le_mul_of_nonneg_left hEJ (by positivity)
      _ = (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by rw [hJ]
  · calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * E := hb0
      _ ≤ (Real.pi / 2) ^ 4 * J := mul_le_mul_of_nonneg_left hEJ (by positivity)
      _ = (Real.pi / 2) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by rw [hJ]

theorem low_order_split {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
  set Jw : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) with hJw
  have hJint : IntegrableOn Jw Work.Spaces.Iz := by
    rw [hJw]
    exact integrable_w_sq_thetaEnergy hwk
  -- the two pointwise bounds
  have hpt1 : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * Jw z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · rw [← h0, hJw]
      simp [Work.Spaces.w]
    · obtain ⟨hsm2, hB2, hint, hmom, hval⟩ := slice_class_facts hwk hz0
      obtain ⟨hs1, -⟩ :=
        slice_split_low_order hsm2 (slice_tendsto_pi_half hwk hz0) hval hint hmom hB2
      have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
        simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      have e2 : Jw z = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
        have h : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            = ∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        simp only [hJw, h]
      rw [e1, e2]
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := mul_le_mul_of_nonneg_left hs1 hw2
        _ = (Real.pi / 2) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by ring
  have hpt0 : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * Jw z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · rw [← h0, hJw]
      simp [Work.Spaces.w]
    · obtain ⟨hsm2, hB2, hint, hmom, hval⟩ := slice_class_facts hwk hz0
      obtain ⟨-, hs0⟩ :=
        slice_split_low_order hsm2 (slice_tendsto_pi_half hwk hz0) hval hint hmom hB2
      have e2 : Jw z = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
        have h : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            = ∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        simp only [hJw, h]
      rw [e2]
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2) ^ 4 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := mul_le_mul_of_nonneg_left hs0 hw2
        _ = (Real.pi / 2) ^ 4 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by ring
  -- integrate the two pointwise bounds
  have hInt1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 2 * (∫ z in Work.Spaces.Iz, Jw z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      (g := fun z => (Real.pi / 2) ^ 2 * Jw z)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))
      (hJint.const_mul ((Real.pi / 2) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt1)
    rwa [MeasureTheory.integral_const_mul] at h
  have hInt0 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 4 * (∫ z in Work.Spaces.Iz, Jw z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (g := fun z => (Real.pi / 2) ^ 4 * Jw z)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))
      (hJint.const_mul ((Real.pi / 2) ^ 4))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt0)
    rwa [MeasureTheory.integral_const_mul] at h
  -- the arithmetic
  have hJnn : 0 ≤ ∫ z in Work.Spaces.Iz, Jw z := by
    rw [hJw]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
    exact mul_nonneg (sq_nonneg _)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ))
  have hpi : (Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4 ≤ 20 := by
    have h1 : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
    have h2 : (0 : ℝ) < Real.pi / 2 := by positivity
    have h3 : (Real.pi / 2) ^ 2 < 4 := by nlinarith [h1, h2]
    have h4 : (Real.pi / 2) ^ 4 < 16 := by nlinarith [h3, sq_nonneg (Real.pi / 2)]
    linarith
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 2 * (∫ z in Work.Spaces.Iz, Jw z)
        + (Real.pi / 2) ^ 4 * (∫ z in Work.Spaces.Iz, Jw z) := add_le_add hInt1 hInt0
    _ = ((Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4) * (∫ z in Work.Spaces.Iz, Jw z) := by ring
    _ ≤ 20 * (∫ z in Work.Spaces.Iz, Jw z) := mul_le_mul_of_nonneg_right hpi hJnn
    _ = 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by rw [hJw]

end

end Work.FTS.EllipticEst.TT.ESW
