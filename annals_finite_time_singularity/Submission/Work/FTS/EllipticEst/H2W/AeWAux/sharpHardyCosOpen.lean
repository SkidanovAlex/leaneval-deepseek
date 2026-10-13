import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.SharpHardyCosWeight
import Submission.Work.Elliptic.sharp_hardy_sin_two
import Submission.Work.FTS.EllipticEst.Honest.PthCore.HalfSharpHardyCosTwo
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.powerHardyOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeWAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## A pointwise comparison of the weights

For `0 < u ≤ π/2` and `0 ≤ η`, `sin u ≤ u` together with `η ≥ 0` gives `u^{-(2+η)} ≤ sin(u)^{-(2+η)}`,
and since `cos²u + sin²u = 1` the latter equals `cos²u·sin(u)^{-(2+η)} + sin(u)^{-η}`.  So the
power weight is dominated by the `cos²`-weighted singular weight plus the `η`-weight. -/

/-- `u^{-(2+η)} ≤ cos²u·sin(u)^{-(2+η)} + sin(u)^{-η}` for `0 ≤ η` and `0 < u ≤ π/2`. -/
lemma rpow_le_cosSq_mul_rpow {η u : ℝ} (hη0 : 0 ≤ η) (hu0 : 0 < u) (hu1 : u ≤ Real.pi / 2) :
    u ^ (-(2 + η)) ≤ Real.cos u ^ 2 * (Real.sin u) ^ (-(2 + η)) + (Real.sin u) ^ (-η) := by
  have hs0 : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu1, Real.pi_pos])
  have hle : Real.sin u ≤ u := Real.sin_le hu0.le
  have h1 : u ^ (-(2 + η)) ≤ (Real.sin u) ^ (-(2 + η)) :=
    Real.rpow_le_rpow_of_nonpos hs0 hle (by linarith)
  have h2 : (Real.sin u) ^ (-(2 + η))
      = Real.cos u ^ 2 * (Real.sin u) ^ (-(2 + η)) + (Real.sin u) ^ (-η) := by
    have hsum : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := Real.cos_sq_add_sin_sq u
    have hsin2 : (Real.sin u) ^ (-(2 + η)) * (Real.sin u) ^ 2 = (Real.sin u) ^ (-η) := by
      rw [← Real.rpow_natCast (Real.sin u) 2,
        ← Real.rpow_add hs0 (-(2 + η)) ((2 : ℕ) : ℝ)]
      congr 1
      push_cast
      ring
    calc (Real.sin u) ^ (-(2 + η))
        = (Real.sin u) ^ (-(2 + η)) * (Real.cos u ^ 2 + Real.sin u ^ 2) := by
          rw [hsum, mul_one]
      _ = Real.cos u ^ 2 * (Real.sin u) ^ (-(2 + η))
            + (Real.sin u) ^ (-(2 + η)) * (Real.sin u) ^ 2 := by ring
      _ = Real.cos u ^ 2 * (Real.sin u) ^ (-(2 + η)) + (Real.sin u) ^ (-η) := by rw [hsin2]
  rw [← h2]
  exact h1

/-- `cos (2 (π/2 - x)) = - cos (2x)`. -/
private lemma cos_two_pi_half_sub (x : ℝ) :
    Real.cos (2 * (Real.pi / 2 - x)) = -Real.cos (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.cos_pi_sub]

/-- `sin (2 (π/2 - x)) = sin (2x)`. -/
private lemma sin_two_pi_half_sub (x : ℝ) :
    Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-! ## Integrability bookkeeping -/

/-- If `0 ≤ f ≤ g` pointwise on a measurable set `s` and `g` is integrable on `s`, then so is
`f` (an `AEStronglyMeasurable` hypothesis is all else that is needed). -/
private lemma integrableOn_of_le {s : Set ℝ} {f g : ℝ → ℝ} (hms : MeasurableSet s)
    (hg : IntegrableOn g s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ x ∈ s, 0 ≤ f x) (hle : ∀ x ∈ s, f x ≤ g x) : IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := hg
  refine hg'.mono' hf ?_
  rw [MeasureTheory.ae_restrict_iff' hms]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]
  exact hle x hx

/-- `IntervalIntegrable` on `[a,b]` (with `a ≤ b`) is integrability over `Ioo a b`. -/
private lemma intervalIntegrable_iff_integrableOn_Ioo {a b : ℝ} (hab : a ≤ b) {H : ℝ → ℝ} :
    IntervalIntegrable H volume a b ↔ IntegrableOn H (Set.Ioo a b) := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact ⟨fun h => h.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc,
    fun h => h.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm⟩

/-- Relation between the power weights at `u` and at `2u`. -/
private lemma rpow_eq_rpow_two_mul {c u : ℝ} (hu : 0 < u) : u ^ c = 2 ^ (-c) * (2 * u) ^ c := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero, one_mul]

/-- `(2u)^c = 2^c u^c`. -/
private lemma two_mul_rpow_eq {c u : ℝ} (hu : 0 < u) : (2 * u) ^ c = 2 ^ c * u ^ c :=
  Real.mul_rpow (by norm_num) hu.le

/-! ## The left half of the sharp Hardy inequality -/

/-- **Sharp Hardy inequality on the left half `(0, π/4)`.**  For `f` of class `C¹` on the *open*
interval `(0, π/4)` whose weighted energies are integrable (no control of `f` at the endpoint `0`
is assumed: the boundary term is handled by the sharp power-weight Hardy inequality
`powerHardyOpen`, whose hypotheses pin down the endpoint behaviour),

`∫_0^{π/4} f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_0^{π/4} (f')² sin(2θ)^{-η}
    + 2 ∫_0^{π/4} f² sin(2θ)^{-η}`. -/
theorem leftHalfSharp {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 4)))
    (hL : IntegrableOn
      (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 4)))
    (hR : IntegrableOn (fun θ => deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 4)))
    (hM : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 4))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 4),
        f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 4),
          deriv f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 4), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hS : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 4)) := measurableSet_Ioo
  -- continuity of the building blocks on `(0, π/4)`
  have hfc : ContinuousOn f (Set.Ioo 0 (Real.pi / 4)) := hf.continuousOn
  have hdc : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 4)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 4)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsin_pos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), 0 < Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  have hid : ContinuousOn (fun θ : ℝ => θ) (Set.Ioo 0 (Real.pi / 4)) := continuousOn_id
  have hpow2 : ContinuousOn (fun θ : ℝ => (2 * θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 4)) :=
    ((continuousOn_const.mul hid).rpow_const
      (fun x hx => Or.inl (mul_ne_zero two_ne_zero (ne_of_gt hx.1))))
  have hpow2' : ContinuousOn (fun θ : ℝ => (2 * θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) :=
    ((continuousOn_const.mul hid).rpow_const
      (fun x hx => Or.inl (mul_ne_zero two_ne_zero (ne_of_gt hx.1))))
  have hpowth : ContinuousOn (fun θ : ℝ => θ ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 4)) :=
    hid.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  have hpowth' : ContinuousOn (fun θ : ℝ => θ ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) :=
    hid.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  -- the two pointwise comparisons on `(0, π/4)`
  have hcmpA : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (Real.sin (2 * x)) ^ (-(2 + η)) ≤ (2 * x) ^ (-(2 + η)) + 2 * (Real.sin (2 * x)) ^ (-η) := by
    intro x hx
    exact Work.FTS.EllipticEst.Honest.PthCore.sin_pow_compare_two hη0 hη1 (2 * x)
      (by linarith [hx.1]) (by linarith [hx.2])
  have hcmpB : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (2 * x) ^ (-(2 + η))
        ≤ Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)) + (Real.sin (2 * x)) ^ (-η) := by
    intro x hx
    exact rpow_le_cosSq_mul_rpow hη0 (by linarith [hx.1]) (by linarith [hx.2])
  -- integrability of the `2θ`-power piece
  have hsum_int : IntegrableOn (fun x => f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      + 2 * (f x ^ 2 * (Real.sin (2 * x)) ^ (-η))) (Set.Ioo 0 (Real.pi / 4)) := by
    have h := hL.add (hM.const_mul 2)
    change IntegrableOn (fun x => f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      + 2 * (f x ^ 2 * (Real.sin (2 * x)) ^ (-η))) (Set.Ioo 0 (Real.pi / 4)) at h
    exact h
  have hFP : IntegrableOn (fun x => f x ^ 2 * (2 * x) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 4)) := by
    refine integrableOn_of_le hS hsum_int ?_ ?_ ?_
    · exact (hfc.pow 2 |>.mul hpow2).aestronglyMeasurable hS
    · intro x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hx.1]) _)
    · intro x hx
      have h := hcmpB x hx
      have hnn : 0 ≤ f x ^ 2 * (Real.sin (2 * x)) ^ (-η) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsin_pos x hx)) _)
      have h1 := mul_le_mul_of_nonneg_left h (sq_nonneg (f x))
      have h2 : f x ^ 2 * (Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
          + (Real.sin (2 * x)) ^ (-η))
          = f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            + f x ^ 2 * (Real.sin (2 * x)) ^ (-η) := by ring
      rw [h2] at h1
      linarith [h1, hnn]
  have hdom : IntegrableOn (fun x => f x ^ 2 * (2 * x) ^ (-(2 + η))
      + 2 * (f x ^ 2 * (Real.sin (2 * x)) ^ (-η))) (Set.Ioo 0 (Real.pi / 4)) := by
    have h := hFP.add (hM.const_mul 2)
    change IntegrableOn (fun x => f x ^ 2 * (2 * x) ^ (-(2 + η))
      + 2 * (f x ^ 2 * (Real.sin (2 * x)) ^ (-η))) (Set.Ioo 0 (Real.pi / 4)) at h
    exact h
  -- integrability of the power-weight pieces `θ^{-(2+η)}` and `θ^{-η}`
  have hFQ : IntegrableOn (fun x => f x ^ 2 * x ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 4)) := by
    refine integrableOn_of_le hS (hFP.const_mul (2 ^ (2 + η))) ?_ ?_ ?_
    · exact (hfc.pow 2 |>.mul hpowth).aestronglyMeasurable hS
    · intro x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hx.1) _)
    · intro x hx
      have h := rpow_eq_rpow_two_mul (c := -(2 + η)) hx.1
      have h1 : f x ^ 2 * x ^ (-(2 + η))
          = f x ^ 2 * (2 ^ (-(-(2 + η))) * (2 * x) ^ (-(2 + η))) := by rw [h]
      have h2 : f x ^ 2 * (2 ^ (-(-(2 + η))) * (2 * x) ^ (-(2 + η)))
          = 2 ^ (2 + η) * (f x ^ 2 * (2 * x) ^ (-(2 + η))) := by rw [neg_neg]; ring
      exact le_of_eq (h1.trans h2)
  have hFD : IntegrableOn (fun x => deriv f x ^ 2 * x ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) := by
    refine integrableOn_of_le hS (hR.const_mul (2 ^ η)) ?_ ?_ ?_
    · exact (hdc.pow 2 |>.mul hpowth').aestronglyMeasurable hS
    · intro x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hx.1) _)
    · intro x hx
      have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
      have hle := Real.rpow_le_rpow_of_nonpos (hsin_pos x hx) hsinle (by linarith : -η ≤ 0)
      have hxη : x ^ (-η) = 2 ^ η * (2 * x) ^ (-η) := by
        rw [two_mul_rpow_eq (u := x) hx.1, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) η]
        field_simp
      have hxη' : x ^ (-η) ≤ 2 ^ η * (Real.sin (2 * x)) ^ (-η) := by
        rw [hxη]
        exact mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 ^ η)
      have h1 := mul_le_mul_of_nonneg_left hxη' (sq_nonneg (deriv f x))
      have h2 : deriv f x ^ 2 * (2 ^ η * (Real.sin (2 * x)) ^ (-η))
          = 2 ^ η * (deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by ring
      exact h1.trans (le_of_eq h2)
  -- the monotone comparison with the power weight
  have hstep1 : (∫ x in Set.Ioo 0 (Real.pi / 4),
        f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (2 * x) ^ (-(2 + η)))
        + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
    have hmono := setIntegral_mono_on hL hdom hS (fun x hx => by
      have hA := hcmpA x hx
      have hcos : Real.cos (2 * x) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * x)
      have hw : 0 ≤ (Real.sin (2 * x)) ^ (-(2 + η)) :=
        Real.rpow_nonneg (le_of_lt (hsin_pos x hx)) _
      have h1 : f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
          ≤ f x ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)) := by
        calc f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            = f x ^ 2 * (Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))) := by ring
          _ ≤ f x ^ 2 * (1 * (Real.sin (2 * x)) ^ (-(2 + η))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcos hw) (sq_nonneg _)
          _ = f x ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)) := by ring
      have h2 := mul_le_mul_of_nonneg_left hA (sq_nonneg (f x))
      have h3 : f x ^ 2 * ((2 * x) ^ (-(2 + η)) + 2 * (Real.sin (2 * x)) ^ (-η))
          = f x ^ 2 * (2 * x) ^ (-(2 + η)) + 2 * (f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        ring
      exact h1.trans (h2.trans (le_of_eq h3)))
    rw [integral_add hFP (hM.const_mul 2), integral_const_mul] at hmono
    exact hmono
  -- the substitution `2θ ↦ θ`
  have hstep2 : (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (2 * x) ^ (-(2 + η)))
      = 2 ^ (-(2 + η)) * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * x ^ (-(2 + η))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hS (fun x hx => ?_)
    rw [two_mul_rpow_eq (u := x) hx.1]
    ring
  -- the sharp power-weight Hardy inequality on `(0, π/4)`
  have hPH : (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * x ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * x ^ (-η)) :=
    powerHardyOpen hpi4 hη0 hη1 hf hFQ hFD
  have hstep4 : (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * x ^ (-η))
      = 2 ^ η * (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * (2 * x) ^ (-η)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun hS (fun x hx => ?_)
    have h2ne : (2 : ℝ) ^ η ≠ 0 := by positivity
    rw [two_mul_rpow_eq (u := x) hx.1, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) η]
    field_simp
  have hstep5 : (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * (2 * x) ^ (-η))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
    have hmid : IntegrableOn (fun x => deriv f x ^ 2 * (2 * x) ^ (-η))
        (Set.Ioo 0 (Real.pi / 4)) := by
      refine integrableOn_of_le hS hR ?_ ?_ ?_
      · exact (hdc.pow 2 |>.mul hpow2').aestronglyMeasurable hS
      · intro x hx
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hx.1]) _)
      · intro x hx
        have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
        have h := Real.rpow_le_rpow_of_nonpos (hsin_pos x hx) hsinle (by linarith : -η ≤ 0)
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
    exact setIntegral_mono_on hmid hR hS (fun x hx => by
      have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
      have h := Real.rpow_le_rpow_of_nonpos (hsin_pos x hx) hsinle (by linarith : -η ≤ 0)
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _))
  -- the coefficient identity
  have hcoef : 2 ^ (-(2 + η)) * (4 / (1 + η) ^ 2 * 2 ^ η) = 1 / (1 + η) ^ 2 := by
    rw [show (2 : ℝ) ^ (-(2 + η)) = ((2 : ℝ) ^ (2 + η))⁻¹ from
      Real.rpow_neg (by norm_num) (2 + η)]
    have h2 : (2 : ℝ) ^ (2 + η) = 2 ^ 2 * 2 ^ η := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
    rw [h2]
    have h2η : (2 : ℝ) ^ η ≠ 0 := by positivity
    have h1η : (1 : ℝ) + η ≠ 0 := by linarith
    field_simp
    ring
  calc (∫ x in Set.Ioo 0 (Real.pi / 4),
        f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (2 * x) ^ (-(2 + η)))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := hstep1
    _ = 2 ^ (-(2 + η)) * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * x ^ (-(2 + η)))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        rw [hstep2]
    _ ≤ 2 ^ (-(2 + η))
          * (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * x ^ (-η)))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hPH (by positivity : (0 : ℝ) ≤ 2 ^ (-(2 + η)))) le_rfl
    _ = 2 ^ (-(2 + η))
          * (4 / (1 + η) ^ 2
              * (2 ^ η * (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * (2 * x) ^ (-η))))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        rw [hstep4]
    _ ≤ 2 ^ (-(2 + η))
          * (4 / (1 + η) ^ 2
              * (2 ^ η * (∫ x in Set.Ioo 0 (Real.pi / 4),
                  deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η))))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep5
            (by positivity : (0 : ℝ) ≤ 2 ^ η))
            (by positivity : (0 : ℝ) ≤ 4 / (1 + η) ^ 2))
          (by positivity : (0 : ℝ) ≤ 2 ^ (-(2 + η)))) le_rfl
    _ = 1 / (1 + η) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 4), deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η))
          + 2 * (∫ x in Set.Ioo 0 (Real.pi / 4), f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by
        have hassoc : 2 ^ (-(2 + η))
              * (4 / (1 + η) ^ 2
                  * (2 ^ η * (∫ x in Set.Ioo 0 (Real.pi / 4),
                      deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η))))
            = (2 ^ (-(2 + η)) * (4 / (1 + η) ^ 2 * 2 ^ η))
              * (∫ x in Set.Ioo 0 (Real.pi / 4),
                  deriv f x ^ 2 * (Real.sin (2 * x)) ^ (-η)) := by ring
        rw [hassoc, hcoef]

/-! ## Reflection to the right half -/

/-- Change of variables `θ ↦ π/2 - θ` for integrability over the right half. -/
private lemma integrableOn_Ioo_reflect_right {G : ℝ → ℝ}
    (hG : IntegrableOn G (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    IntegrableOn (fun x => G (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4)) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hii : IntervalIntegrable G volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le h4le]
    exact hG.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hii' : IntervalIntegrable (fun x => G (Real.pi / 2 - x)) volume 0 (Real.pi / 4) := by
    have h := hii.comp_sub_left (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
      show Real.pi / 2 - Real.pi / 2 = 0 by ring] at h
    exact h.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo (a := 0) (b := Real.pi / 4) h4).mp hii'

/-- Change of variables `θ ↦ π/2 - θ` for integrals over the right half. -/
private lemma integral_Ioo_reflect_right (F : ℝ → ℝ) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
      = ∫ x in Set.Ioo 0 (Real.pi / 4), F (Real.pi / 2 - x) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h4le, ← intervalIntegral.integral_of_le h4]
  rw [intervalIntegral.integral_comp_sub_left F (Real.pi / 2)]
  rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
    show Real.pi / 2 - 0 = Real.pi / 2 by ring]

/-- Splitting an integral over `(0, π/2)` into its two halves. -/
private lemma integral_Ioo_split {H : ℝ → ℝ}
    (h1 : IntervalIntegrable H volume 0 (Real.pi / 4))
    (h2 : IntervalIntegrable H volume (Real.pi / 4) (Real.pi / 2)) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), H θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), H θ)
        + ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), H θ := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h2le : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have e1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), H θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h2le]
  have e2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), H θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 4), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h4]
  have e3 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), H θ)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), H θ := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm,
      ← intervalIntegral.integral_of_le h4le]
  rw [e1, e2, e3]
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

/-- `Iθ`-integrals are integrals over `(0, π/2)`. -/
private lemma integral_Iθ_eq_Ioo (H : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, H θ) = ∫ θ in Set.Ioo 0 (Real.pi / 2), H θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The main inequality for a general exponent `η ∈ [0,1)`, in `Iθ`-form.**  The two halves are
`leftHalfSharp` on `(0, π/4)` and its reflection on `(π/4, π/2)`. -/
theorem mainSharp {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hI2 : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.Spaces.Iθ)
    (hI1 : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ)
    (hI0 : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  have hsinp : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  -- continuity of the building blocks on the open interval
  have hf2c : ContinuousOn (fun θ : ℝ => f θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn.pow 2
  have hc2c : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
  have hs2c : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hsinp x hx)))
  -- integrability on the open interval
  have hI2o : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)) := hI2.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc
  have hI1o : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := hI1.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc
  have hI0o : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := hI0.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc
  -- the `cos²`-weighted integrand
  have hLcos : IntegrableOn
      (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine integrableOn_of_le measurableSet_Ioo hI2o ?_ ?_ ?_
    · exact ((hf2c.mul hc2c).mul hs2c).aestronglyMeasurable measurableSet_Ioo
    · intro x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (le_of_lt (hsinp x hx)) _)
    · intro x hx
      have hcos : Real.cos (2 * x) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * x)
      have hw : 0 ≤ (Real.sin (2 * x)) ^ (-(2 + η)) :=
        Real.rpow_nonneg (le_of_lt (hsinp x hx)) _
      calc f x ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
          = f x ^ 2 * (Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))) := by ring
        _ ≤ f x ^ 2 * (1 * (Real.sin (2 * x)) ^ (-(2 + η))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcos hw) (sq_nonneg _)
        _ = f x ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η)) := by ring
  -- the two halves
  have hsubL : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsubR : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hleft := leftHalfSharp hη0 hη1 (f := f) (hf.mono hsubL)
    (hLcos.mono_set hsubL) (hI1o.mono_set hsubL) (hI0o.mono_set hsubL)
  -- the right half, by reflection
  have hg_cd : ContDiffOn ℝ 1 (fun x : ℝ => f (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4)) := by
    have hmap : Set.MapsTo (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4))
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · show (0 : ℝ) < Real.pi / 2 - x
        linarith [hx.2, Real.pi_pos]
      · show Real.pi / 2 - x < Real.pi / 2
        linarith [hx.1]
    have hlin : ContDiffOn ℝ 1 (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo 0 (Real.pi / 4)) := by
      fun_prop
    simpa only [Function.comp_def] using hf.comp hlin hmap
  have hgr_L : IntegrableOn (fun x => f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2
      * (Real.sin (2 * x)) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hLcos.mono_set hsubR)
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioo
    show f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(2 + η))
      = f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
    rw [cos_two_pi_half_sub, sin_two_pi_half_sub]
    ring
  have hgr_M : IntegrableOn (fun x => f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hI0o.mono_set hsubR)
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioo
    show f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
      = f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η)
    rw [sin_two_pi_half_sub]
  have hgr_R : IntegrableOn (fun x => deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2
      * (Real.sin (2 * x)) ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) := by
    have h1 := integrableOn_Ioo_reflect_right (hI1o.mono_set hsubR)
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioo
    show deriv f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
      = deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η)
    rw [deriv_comp_const_sub f (Real.pi / 2) x, sin_two_pi_half_sub]
    ring
  have hright := leftHalfSharp hη0 hη1 (f := fun x : ℝ => f (Real.pi / 2 - x))
    hg_cd hgr_L hgr_R hgr_M
  -- rewrite the reflected integrals
  have hconvL : (∫ x in Set.Ioo 0 (Real.pi / 4), f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + η)))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    show f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      = f (Real.pi / 2 - x) ^ 2 * Real.cos (2 * (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(2 + η))
    rw [cos_two_pi_half_sub, sin_two_pi_half_sub]
    ring
  have hconvM : (∫ x in Set.Ioo 0 (Real.pi / 4),
        f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    show f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * x)) ^ (-η)
      = f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
    rw [sin_two_pi_half_sub]
  have hconvR : (∫ x in Set.Ioo 0 (Real.pi / 4),
        deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    refine Eq.trans ?_ (integral_Ioo_reflect_right
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))).symm
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    show deriv (fun x : ℝ => f (Real.pi / 2 - x)) x ^ 2 * (Real.sin (2 * x)) ^ (-η)
      = deriv f (Real.pi / 2 - x) ^ 2 * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-η)
    rw [deriv_comp_const_sub f (Real.pi / 2) x, sin_two_pi_half_sub]
    ring
  rw [hconvL, hconvM, hconvR] at hright
  -- split all three integrals at `π/4`
  have h1L : IntervalIntegrable (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := 0) (b := Real.pi / 4) (by positivity)).mpr
      (hLcos.mono_set hsubL)
  have h1R : IntervalIntegrable (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := Real.pi / 4) (b := Real.pi / 2)
      (by linarith [Real.pi_pos])).mpr (hLcos.mono_set hsubR)
  have h2L : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := 0) (b := Real.pi / 4) (by positivity)).mpr
      (hI1o.mono_set hsubL)
  have h2R : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := Real.pi / 4) (b := Real.pi / 2)
      (by linarith [Real.pi_pos])).mpr (hI1o.mono_set hsubR)
  have h3L : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := 0) (b := Real.pi / 4) (by positivity)).mpr
      (hI0o.mono_set hsubL)
  have h3R : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume (Real.pi / 4) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo (a := Real.pi / 4) (b := Real.pi / 2)
      (by linarith [Real.pi_pos])).mpr (hI0o.mono_set hsubR)
  rw [integral_Iθ_eq_Ioo
      (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))),
    integral_Ioo_split h1L h1R,
    integral_Iθ_eq_Ioo (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
    integral_Ioo_split h2L h2R,
    integral_Iθ_eq_Ioo (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
    integral_Ioo_split h3L h3R]
  refine le_of_le_of_eq (add_le_add hleft hright) ?_
  ring

theorem sharpHardyCosOpen : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ 1/(1 + Work.Spaces.eta)^2 * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + C * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
  ⟨2, by norm_num, fun f hf _hf0 _hfpi hI2 hI1 hI0 =>
    mainSharp Work.Spaces.eta_nonneg Work.Spaces.eta_lt_one hf hI2 hI1 hI0⟩

end

end Work.FTS.EllipticEst.H2W.AeWAux
