import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.power_hardy_bounds
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-!
# Weighted Hardy inequality on `Iθ` with the weight `sin(2θ)^{-η}`

For `0 < η ≤ 2` and `u : ℝ → ℝ` of class `C¹` on `[0,π/2]` vanishing at both endpoints,

  `∫_{Iθ} u(θ)² sin(2θ)^{-η} dθ ≤ π²/4 ∫_{Iθ} (u')(θ)² dθ  ≤ 10 ∫_{Iθ} (u')(θ)² dθ`.

The proof splits `Iθ` at `π/4`.  On each half the weight `sin(2θ)^{-η}` is dominated by
`(π²/16) t^{-2}`, where `t = θ` on the left and `t = π/2 - θ` on the right (Jordan's
inequality `sin x ≥ (2/π)x` together with `η ≤ 2`), and the sharp power Hardy inequality
`Work.Elliptic.power_hardy` at `η = 0` (constant `4`) on each half gives the result with the
constant `π²/4 ≈ 2.467`.
-/

/-! ## Elementary trigonometric bounds -/

/-- Jordan's inequality on the left half: `(4/π) θ ≤ sin (2θ)` for `0 ≤ θ ≤ π/4`. -/
private lemma four_div_pi_mul_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h2 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) h2
  calc (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) := by ring
    _ ≤ Real.sin (2 * θ) := h

/-- Jordan's inequality on the right half: `(4/π) (π/2 - θ) ≤ sin (2θ)` for `π/4 ≤ θ ≤ π/2`. -/
private lemma four_div_pi_mul_le_sin_two' {θ : ℝ} (h0 : Real.pi / 4 ≤ θ)
    (h1 : θ ≤ Real.pi / 2) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have h2 : 0 ≤ Real.pi / 2 - θ := by linarith
  have h3 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have h := four_div_pi_mul_le_sin_two h2 h3
  have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  rwa [hsin] at h

/-- `x ^ 2 * x ^ (-2 : ℝ) = 1` for `x > 0`. -/
private lemma sq_mul_rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ 2 * x ^ (-2 : ℝ) = 1 := by
  rw [Real.rpow_neg hx.le 2, Real.rpow_two, ← div_eq_mul_inv,
    div_self (pow_ne_zero 2 (ne_of_gt hx))]

/-! ## Comparison of the weight with the power weight on each half -/

/-- On `(0, π/4]`, `sin(2θ)^{-η} ≤ (π²/16) θ^{-2}` for `0 < η ≤ 2`. -/
private lemma sin_rpow_le_left_aux (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) {θ : ℝ}
    (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 4) :
    (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi ^ 2 / 16) * θ ^ (-2 : ℝ) := by
  have hj : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := four_div_pi_mul_le_sin_two h0.le h1
  have ha : 0 < (4 / Real.pi) * θ := mul_pos (by positivity) h0
  have hA : (Real.sin (2 * θ)) ^ (-η) ≤ ((4 / Real.pi) * θ) ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos ha hj (by linarith)
  have hmul : ((4 / Real.pi) * θ) ^ (-η) = (4 / Real.pi) ^ (-η) * θ ^ (-η) :=
    Real.mul_rpow (by positivity) h0.le
  have hB : (4 / Real.pi) ^ (-η) = (Real.pi / 4) ^ η := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi) η,
      ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) η,
      inv_div (4 : ℝ) Real.pi]
  have hC : θ ^ (-η) ≤ θ ^ (-2 : ℝ) * (Real.pi / 4) ^ (2 - η) := by
    rw [show (-η : ℝ) = (-2 : ℝ) + (2 - η) by ring, Real.rpow_add h0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0.le h1 (by linarith))
      (Real.rpow_nonneg h0.le _)
  have hcomb : ((4 / Real.pi) * θ) ^ (-η) ≤ (Real.pi ^ 2 / 16) * θ ^ (-2 : ℝ) := by
    rw [hmul, hB]
    calc (Real.pi / 4) ^ η * θ ^ (-η)
        ≤ (Real.pi / 4) ^ η * (θ ^ (-2 : ℝ) * (Real.pi / 4) ^ (2 - η)) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = ((Real.pi / 4) ^ η * (Real.pi / 4) ^ (2 - η)) * θ ^ (-2 : ℝ) := by ring
      _ = (Real.pi ^ 2 / 16) * θ ^ (-2 : ℝ) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < Real.pi / 4) η (2 - η),
            show η + (2 - η) = 2 by ring, Real.rpow_two]
          ring
  exact hA.trans hcomb

/-- On `[π/4, π/2)`, `sin(2θ)^{-η} ≤ (π²/16) (π/2 - θ)^{-2}` for `0 < η ≤ 2`. -/
private lemma sin_rpow_le_right_aux (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) {θ : ℝ}
    (h0 : Real.pi / 4 ≤ θ) (h1 : θ < Real.pi / 2) :
    (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi ^ 2 / 16) * (Real.pi / 2 - θ) ^ (-2 : ℝ) := by
  have hδ : 0 < Real.pi / 2 - θ := by linarith
  have hδ1 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have hsin : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  have h := sin_rpow_le_left_aux η hη hη2 hδ hδ1
  rwa [hsin] at h

/-! ## The Hardy estimate on the left half -/

/-- `∫_0^{π/4} f² sin(2θ)^{-η} ≤ (π²/4) ∫_0^{π/4} (f')²` for `f` of class `C¹` on
`[0, π/2]` with `f 0 = 0` and `0 < η ≤ 2`. -/
private lemma hardy_left_sinWeight (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    (∫ θ in (0 : ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      ≤ Real.pi ^ 2 / 4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 := by
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hcd : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 4)) :=
    hf.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  obtain ⟨C, hC, hbf, _hbd⟩ := Work.Elliptic.power_hardy_bounds hπ4 hcd h0
  have hfc : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    hcd.continuousOn.mono Set.Ioo_subset_Icc_self
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- the bound `f θ ^ 2 * θ ^ (-2) ≤ C ^ 2`
  have hb2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), f θ ^ 2 * θ ^ (-2 : ℝ) ≤ C ^ 2 := by
    intro θ hθ
    have h1 : |f θ| ≤ C * θ := hbf θ hθ
    have h2 : f θ ^ 2 ≤ (C * θ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC hθ.1.le)]
      exact h1
    calc f θ ^ 2 * θ ^ (-2 : ℝ) ≤ (C * θ) ^ 2 * θ ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hθ.1.le _)
      _ = C ^ 2 * (θ ^ 2 * θ ^ (-2 : ℝ)) := by ring
      _ = C ^ 2 * 1 := by rw [sq_mul_rpow_neg_two hθ.1]
      _ = C ^ 2 := by ring
  -- interval integrability of `f² θ^{-2}`
  have hcontθ : ContinuousOn (fun θ : ℝ => θ ^ (-2 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    continuous_id.continuousOn.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  have hIi2 : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 * θ ^ (-2 : ℝ)) volume 0 (Real.pi / 4) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ4.le
      ((hfc.pow 2).mul hcontθ) (C ^ 2) ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hθ.1.le _))]
    exact hb2 θ hθ
  -- the pointwise comparison
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η) ≤ (Real.pi ^ 2 / 16) * (f θ ^ 2 * θ ^ (-2 : ℝ)) := by
    intro θ hθ
    have hw := sin_rpow_le_left_aux η hη hη2 hθ.1 hθ.2.le
    calc f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ f θ ^ 2 * ((Real.pi ^ 2 / 16) * θ ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (Real.pi ^ 2 / 16) * (f θ ^ 2 * θ ^ (-2 : ℝ)) := by ring
  -- interval integrability of the weighted integrand
  have hIi : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ4.le
      ((hfc.pow 2).mul (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hsinpos x hx))))) ((Real.pi ^ 2 / 16) * C ^ 2) ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
    calc f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (Real.pi ^ 2 / 16) * (f θ ^ 2 * θ ^ (-2 : ℝ)) := hpt θ hθ
      _ ≤ (Real.pi ^ 2 / 16) * C ^ 2 := mul_le_mul_of_nonneg_left (hb2 θ hθ) (by positivity)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hπ4.le hIi (hIi2.const_mul _) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hph := Work.Elliptic.power_hardy (a := Real.pi / 4) (η := 0) hπ4 le_rfl (by norm_num) hcd h0
  have hph' : (∫ t in (0 : ℝ)..(Real.pi / 4), f t ^ 2 * t ^ (-2 : ℝ))
      ≤ 4 * ∫ t in (0 : ℝ)..(Real.pi / 4), (deriv f t) ^ 2 := by
    simpa using hph
  calc (∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      ≤ (Real.pi ^ 2 / 16) * ∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 * θ ^ (-2 : ℝ) := hmono
    _ ≤ (Real.pi ^ 2 / 16) * (4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hph' (by positivity)
    _ = Real.pi ^ 2 / 4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 := by ring

/-! ## Interval integrability of the two integrands on both halves -/

private lemma ii_deriv_sq {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0)
    (h1 : u (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ : ℝ => (deriv u θ) ^ 2) volume 0 (Real.pi / 4) ∧
    IntervalIntegrable (fun θ : ℝ => (deriv u θ) ^ 2) volume (Real.pi / 4) (Real.pi / 2) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hπ42 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨C, _hC, _hbf, hbd⟩ := Work.Elliptic.contDiffOn_one_bounds hu h0 h1
  have hdcont : ContinuousOn (fun θ : ℝ => deriv u θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1' : ContinuousOn (derivWithin u (Set.Icc 0 (Real.pi / 2)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hu.continuousOn_derivWithin (uniqueDiffOn_Icc hπ2) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1'.congr fun t ht => ?_
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |(deriv u θ) ^ 2| ≤ C ^ 2 := by
    intro θ hθ
    have h := hbd θ hθ
    rw [Real.norm_eq_abs] at h
    calc |(deriv u θ) ^ 2| = (deriv u θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
      _ = |deriv u θ| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  refine ⟨?_, ?_⟩
  · refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ4.le
      ((hdcont.mono ?_).pow 2) (C ^ 2) ?_
    · intro x hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    · intro θ hθ
      exact hbnd θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  · refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42
      ((hdcont.mono ?_).pow 2) (C ^ 2) ?_
    · intro x hx
      exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    · intro θ hθ
      have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      exact hbnd θ hmem

private lemma ii_sinWeight (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0)
    (h1 : u (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume 0 (Real.pi / 4) ∧
    IntervalIntegrable (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      volume (Real.pi / 4) (Real.pi / 2) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hπ42 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨C, hC, hbf, _hbd⟩ := Work.Elliptic.contDiffOn_one_bounds hu h0 h1
  have huc : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.continuousOn.mono Set.Ioo_subset_Icc_self
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (huc.pow 2).mul (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hsinpos x hx))))
  have hbndL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |(u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)| ≤ C ^ 2 * (Real.pi ^ 2 / 16) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hw := sin_rpow_le_left_aux η hη hη2 hθ.1 hθ.2.le
    have huw : |u θ| ≤ C * θ := (hbf θ hmem).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    have hu2 : (u θ) ^ 2 ≤ (C * θ) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC hθ.1.le)]
      exact huw
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (hsinpos θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)) _))]
    calc (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (u θ) ^ 2 * ((Real.pi ^ 2 / 16) * θ ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (Real.pi ^ 2 / 16) * ((u θ) ^ 2 * θ ^ (-2 : ℝ)) := by ring
      _ ≤ (Real.pi ^ 2 / 16) * C ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (u θ) ^ 2 * θ ^ (-2 : ℝ) ≤ (C * θ) ^ 2 * θ ^ (-2 : ℝ) :=
                mul_le_mul_of_nonneg_right hu2 (Real.rpow_nonneg hθ.1.le _)
            _ = C ^ 2 * (θ ^ 2 * θ ^ (-2 : ℝ)) := by ring
            _ = C ^ 2 * 1 := by rw [sq_mul_rpow_neg_two hθ.1]
            _ = C ^ 2 := by ring
      _ = C ^ 2 * (Real.pi ^ 2 / 16) := by ring
  have hbndR : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |(u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)| ≤ C ^ 2 * (Real.pi ^ 2 / 16) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
    have hw := sin_rpow_le_right_aux η hη hη2 hθ.1.le hθ.2
    have huw : |u θ| ≤ C * (Real.pi / 2 - θ) :=
      (hbf θ hmem).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
    have hu2 : (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC (by linarith [hθ.2]))]
      exact huw
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (hsinpos θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)) _))]
    calc (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (u θ) ^ 2 * ((Real.pi ^ 2 / 16) * (Real.pi / 2 - θ) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (Real.pi ^ 2 / 16) * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 : ℝ)) := by ring
      _ ≤ (Real.pi ^ 2 / 16) * C ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 : ℝ)
              ≤ (C * (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-2 : ℝ) :=
                mul_le_mul_of_nonneg_right hu2 (Real.rpow_nonneg (by linarith [hθ.2]) _)
            _ = C ^ 2 * ((Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 : ℝ)) := by ring
            _ = C ^ 2 * 1 := by rw [sq_mul_rpow_neg_two (by linarith [hθ.2])]
            _ = C ^ 2 := by ring
      _ = C ^ 2 * (Real.pi ^ 2 / 16) := by ring
  refine ⟨?_, ?_⟩
  · refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ4.le
      (hcont.mono ?_) (C ^ 2 * (Real.pi ^ 2 / 16)) ?_
    · intro x hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    · intro θ hθ
      exact hbndL θ hθ
  · refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42
      (hcont.mono ?_) (C ^ 2 * (Real.pi ^ 2 / 16)) ?_
    · intro x hx
      exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    · intro θ hθ
      exact hbndR θ hθ

/-! ## The Hardy estimate on the right half, by reflection -/

/-- `∫_{π/4}^{π/2} f² sin(2θ)^{-η} ≤ (π²/4) ∫_{π/4}^{π/2} (f')²` for `f` of class `C¹` on
`[0, π/2]` with `f (π/2) = 0` and `0 < η ≤ 2`. -/
private lemma hardy_right_sinWeight (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in (Real.pi / 4)..(Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      ≤ Real.pi ^ 2 / 4 * ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv f θ) ^ 2 := by
  set g : ℝ → ℝ := fun φ => f (Real.pi / 2 - φ) with hg
  have hg_cd : ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi / 2)) := by
    have h1' : ContDiffOn ℝ 1 (fun t : ℝ => Real.pi / 2 - t) (Set.Icc 0 (Real.pi / 2)) := by
      fun_prop
    have h2' : Set.MapsTo (fun t : ℝ => Real.pi / 2 - t) (Set.Icc 0 (Real.pi / 2))
        (Set.Icc 0 (Real.pi / 2)) := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
    have := hf.comp h1' h2'
    simpa only [hg, Function.comp_def] using this
  have hg0 : g 0 = 0 := by simp [hg, h1]
  have hL := hardy_left_sinWeight η hη hη2 hg_cd hg0
  have e1 : (∫ φ in (0 : ℝ)..(Real.pi / 4), (g φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η))
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Real.pi / 2)
      (a := (0 : ℝ)) (b := Real.pi / 4)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ _
    simp only [hg]
    rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]
  have e2 : (∫ φ in (0 : ℝ)..(Real.pi / 4), (deriv g φ) ^ 2)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv f θ) ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => (deriv f θ) ^ 2) (Real.pi / 2) (a := (0 : ℝ)) (b := Real.pi / 4)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro φ _
    show (deriv g φ) ^ 2 = (deriv f (Real.pi / 2 - φ)) ^ 2
    have hd : deriv g φ = -deriv f (Real.pi / 2 - φ) := by
      rw [hg]
      exact deriv_comp_const_sub f (Real.pi / 2) φ
    rw [hd, neg_sq]
  rw [e1, e2] at hL
  exact hL

/-! ## The target -/

theorem hardy_sinWeight (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
      ≤ 10 * ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hπ2.le
  have hkey : ∀ h : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), h θ := by
    intro h
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
  rw [hkey (fun θ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
    hkey (fun θ => (deriv u θ) ^ 2)]
  obtain ⟨hIL, hIR⟩ := ii_sinWeight η hη hη2 hu h0 h1
  obtain ⟨hDL, hDR⟩ := ii_deriv_sq hu h0 h1
  have hL := hardy_left_sinWeight η hη hη2 hu h0
  have hR := hardy_right_sinWeight η hη hη2 hu h1
  have e1 := intervalIntegral.integral_add_adjacent_intervals hIL hIR
  have e2 := intervalIntegral.integral_add_adjacent_intervals hDL hDR
  rw [← e1, ← e2]
  have hpn : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv u θ) ^ 2 :=
    intervalIntegral.integral_nonneg hπ4.le (fun x _ => sq_nonneg _)
  have hqn : (0 : ℝ) ≤ ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv u θ) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun x _ => sq_nonneg _)
  have hπsq : Real.pi ^ 2 / 4 ≤ 10 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hA : Real.pi ^ 2 / 4 * (∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv u θ) ^ 2)
      ≤ 10 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv u θ) ^ 2 :=
    mul_le_mul_of_nonneg_right hπsq hpn
  have hB : Real.pi ^ 2 / 4 * (∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv u θ) ^ 2)
      ≤ 10 * ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv u θ) ^ 2 :=
    mul_le_mul_of_nonneg_right hπsq hqn
  linarith

end Work.FTS.EllipticEst.H2W
