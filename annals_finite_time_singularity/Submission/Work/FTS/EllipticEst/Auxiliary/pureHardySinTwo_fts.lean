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

namespace Work.FTS.EllipticEst.Aux

/-! ## Elementary trigonometric comparisons

Both endpoints of `Iθ = [0, π/2]` are singular for the weight `sin(2θ)^{-2}`.  On the halves
`[0,π/4]` and `[π/4,π/2]` Jordan's inequality `sin x ≥ (2/π) x` gives the comparison with a
power weight, and `Work.Elliptic.power_hardy` supplies the sharp power Hardy inequality. -/

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

/-- `(4/π) t > 0` for `t > 0`. -/
private lemma four_div_pi_mul_pos {t : ℝ} (ht : 0 < t) : 0 < (4 / Real.pi) * t :=
  mul_pos (by positivity) ht

/-! ## Two elementary algebraic identities -/

private lemma sq_mul_div_sq (c : ℝ) {t : ℝ} (ht : t ≠ 0) : (c * t) ^ 2 / t ^ 2 = c ^ 2 := by
  rw [← div_pow, mul_div_cancel_right₀ c ht]

private lemma div_sq_four_pi (u : ℝ) {t : ℝ} (ht : t ≠ 0) :
    u ^ 2 / ((4 / Real.pi) * t) ^ 2 = Real.pi ^ 2 / 16 * (u ^ 2 / t ^ 2) := by
  rw [div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by positivity) ht))]
  field_simp [ht, Real.pi_ne_zero]
  ring

/-! ## The power-weight Hardy inequality in division form -/

/-- `Work.Elliptic.power_hardy` at `η = 0`, written with `/` instead of real powers. -/
private lemma power_hardy_div {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) (h0 : f 0 = 0) :
    (∫ t in (0 : ℝ)..a, f t ^ 2 / t ^ 2) ≤ 4 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 := by
  have h := Work.Elliptic.power_hardy (a := a) (η := 0) ha le_rfl (by norm_num) hf h0
  have e1 : (∫ t in (0 : ℝ)..a, f t ^ 2 / t ^ 2)
      = ∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + (0 : ℝ))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show f t ^ 2 / t ^ 2 = f t ^ 2 * t ^ (-(2 + (0 : ℝ)))
    rw [Set.uIcc_of_le ha.le] at ht
    rw [show (2 : ℝ) + 0 = 2 by norm_num, div_eq_mul_inv, ← Real.rpow_natCast t 2,
      ← Real.rpow_neg ht.1]
    norm_num
  have e2 : (∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-(0 : ℝ)))
      = ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _ht
    show deriv f t ^ 2 * t ^ (-(0 : ℝ)) = deriv f t ^ 2
    simp
  calc (∫ t in (0 : ℝ)..a, f t ^ 2 / t ^ 2)
      = ∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + (0 : ℝ))) := e1
    _ ≤ 4 / (1 + 0) ^ 2 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-(0 : ℝ)) := h
    _ = 4 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 := by rw [e2]; norm_num

/-- The mirror of `power_hardy_div` at the right endpoint: `∫_a^b f²/(b-t)² ≤ 4 ∫_a^b (f')²`
for `f` of class `C¹` on `[a,b]` with `f b = 0`. -/
private lemma power_hardy_div_right {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) (hb : f b = 0) :
    (∫ t in a..b, f t ^ 2 / (b - t) ^ 2) ≤ 4 * ∫ t in a..b, (deriv f t) ^ 2 := by
  have hpos : (0 : ℝ) < b - a := by linarith
  set g : ℝ → ℝ := fun t => f (b - t) with hg
  have hg_cd : ContDiffOn ℝ 1 g (Set.Icc 0 (b - a)) := by
    have h1 : ContDiffOn ℝ 1 (fun t : ℝ => b - t) (Set.Icc 0 (b - a)) := by fun_prop
    have h2 : Set.MapsTo (fun t : ℝ => b - t) (Set.Icc 0 (b - a)) (Set.Icc a b) := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := hf.comp h1 h2
    simpa only [hg, Function.comp_def] using this
  have hg0 : g 0 = 0 := by simp [hg, hb]
  have hph := power_hardy_div hpos hg_cd hg0
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (b - a), deriv g t = -deriv f (b - t) := by
    intro t _ht
    rw [hg]
    exact deriv_comp_const_sub f b t
  have e1 : (∫ t in (0 : ℝ)..(b - a), g t ^ 2 / t ^ 2) = ∫ t in a..b, f t ^ 2 / (b - t) ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => f s ^ 2 / (b - s) ^ 2) b (a := (0 : ℝ)) (b := b - a)
    rw [show b - (b - a) = a by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro t _ht
    show g t ^ 2 / t ^ 2 = f (b - t) ^ 2 / (b - (b - t)) ^ 2
    rw [hg]
    rw [show b - (b - t) = t by ring]
  have e2 : (∫ t in (0 : ℝ)..(b - a), (deriv g t) ^ 2) = ∫ t in a..b, (deriv f t) ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => (deriv f s) ^ 2) b (a := (0 : ℝ)) (b := b - a)
    rw [show b - (b - a) = a by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro t ht
    show (deriv g t) ^ 2 = (deriv f (b - t)) ^ 2
    rw [Set.uIcc_of_le hpos.le] at ht
    rw [hderiv t ht, neg_sq]
  rw [e1, e2] at hph
  exact hph

/-! ## The two halves of `Iθ` -/

/-- The pure Hardy inequality on `[0, π/4]`. -/
private lemma hardy_left {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    (∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 := by
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hcd : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 4)) :=
    hf.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  obtain ⟨C, hC, hbf, hbd⟩ := Work.Elliptic.power_hardy_bounds hπ4 hcd h0
  have hfc : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    hf.continuousOn.mono fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsc : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
  have hcont1 : ContinuousOn (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    (hfc.pow 2).div hsc fun θ hθ => pow_ne_zero 2 (ne_of_gt (hsinpos θ hθ))
  have hfθ_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), f θ ^ 2 ≤ (C * θ) ^ 2 := by
    intro θ hθ
    have h1 : |f θ| ≤ C * θ := hbf θ hθ
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC (le_of_lt hθ.1))]
    exact h1
  have hden_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ((4 / Real.pi) * θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
    intro θ hθ
    exact pow_le_pow_left₀ (le_of_lt (four_div_pi_mul_pos hθ.1))
      (four_div_pi_mul_le_sin_two (le_of_lt hθ.1) (le_of_lt hθ.2)) 2
  have hbnd1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |f θ ^ 2 / (Real.sin (2 * θ)) ^ 2| ≤ C ^ 2 * Real.pi ^ 2 / 16 := by
    intro θ hθ
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2 ≤ (C * θ) ^ 2 / (Real.sin (2 * θ)) ^ 2 :=
          div_le_div_of_nonneg_right (hfθ_le θ hθ) (sq_nonneg _)
      _ ≤ (C * θ) ^ 2 / ((4 / Real.pi) * θ) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (four_div_pi_mul_pos hθ.1) 2)
            (hden_le θ hθ)
      _ = Real.pi ^ 2 / 16 * ((C * θ) ^ 2 / θ ^ 2) := div_sq_four_pi (C * θ) (ne_of_gt hθ.1)
      _ = C ^ 2 * Real.pi ^ 2 / 16 := by rw [sq_mul_div_sq C (ne_of_gt hθ.1)]; ring
  have hIi : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      volume 0 (Real.pi / 4) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound (le_of_lt hπ4) hcont1 _
      hbnd1
  have hcont2 : ContinuousOn (fun θ : ℝ => f θ ^ 2 / θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    (hfc.pow 2).div (continuous_id.continuousOn.pow 2)
      fun θ hθ => pow_ne_zero 2 (ne_of_gt hθ.1)
  have hbnd2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |f θ ^ 2 / θ ^ 2| ≤ C ^ 2 := by
    intro θ hθ
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc f θ ^ 2 / θ ^ 2 ≤ (C * θ) ^ 2 / θ ^ 2 :=
          div_le_div_of_nonneg_right (hfθ_le θ hθ) (sq_nonneg _)
      _ = C ^ 2 := sq_mul_div_sq C (ne_of_gt hθ.1)
  have hIi2 : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / θ ^ 2) volume 0 (Real.pi / 4) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound (le_of_lt hπ4) hcont2 _ hbnd2
  have hmono : (∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 16 * ∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 / θ ^ 2 := by
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
        f θ ^ 2 / (Real.sin (2 * θ)) ^ 2 ≤ Real.pi ^ 2 / 16 * (f θ ^ 2 / θ ^ 2) := by
      intro θ hθ
      calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2 ≤ f θ ^ 2 / ((4 / Real.pi) * θ) ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (four_div_pi_mul_pos hθ.1) 2)
              (hden_le θ hθ)
        _ = Real.pi ^ 2 / 16 * (f θ ^ 2 / θ ^ 2) := div_sq_four_pi (f θ) (ne_of_gt hθ.1)
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hπ4) hIi (hIi2.const_mul _) hpt
    rwa [intervalIntegral.integral_const_mul] at h
  have hph := power_hardy_div hπ4 hcd h0
  calc (∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 16 * ∫ θ in (0 : ℝ)..(Real.pi / 4), f θ ^ 2 / θ ^ 2 := hmono
    _ ≤ Real.pi ^ 2 / 16 * (4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hph (by positivity)
    _ = Real.pi ^ 2 / 4 * ∫ θ in (0 : ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 := by ring

/-- The pure Hardy inequality on `[π/4, π/2]`. -/
private lemma hardy_right {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in (Real.pi / 4)..(Real.pi / 2), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 4 * ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv f θ) ^ 2 := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ42 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  set g : ℝ → ℝ := fun t => f (Real.pi / 2 - t) with hg
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
  obtain ⟨C, hC, hbf, hbd⟩ := Work.Elliptic.power_hardy_bounds hπ2 hg_cd hg0
  have hfb : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      f θ ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := by
    intro θ hθ
    have ht : Real.pi / 2 - θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.2], by linarith [hθ.1, Real.pi_pos]⟩
    have hval : g (Real.pi / 2 - θ) = f θ := by
      simp only [hg]
      rw [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring]
    have hle : |g (Real.pi / 2 - θ)| ≤ C * (Real.pi / 2 - θ) := hbf _ ht
    rw [hval] at hle
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC (by linarith [hθ.2]))]
    exact hle
  have hfc : ContinuousOn f (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hf.continuousOn.mono fun x hx => ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  have hsinpos : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])
  have hsc : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
  have hcont1 : ContinuousOn (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (hfc.pow 2).div hsc fun θ hθ => pow_ne_zero 2 (ne_of_gt (hsinpos θ hθ))
  have hden_le : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
    intro θ hθ
    exact pow_le_pow_left₀ (le_of_lt (four_div_pi_mul_pos (by linarith [hθ.2])))
      (four_div_pi_mul_le_sin_two' (le_of_lt hθ.1) (le_of_lt hθ.2)) 2
  have hbnd1 : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |f θ ^ 2 / (Real.sin (2 * θ)) ^ 2| ≤ C ^ 2 * Real.pi ^ 2 / 16 := by
    intro θ hθ
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2
        ≤ (C * (Real.pi / 2 - θ)) ^ 2 / (Real.sin (2 * θ)) ^ 2 :=
          div_le_div_of_nonneg_right (hfb θ hθ) (sq_nonneg _)
      _ ≤ (C * (Real.pi / 2 - θ)) ^ 2 / ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _)
            (pow_pos (four_div_pi_mul_pos (by linarith [hθ.2])) 2) (hden_le θ hθ)
      _ = Real.pi ^ 2 / 16 * ((C * (Real.pi / 2 - θ)) ^ 2 / (Real.pi / 2 - θ) ^ 2) :=
          div_sq_four_pi (C * (Real.pi / 2 - θ)) (by linarith [hθ.2])
      _ = C ^ 2 * Real.pi ^ 2 / 16 := by
          rw [sq_mul_div_sq C (by linarith [hθ.2])]; ring
  have hIi : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      volume (Real.pi / 4) (Real.pi / 2) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42 hcont1 _ hbnd1
  have hcont2 : ContinuousOn (fun θ : ℝ => f θ ^ 2 / (Real.pi / 2 - θ) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (hfc.pow 2).div (((continuous_const.sub continuous_id).pow 2).continuousOn)
      fun θ hθ => pow_ne_zero 2 (by linarith [hθ.2] : Real.pi / 2 - θ ≠ 0)
  have hbnd2 : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |f θ ^ 2 / (Real.pi / 2 - θ) ^ 2| ≤ C ^ 2 := by
    intro θ hθ
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc f θ ^ 2 / (Real.pi / 2 - θ) ^ 2
        ≤ (C * (Real.pi / 2 - θ)) ^ 2 / (Real.pi / 2 - θ) ^ 2 :=
          div_le_div_of_nonneg_right (hfb θ hθ) (sq_nonneg _)
      _ = C ^ 2 := sq_mul_div_sq C (by linarith [hθ.2])
  have hIi2 : IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / (Real.pi / 2 - θ) ^ 2)
      volume (Real.pi / 4) (Real.pi / 2) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42 hcont2 _ hbnd2
  have hmono : (∫ θ in (Real.pi / 4)..(Real.pi / 2), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 16 * ∫ θ in (Real.pi / 4)..(Real.pi / 2),
          f θ ^ 2 / (Real.pi / 2 - θ) ^ 2 := by
    have hpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        f θ ^ 2 / (Real.sin (2 * θ)) ^ 2
          ≤ Real.pi ^ 2 / 16 * (f θ ^ 2 / (Real.pi / 2 - θ) ^ 2) := by
      intro θ hθ
      calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2
          ≤ f θ ^ 2 / ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _)
              (pow_pos (four_div_pi_mul_pos (by linarith [hθ.2])) 2) (hden_le θ hθ)
        _ = Real.pi ^ 2 / 16 * (f θ ^ 2 / (Real.pi / 2 - θ) ^ 2) :=
            div_sq_four_pi (f θ) (by linarith [hθ.2])
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hπ42 hIi (hIi2.const_mul _) hpt
    rwa [intervalIntegral.integral_const_mul] at h
  have hmh := power_hardy_div_right (a := Real.pi / 4) (b := Real.pi / 2)
    (by linarith [Real.pi_pos]) (hf.mono (Set.Icc_subset_Icc (by positivity) le_rfl)) h1
  calc (∫ θ in (Real.pi / 4)..(Real.pi / 2), f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ Real.pi ^ 2 / 16 * ∫ θ in (Real.pi / 4)..(Real.pi / 2),
          f θ ^ 2 / (Real.pi / 2 - θ) ^ 2 := hmono
    _ ≤ Real.pi ^ 2 / 16 * (4 * ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv f θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hmh (by positivity)
    _ = Real.pi ^ 2 / 4 * ∫ θ in (Real.pi / 4)..(Real.pi / 2), (deriv f θ) ^ 2 := by ring

/-! ## Interval integrability of the four integrands -/

private lemma ii_pieces {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2) volume 0 (Real.pi / 4) ∧
    IntervalIntegrable (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2) volume (Real.pi / 4) (Real.pi / 2) ∧
    IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2) volume 0 (Real.pi / 4) ∧
    IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2) volume (Real.pi / 4) (Real.pi / 2) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hπ42 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨C, hC, hbf, hbd⟩ := Work.Elliptic.contDiffOn_one_bounds hf h0 h1
  have hsub1 : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsub2 : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hfc : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn.mono Set.Ioo_subset_Icc_self
  have hdcont : ContinuousOn (fun θ : ℝ => deriv f θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1' : ContinuousOn (derivWithin f (Set.Icc 0 (Real.pi / 2))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hπ2) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1'.congr fun t ht => ?_
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsc : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
        (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      ((hfc.mono hsub1).pow 2).div (hsc.mono hsub1) fun θ hθ =>
        pow_ne_zero 2 (ne_of_gt (hsinpos θ (hsub1 hθ)))
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
        |f θ ^ 2 / (Real.sin (2 * θ)) ^ 2| ≤ C ^ 2 * Real.pi ^ 2 / 16 := by
      intro θ hθ
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hm : |f θ| ≤ C * θ := by
        have h := hbf θ (Set.Ioo_subset_Icc_self (hsub1 hθ))
        rwa [min_eq_left (by linarith [hθ.2])] at h
      have hden : ((4 / Real.pi) * θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (four_div_pi_mul_pos hθ.1))
          (four_div_pi_mul_le_sin_two (le_of_lt hθ.1) (le_of_lt hθ.2)) 2
      calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2 ≤ (C * θ) ^ 2 / (Real.sin (2 * θ)) ^ 2 :=
            div_le_div_of_nonneg_right (by
              rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC (le_of_lt hθ.1))]; exact hm)
              (sq_nonneg _)
        _ ≤ (C * θ) ^ 2 / ((4 / Real.pi) * θ) ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (four_div_pi_mul_pos hθ.1) 2) hden
        _ = Real.pi ^ 2 / 16 * ((C * θ) ^ 2 / θ ^ 2) := div_sq_four_pi (C * θ) (ne_of_gt hθ.1)
        _ = C ^ 2 * Real.pi ^ 2 / 16 := by rw [sq_mul_div_sq C (ne_of_gt hθ.1)]; ring
    exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound (le_of_lt hπ4) hcont _
      hbnd
  · have hcont : ContinuousOn (fun θ : ℝ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      ((hfc.mono hsub2).pow 2).div (hsc.mono hsub2) fun θ hθ =>
        pow_ne_zero 2 (ne_of_gt (hsinpos θ (hsub2 hθ)))
    have hbnd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        |f θ ^ 2 / (Real.sin (2 * θ)) ^ 2| ≤ C ^ 2 * Real.pi ^ 2 / 16 := by
      intro θ hθ
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hm : |f θ| ≤ C * (Real.pi / 2 - θ) := by
        have h := hbf θ (Set.Ioo_subset_Icc_self (hsub2 hθ))
        have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := by
          rw [min_eq_right]
          linarith [hθ.1, Real.pi_pos]
        rwa [hmin] at h
      have hden : ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (four_div_pi_mul_pos (by linarith [hθ.2])))
          (four_div_pi_mul_le_sin_two' (le_of_lt hθ.1) (le_of_lt hθ.2)) 2
      calc f θ ^ 2 / (Real.sin (2 * θ)) ^ 2
          ≤ (C * (Real.pi / 2 - θ)) ^ 2 / (Real.sin (2 * θ)) ^ 2 :=
            div_le_div_of_nonneg_right (by
              rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC (by linarith [hθ.2]))]; exact hm)
              (sq_nonneg _)
        _ ≤ (C * (Real.pi / 2 - θ)) ^ 2 / ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _)
              (pow_pos (four_div_pi_mul_pos (by linarith [hθ.2])) 2) hden
        _ = Real.pi ^ 2 / 16 * ((C * (Real.pi / 2 - θ)) ^ 2 / (Real.pi / 2 - θ) ^ 2) :=
            div_sq_four_pi (C * (Real.pi / 2 - θ)) (by linarith [hθ.2])
        _ = C ^ 2 * Real.pi ^ 2 / 16 := by
            rw [sq_mul_div_sq C (by linarith [hθ.2])]; ring
    exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42 hcont _ hbnd
  · have hcont : ContinuousOn (fun θ : ℝ => (deriv f θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      (hdcont.mono hsub1).pow 2
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |(deriv f θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      have h := hbd θ (hsub1 hθ)
      rw [Real.norm_eq_abs] at h
      calc |(deriv f θ) ^ 2| = (deriv f θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
        _ ≤ C ^ 2 := by rw [sq_le_sq, abs_of_nonneg hC]; exact h
    exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound (le_of_lt hπ4) hcont _
      hbnd
  · have hcont : ContinuousOn (fun θ : ℝ => (deriv f θ) ^ 2)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (hdcont.mono hsub2).pow 2
    have hbnd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |(deriv f θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      have h := hbd θ (hsub2 hθ)
      rw [Real.norm_eq_abs] at h
      calc |(deriv f θ) ^ 2| = (deriv f θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
        _ ≤ C ^ 2 := by rw [sq_le_sq, abs_of_nonneg hC]; exact h
    exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hπ42 hcont _ hbnd

/-! ## The target -/

theorem pureHardySinTwo_fts : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
    (∫ θ in Work.Spaces.Iθ, f θ ^ 2 / (Real.sin (2 * θ)) ^ 2)
      ≤ C * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  refine ⟨π ^ 2 / 4, ?_, ?_, ?_⟩
  · positivity
  · nlinarith [Real.pi_pos, Real.pi_lt_four]
  · intro f hf h0 h1
    obtain ⟨hLii, hRii, hDLii, hDRii⟩ := ii_pieces hf h0 h1
    have hL := hardy_left hf h0
    have hR := hardy_right hf h1
    have hle : (0 : ℝ) ≤ π / 2 := by positivity
    have hkey : ∀ h : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in (0 : ℝ)..(π / 2), h θ := by
      intro h
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hle]
    rw [hkey (fun θ => f θ ^ 2 / (Real.sin (2 * θ)) ^ 2), hkey (fun θ => (deriv f θ) ^ 2)]
    have e1 := intervalIntegral.integral_add_adjacent_intervals hLii hRii
    have e2 := intervalIntegral.integral_add_adjacent_intervals hDLii hDRii
    rw [← e1, ← e2]
    nlinarith [hL, hR]

end Work.FTS.EllipticEst.Aux
