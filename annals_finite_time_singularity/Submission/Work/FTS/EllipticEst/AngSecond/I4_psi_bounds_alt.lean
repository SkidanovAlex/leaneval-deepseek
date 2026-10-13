/-
Copyright: work module for the Elgindi finite-time singularity project.

# Boundedness of `Ψ̄ = u / cos θ` and of its derivative on the open quadrant

Fallback proof of the endpoint bounds needed by the `I₄` identity
(`Submission.Work.FTS.EllipticEst.AngSecond.I4_lower_bound`): for `u` of class `C²` on a
neighbourhood of `[0, π/2]` with `u (π/2) = 0`, the function `Ψ̄ θ = u θ / cos θ` and its
derivative are bounded on `(0, π/2)`.

The hard endpoint is `π/2`, where `cos` has a simple zero: `u` vanishes there, so the quotient
extends continuously with the limit `-u'(π/2)`, and its derivative — computed by the quotient
rule as `(u'·cos θ + u·sin θ)/cos²θ` — stays bounded because the numerator vanishes to second
order.  With `t = π/2 - θ ∈ (0, 1/4]` the two inputs are the mean-value bounds
`|u θ| ≤ M₁·t` and `|u'θ - u'(π/2)| ≤ M₂·t`, `|u θ - u'(π/2)(θ - π/2)| ≤ M₂·t²`
(`M₁`, `M₂` bound `|u'|`, `|u''|` on the compact quadrant), together with the elementary
trigonometric estimates `t·cos(1/4) ≤ sin t` and `|sin t - t cos t| ≤ t²`.

On `[0, π/2 - 1/4]`, where `cos θ ≥ sin(1/4) > 0`, both bounds are immediate from the
supremum bounds `M₀` of `|u|` and `M₁` of `|u'|`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## Trigonometric helpers -/

theorem sin_quarter_pos : (0 : ℝ) < Real.sin (1 / 4) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])

theorem cos_quarter_pos : (0 : ℝ) < Real.cos (1 / 4) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩

/-- `sin t ≥ t·cos(1/4)` for `0 < t ≤ 1/4`. -/
theorem sin_ge_mul_cos_quarter {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 4) :
    t * Real.cos (1 / 4) ≤ Real.sin t := by
  obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope Real.sin h0
    Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
  have hcos : Real.cos (1 / 4) ≤ Real.cos c :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hc.1) (by linarith [Real.pi_gt_three])
      (by linarith [hc.2, h1])
  have hval : Real.sin t = t * Real.cos c := by
    have ht : t ≠ 0 := ne_of_gt h0
    rw [Real.deriv_sin, Real.sin_zero, sub_zero] at hcval
    rw [hcval, mul_div_assoc', mul_comm t (Real.sin t), sub_zero]
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hcos (le_of_lt h0)

/-- `|sin t - t cos t| ≤ t²` for `0 ≤ t`. -/
theorem abs_sin_sub_mul_cos_le {t : ℝ} (h0 : 0 ≤ t) :
    |Real.sin t - t * Real.cos t| ≤ t ^ 2 := by
  have hInt : (∫ s in (0 : ℝ)..t, s * Real.sin s) = Real.sin t - t * Real.cos t := by
    have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s) (s * Real.sin s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos s) s := Real.hasDerivAt_sin s
      have h2 : HasDerivAt (fun s : ℝ => s * Real.cos s) (Real.cos s - s * Real.sin s) s := by
        have h := (hasDerivAt_id s).mul (Real.hasDerivAt_cos s)
        convert h using 1
        · ext x; simp [Pi.mul_apply]
        · simp only [id_eq]; ring
      have h3 := h1.sub h2
      convert h3 using 1
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_id.mul Real.continuous_sin).intervalIntegrable 0 t)
    simpa using h
  have hsin1 : ∀ s : ℝ, |Real.sin s| ≤ 1 := fun s =>
    abs_le.mpr ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩
  rw [← hInt]
  calc |∫ s in (0 : ℝ)..t, s * Real.sin s|
      ≤ ∫ s in (0 : ℝ)..t, |s * Real.sin s| := by
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s => s * Real.sin s) h0
    _ ≤ ∫ s in (0 : ℝ)..t, s := by
        refine intervalIntegral.integral_mono_on h0 ?_ ?_ ?_
        · exact (continuous_abs.comp (continuous_id.mul Real.continuous_sin)).intervalIntegrable 0 t
        · exact continuous_id.intervalIntegrable 0 t
        · intro s hs
          calc |s * Real.sin s| = s * |Real.sin s| := by rw [abs_mul, abs_of_nonneg hs.1]
            _ ≤ s * 1 := mul_le_mul_of_nonneg_left (hsin1 s) hs.1
            _ = s := mul_one s
    _ = t ^ 2 / 2 := by rw [integral_id]; ring
    _ ≤ t ^ 2 := by nlinarith [h0]

/-- `sin(1/4) ≤ cos θ` for `0 ≤ θ ≤ π/2 - 1/4`. -/
theorem sin_quarter_le_cos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2 - 1 / 4) :
    Real.sin (1 / 4) ≤ Real.cos θ := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 2 - 1 / 4) h0
    (by linarith [Real.pi_gt_three]) h1
  rwa [Real.cos_pi_div_two_sub] at h

/-- Mean value bound: `|f y - f x| ≤ M (y - x)` when `|f'| ≤ M` on `(x,y)`. -/
theorem abs_sub_le_of_abs_deriv_le {f : ℝ → ℝ} {x y M : ℝ} (hxy : x ≤ y)
    (hcont : ContinuousOn f (Set.Icc x y)) (hdiff : DifferentiableOn ℝ f (Set.Ioo x y))
    (hM : ∀ t ∈ Set.Ioo x y, |deriv f t| ≤ M) :
    |f y - f x| ≤ M * (y - x) := by
  rcases eq_or_lt_of_le hxy with h | h
  · subst h; simp
  · obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope f h hcont hdiff
    have hpos : (0 : ℝ) < y - x := by linarith
    have key : f y - f x = deriv f c * (y - x) := by
      rw [hcval]; field_simp
    calc |f y - f x| = |deriv f c| * (y - x) := by rw [key, abs_mul, abs_of_pos hpos]
      _ ≤ M * (y - x) := mul_le_mul_of_nonneg_right (hM c hc) (le_of_lt hpos)

/-- The derivative of `θ ↦ u θ / cos θ` on the open quadrant. -/
theorem deriv_div_cos_eq (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hd : DifferentiableAt ℝ u θ) :
    deriv (fun θ' => u θ' / Real.cos θ') θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [show (fun θ' => u θ' / Real.cos θ') = u / Real.cos by funext x; rfl]
  rw [deriv_div hd Real.differentiableAt_cos hcos, Real.deriv_cos]
  ring

/-- Fallback proof of the endpoint bounds for `Ψ̄ = u / cos θ`. -/
theorem I4_psi_bounds_alt (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set s : Set ℝ := Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) with hs
  have hsopen : IsOpen s := isOpen_Ioo
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ s := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hcu : ContinuousOn u (Set.Icc 0 (Real.pi / 2)) := hu.continuousOn.mono hsub
  have hcu1 : ContinuousOn (deriv u) (Set.Icc 0 (Real.pi / 2)) :=
    (hu.continuousOn_deriv_of_isOpen hsopen (by norm_num)).mono hsub
  have hcu2 : ContinuousOn (deriv (deriv u)) (Set.Icc 0 (Real.pi / 2)) :=
    ((hu.deriv_of_isOpen (m := 1) hsopen (by norm_num)).continuousOn_deriv_of_isOpen hsopen
      (by norm_num)).mono hsub
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcu2
  have hM0' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u x| ≤ M0 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM0 x hx
  have hM1' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv u x| ≤ M1 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM1 x hx
  have hM2' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv u) x| ≤ M2 := fun x hx => by
    simpa [Real.norm_eq_abs] using hM2 x hx
  have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_refl 0, le_of_lt hπ⟩
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg (u 0)) (hM0' 0 hIcc0)
  have hM1nn : 0 ≤ M1 := le_trans (abs_nonneg (deriv u 0)) (hM1' 0 hIcc0)
  have hM2nn : 0 ≤ M2 := le_trans (abs_nonneg (deriv (deriv u) 0)) (hM2' 0 hIcc0)
  have hdiffu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ u θ := fun θ hθ =>
    (hu.contDiffAt (Ioo_mem_nhds (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))).differentiableAt
      (by simp)
  -- ## (A) first order bound at `π/2`
  have hA : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u θ| ≤ M1 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hcont : ContinuousOn u (Set.Icc θ (Real.pi / 2)) :=
      hcu.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hdiff : DifferentiableOn ℝ u (Set.Ioo θ (Real.pi / 2)) :=
      (hu.differentiableOn (by simp)).mono fun x hx =>
        ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff
      (fun t ht => hM1' t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩)
    rw [hu1] at hle
    simpa using hle
  -- ## (C) Lipschitz bound for `deriv u` at `π/2`
  have hCb : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv u θ - deriv u (Real.pi / 2)| ≤ M2 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hcont : ContinuousOn (deriv u) (Set.Icc θ (Real.pi / 2)) :=
      hcu1.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hdiff : DifferentiableOn ℝ (deriv u) (Set.Ioo θ (Real.pi / 2)) :=
      ((hu.deriv_of_isOpen (m := 1) hsopen (by norm_num)).differentiableOn (by simp)).mono
        fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff
      (fun t ht => hM2' t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩)
    rwa [abs_sub_comm] at hle
  -- ## (B) second order bound at `π/2`
  have hdg : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2)) t
        = deriv u t - deriv u (Real.pi / 2) := by
    intro t ht
    have h1 : HasDerivAt u (deriv u t) t := (hdiffu t ht).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (deriv u (Real.pi / 2)) t := by
      have h := ((hasDerivAt_id t).sub_const (Real.pi / 2)).const_mul (deriv u (Real.pi / 2))
      simpa using h
    have h3 := (h1.sub h2).deriv
    have h4 : (fun s : ℝ => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        = (u - fun s : ℝ => deriv u (Real.pi / 2) * (s - Real.pi / 2)) := by
      ext x; rfl
    rw [h4]
    exact h3
  have hB : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)| ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
    intro θ hθ
    have hcont : ContinuousOn (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (Set.Icc θ (Real.pi / 2)) :=
      (hcu.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).mono
        (fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩)
    have hdiff : DifferentiableOn ℝ (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2))
        (Set.Ioo θ (Real.pi / 2)) :=
      ((hu.differentiableOn (by simp)).mono (fun x hx =>
          ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, Real.pi_pos]⟩)).sub
        ((DifferentiableOn.mul (differentiableOn_const (deriv u (Real.pi / 2)))
            (differentiableOn_id.sub (differentiableOn_const (Real.pi / 2)))).mono
          (fun x _ => trivial))
    have hMg : ∀ t ∈ Set.Ioo θ (Real.pi / 2),
        |deriv (fun s => u s - deriv u (Real.pi / 2) * (s - Real.pi / 2)) t|
          ≤ M2 * (Real.pi / 2 - θ) := by
      intro t ht
      rw [hdg t ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, Real.pi_pos]⟩]
      have h1 := hCb t ⟨by linarith [ht.1, hθ.1], le_of_lt ht.2⟩
      have h2 : Real.pi / 2 - t ≤ Real.pi / 2 - θ := by linarith [ht.1]
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hM2nn)
    have hle := abs_sub_le_of_abs_deriv_le hθ.2 hcont hdiff hMg
    have hg0 : u (Real.pi / 2) - deriv u (Real.pi / 2) * (Real.pi / 2 - Real.pi / 2) = 0 := by
      rw [hu1]; ring
    rw [hg0, zero_sub] at hle
    simp only [abs_neg] at hle
    have : (M2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
    rw [this] at hle
    simpa using hle
  -- ## the two bounds
  refine ⟨max (max (M0 / Real.sin (1 / 4)) ((M1 + M0) / Real.sin (1 / 4) ^ 2))
      (max (M1 / Real.cos (1 / 4)) ((M1 + 2 * M2) / Real.cos (1 / 4) ^ 2)), ?_, ?_⟩
  · have h1 : 0 ≤ Real.sin (1 / 4) := le_of_lt sin_quarter_pos
    exact le_max_of_le_left (le_max_of_le_left (div_nonneg hM0nn h1))
  · intro θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdθ : DifferentiableAt ℝ u θ := hdiffu θ hθ
    rcases le_or_gt θ (Real.pi / 2 - 1 / 4) with hle | hlt
    · -- case 1 : θ ≤ π/2 - 1/4
      have hc1 : (0 : ℝ) < Real.sin (1 / 4) := sin_quarter_pos
      have hcos_ge : Real.sin (1 / 4) ≤ Real.cos θ := sin_quarter_le_cos (le_of_lt hθ.1) hle
      have hcos_pos : 0 < Real.cos θ := lt_of_lt_of_le hc1 hcos_ge
      have hb1 : |u θ / Real.cos θ| ≤ M0 / Real.sin (1 / 4) := by
        rw [abs_div, abs_of_pos hcos_pos, div_le_div_iff₀ hcos_pos hc1]
        have h2 : |u θ| * Real.sin (1 / 4) ≤ M0 * Real.sin (1 / 4) :=
          mul_le_mul_of_nonneg_right (hM0' θ hθI) (le_of_lt hc1)
        have h3 : M0 * Real.sin (1 / 4) ≤ M0 * Real.cos θ :=
          mul_le_mul_of_nonneg_left hcos_ge hM0nn
        linarith
      have hb2 : |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ (M1 + M0) / Real.sin (1 / 4) ^ 2 := by
        rw [deriv_div_cos_eq u hθ hdθ]
        have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ M1 + M0 := by
          have h1 : |deriv u θ * Real.cos θ| ≤ M1 := by
            rw [abs_mul]
            calc |deriv u θ| * |Real.cos θ| ≤ M1 * |Real.cos θ| :=
                  mul_le_mul_of_nonneg_right (hM1' θ hθI) (abs_nonneg _)
              _ ≤ M1 * 1 := mul_le_mul_of_nonneg_left
                  (abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩) hM1nn
              _ = M1 := mul_one M1
          have h2 : |u θ * Real.sin θ| ≤ M0 := by
            rw [abs_mul]
            calc |u θ| * |Real.sin θ| ≤ M0 * |Real.sin θ| :=
                  mul_le_mul_of_nonneg_right (hM0' θ hθI) (abs_nonneg _)
              _ ≤ M0 * 1 := mul_le_mul_of_nonneg_left
                  (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩) hM0nn
              _ = M0 := mul_one M0
          calc |deriv u θ * Real.cos θ + u θ * Real.sin θ|
              ≤ |deriv u θ * Real.cos θ| + |u θ * Real.sin θ| := abs_add_le _ _
            _ ≤ M1 + M0 := add_le_add h1 h2
        rw [abs_div, abs_of_pos (pow_pos hcos_pos 2), div_le_div_iff₀ (pow_pos hcos_pos 2) (pow_pos hc1 2)]
        have h4 : Real.sin (1 / 4) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hcos_ge, hc1]
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ| * Real.sin (1 / 4) ^ 2
            ≤ (M1 + M0) * Real.sin (1 / 4) ^ 2 :=
              mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
          _ ≤ (M1 + M0) * Real.cos θ ^ 2 :=
              mul_le_mul_of_nonneg_left h4 (by linarith [hM1nn, hM0nn])
      exact ⟨le_trans hb1 (le_trans (le_max_left _ _) (le_max_left _ _)),
        le_trans hb2 (le_trans (le_max_right _ _) (le_max_left _ _))⟩
    · -- case 2 : θ > π/2 - 1/4
      have ht0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have ht1 : Real.pi / 2 - θ ≤ 1 / 4 := by linarith [hlt]
      have hsin_ge : (Real.pi / 2 - θ) * Real.cos (1 / 4) ≤ Real.sin (Real.pi / 2 - θ) :=
        sin_ge_mul_cos_quarter ht0 ht1
      have hcos_eq : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
      have hsin_eq : Real.sin θ = Real.cos (Real.pi / 2 - θ) := by
        have h := Real.sin_pi_div_two_sub (Real.pi / 2 - θ)
        rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
      have hcos_pos : 0 < Real.cos θ := by
        rw [hcos_eq]
        exact lt_of_lt_of_le (mul_pos ht0 cos_quarter_pos) hsin_ge
      have htrig : |Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ| ≤ (Real.pi / 2 - θ) ^ 2 := by
        rw [hcos_eq, hsin_eq]
        exact abs_sin_sub_mul_cos_le (le_of_lt ht0)
      have hb1 : |u θ / Real.cos θ| ≤ M1 / Real.cos (1 / 4) := by
        rw [abs_div, abs_of_pos hcos_pos, div_le_div_iff₀ hcos_pos cos_quarter_pos, hcos_eq]
        calc |u θ| * Real.cos (1 / 4)
            ≤ (M1 * (Real.pi / 2 - θ)) * Real.cos (1 / 4) :=
              mul_le_mul_of_nonneg_right (hA θ hθI) (le_of_lt cos_quarter_pos)
          _ = M1 * ((Real.pi / 2 - θ) * Real.cos (1 / 4)) := by ring
          _ ≤ M1 * Real.sin (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hsin_ge hM1nn
      have hnum : |deriv u θ * Real.cos θ + u θ * Real.sin θ|
          ≤ (M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2 := by
        have hcos_le_t : |Real.cos θ| ≤ Real.pi / 2 - θ := by
          rw [abs_of_nonneg (le_of_lt hcos_pos), hcos_eq]
          exact Real.sin_le (le_of_lt ht0)
        have hdecomp : deriv u θ * Real.cos θ + u θ * Real.sin θ
            = deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
              + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ
              + (u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ := by ring
        have hT1 : |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)|
            ≤ M1 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          exact mul_le_mul (hM1' (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩) htrig
            (abs_nonneg _) hM1nn
        have hT2 : |(deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|
            ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          calc |deriv u θ - deriv u (Real.pi / 2)| * |Real.cos θ|
              ≤ (M2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) :=
                mul_le_mul (hCb θ hθI) hcos_le_t (abs_nonneg _) (mul_nonneg hM2nn (le_of_lt ht0))
            _ = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
        have hT3 : |(u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ|
            ≤ M2 * (Real.pi / 2 - θ) ^ 2 := by
          rw [abs_mul]
          calc |u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)| * |Real.sin θ|
              ≤ (M2 * (Real.pi / 2 - θ) ^ 2) * 1 :=
                mul_le_mul (hB θ hθI)
                  (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩) (abs_nonneg _)
                  (mul_nonneg hM2nn (sq_nonneg _))
            _ = M2 * (Real.pi / 2 - θ) ^ 2 := by ring
        rw [hdecomp]
        calc |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
              + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ
              + (u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ|
            ≤ |deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)
                + (deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|
              + |(u θ - deriv u (Real.pi / 2) * (θ - Real.pi / 2)) * Real.sin θ| := abs_add_le _ _
          _ ≤ (|deriv u (Real.pi / 2) * (Real.cos θ - (Real.pi / 2 - θ) * Real.sin θ)|
                + |(deriv u θ - deriv u (Real.pi / 2)) * Real.cos θ|) + M2 * (Real.pi / 2 - θ) ^ 2 :=
              add_le_add (abs_add_le _ _) hT3
          _ ≤ (M1 * (Real.pi / 2 - θ) ^ 2 + M2 * (Real.pi / 2 - θ) ^ 2)
                + M2 * (Real.pi / 2 - θ) ^ 2 := by linarith [hT1, hT2, hT3]
          _ = (M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2 := by ring
      have hb2 : |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ (M1 + 2 * M2) / Real.cos (1 / 4) ^ 2 := by
        rw [deriv_div_cos_eq u hθ hdθ, abs_div, abs_of_pos (pow_pos hcos_pos 2),
          div_le_div_iff₀ (pow_pos hcos_pos 2) (pow_pos cos_quarter_pos 2)]
        have hsq : (Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2 ≤ (Real.cos θ) ^ 2 := by
          rw [hcos_eq]
          have h := pow_le_pow_left₀ (mul_nonneg (le_of_lt ht0) (le_of_lt cos_quarter_pos)) hsin_ge 2
          rwa [show ((Real.pi / 2 - θ) * Real.cos (1 / 4)) ^ 2
            = (Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2 by ring] at h
        calc |deriv u θ * Real.cos θ + u θ * Real.sin θ| * Real.cos (1 / 4) ^ 2
            ≤ ((M1 + 2 * M2) * (Real.pi / 2 - θ) ^ 2) * Real.cos (1 / 4) ^ 2 :=
              mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
          _ = (M1 + 2 * M2) * ((Real.pi / 2 - θ) ^ 2 * Real.cos (1 / 4) ^ 2) := by ring
          _ ≤ (M1 + 2 * M2) * (Real.cos θ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by linarith [hM1nn, hM2nn])
      exact ⟨le_trans hb1 (le_trans (le_max_left _ _) (le_max_right _ _)),
        le_trans hb2 (le_trans (le_max_right _ _) (le_max_right _ _))⟩

