import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.psi_deriv_formula

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

/-- The `g`-function `g θ = u' θ cos θ + u θ sin θ` of the `ψ`-derivative formula has
derivative `(u'' θ + u θ) cos θ` at every point of the open neighbourhood of `[0, π/2]`. -/
private lemma hasDerivAt_gfun (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1))) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    HasDerivAt (fun θ => deriv u θ * Real.cos θ + u θ * Real.sin θ)
      ((deriv (deriv u) x + u x) * Real.cos x) x := by
  have hs : IsOpen (Set.Ioo (-1) (Real.pi / 2 + 1)) := isOpen_Ioo
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hu.deriv_of_isOpen hs (m := 1) (by norm_num)
  have hdu : HasDerivAt u (deriv u x) x :=
    (hu.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hx) |>.hasDerivAt
  have hdu2 : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    (h1.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hx) |>.hasDerivAt
  have hh := (hdu2.mul (Real.hasDerivAt_cos x)).add (hdu.mul (Real.hasDerivAt_sin x))
  convert hh using 1
  ring

/-- If `g` has derivative `g'` on the open neighbourhood of `[0, π/2]`, `‖g'‖` is bounded by
`E cos` there, and `g (π/2) = 0`, then `|g θ| ≤ E (1 - sin θ)` for `θ ∈ [0, π/2)`.

This is the `θ ↦ ∫_θ^{π/2}` form of the fundamental theorem of calculus used for the sharp
`ψ'`-bound: since `∫_θ^{π/2} cos = 1 - sin θ` and `1 - sin θ ≤ cos² θ`, it gives `|ψ'| ≤ E`. -/
private lemma abs_le_of_hasDerivAt_le (g g' : ℝ → ℝ) {E : ℝ}
    (hcont' : ContinuousOn g' (Set.Icc 0 (Real.pi / 2)))
    (hderiv : ∀ x ∈ Set.Ioo (-1) (Real.pi / 2 + 1), HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc 0 (Real.pi / 2), ‖g' x‖ ≤ E * Real.cos x)
    (hgpi : g (Real.pi / 2) = 0) :
    ∀ θ ∈ Set.Ico 0 (Real.pi / 2), |g θ| ≤ E * (1 - Real.sin θ) := by
  intro θ hθ
  have hle_pi : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hsub2 : Set.uIcc θ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [uIcc_of_le hle_pi]
    intro x hx
    exact ⟨hθ.1.trans hx.1, hx.2⟩
  -- integrability of the bound `E cos` and of `g'`
  have hint_cos : IntervalIntegrable (fun x => E * Real.cos x) volume θ (Real.pi / 2) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  have hint_g' : IntervalIntegrable g' volume θ (Real.pi / 2) :=
    (hcont'.mono hsub2).intervalIntegrable
  have hmem : ∀ x ∈ Set.uIcc θ (Real.pi / 2), x ∈ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [uIcc_of_le hle_pi] at hx
    exact ⟨by linarith [hx.1, hθ.1], by linarith [hx.2]⟩
  have hFTC : ∫ x in θ..Real.pi / 2, g' x = g (Real.pi / 2) - g θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (hmem x hx)) hint_g'
  have h1 : ‖g θ‖ = ‖∫ x in θ..Real.pi / 2, g' x‖ := by
    rw [hFTC, hgpi, zero_sub, norm_neg]
  have h2 : ‖∫ x in θ..Real.pi / 2, g' x‖ ≤ ∫ x in θ..Real.pi / 2, E * Real.cos x := by
    refine intervalIntegral.norm_integral_le_of_norm_le hle_pi ?_ hint_cos
    filter_upwards with t ht
    exact hbound t ⟨hθ.1.trans ht.1.le, ht.2⟩
  have h3 : ∫ x in θ..Real.pi / 2, E * Real.cos x = E * (1 - Real.sin θ) := by
    rw [intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi_div_two]
  rw [Real.norm_eq_abs] at h1
  linarith [h1 ▸ h2, h3 ▸ h2]

/-- **`ψ = u / cos` and `ψ'` are bounded on the whole open interval `(0, π/2)`** (self-contained
version), for `u` of class `C²` on the open neighbourhood `(-1, π/2 + 1)` of `[0, π/2]` with
`u (π/2) = 0`.

NOTE for the prover: please prove this ENTIRELY inside this file (helper lemmas above it are
welcome, with any names).  In particular do NOT import modules that contain `sorry` — avoid
`Submission.Work.FTS.EllipticEst.TanTheta.psi_hasDerivAt`,
`Submission.Work.FTS.EllipticEst.TanTheta.gfun_cos_bound` and
`Submission.Work.FTS.EllipticEst.TanTheta.exists_bounds_derivs` (they are stubs).  The only
imports you need are `Mathlib` and
`Submission.Work.FTS.EllipticEst.TanTheta.Basic` (which supplies `psi`), plus — if you wish —
the already proved and `sorry`-free `Submission.Work.FTS.EllipticEst.TanTheta.psi_deriv_formula`
and `Submission.Work.FTS.EllipticEst.TanTheta.psi_contdiff`.  Your `#print axioms` must be
`[propext, Classical.choice, Quot.sound]`.

Route.  `hu` is `C²` on an open set containing the compact interval `[0, π/2]`, so
`u`, `deriv u`, `deriv (deriv u)` are bounded on `[0, π/2]` by some `M0, M1, M2`
(`IsCompact.exists_bound_of_continuousOn`, using `hu.continuousOn` and its restrictions to the
derivatives).
Write `g θ = deriv u θ * cos θ + u θ * sin θ`; then `ψ' θ = g θ / cos θ ^ 2` on `(0, π/2)`
(`psi_deriv_formula`) and `g' θ = (deriv (deriv u) θ + u θ) * cos θ`, so with `E = M2 + M0`
one has `|g'| ≤ E cos θ` on the interval and `g (π/2) = 0` (because `u (π/2) = 0` and
`cos (π/2) = 0`).  Hence `|g θ| ≤ E (1 - sin θ)` for `θ ∈ [0, π/2]`
(`norm_image_sub_le_of_norm_deriv_le_segment'`, or the FTC), and since
`(1 - sin θ) / cos θ ^ 2 = 1 / (1 + sin θ) ≤ 1`, `|ψ' θ| ≤ E` there.
Similarly `u (π/2) = 0` gives `|u θ| ≤ M1 (π/2 - θ)`, hence `|ψ θ| ≤ 2 M1` for
`θ ≥ π/4`; for `θ ≤ π/4` both `u` and `g` are bounded by `M0`, `M0 + M1` and
`cos θ ≥ √2 / 2`.  Take `C = max` of the finitely many constants. -/
theorem psi_bounds_sc (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖Work.FTS.EllipticEst.TanTheta.psi u θ‖ ≤ C
        ∧ ‖deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ‖ ≤ C := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := pi_half_pos
  have hs : IsOpen (Set.Ioo (-1) (Real.pi / 2 + 1)) := isOpen_Ioo
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_refl 0, le_of_lt hpi2⟩
  -- smoothness of the two derivatives on the open neighbourhood
  have hderiv1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hu.deriv_of_isOpen hs (m := 1) (by norm_num)
  have hderiv2 : ContDiffOn ℝ 0 (deriv (deriv u)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hderiv1.deriv_of_isOpen hs (m := 0) (by norm_num)
  -- bounds on the compact interval
  obtain ⟨M0, hM0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hu.continuousOn.mono hsub)
  obtain ⟨M1, hM1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hderiv1.continuousOn.mono hsub)
  obtain ⟨M2, hM2⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hderiv2.continuousOn.mono hsub)
  have hM0' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |u x| ≤ M0 := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hM0 x hx
  have hM1' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv u x| ≤ M1 := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hM1 x hx
  have hM2' : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv u) x| ≤ M2 := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hM2 x hx
  have hM0nn : 0 ≤ M0 := (abs_nonneg (u 0)).trans (hM0' 0 h0mem)
  have hM1nn : 0 ≤ M1 := (abs_nonneg (deriv u 0)).trans (hM1' 0 h0mem)
  have hM2nn : 0 ≤ M2 := (abs_nonneg (deriv (deriv u) 0)).trans (hM2' 0 h0mem)
  set E : ℝ := M2 + M0 with hE
  have hEnn : 0 ≤ E := by rw [hE]; linarith [hM0nn, hM2nn]
  -- *first claim*: `|g| ≤ E (1 - sin)` on `[0, π/2]` for `g θ = u' θ cos θ + u θ sin θ`
  have hgcont' : ContinuousOn (fun x => (deriv (deriv u) x + u x) * Real.cos x)
      (Set.Icc 0 (Real.pi / 2)) :=
    ((hderiv2.continuousOn.mono hsub).add (hu.continuousOn.mono hsub)).mul
      Real.continuous_cos.continuousOn
  have hgbound : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ‖(deriv (deriv u) x + u x) * Real.cos x‖ ≤ E * Real.cos x := by
    intro x hx
    have hcos : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos],
        by linarith [hx.2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcos, hE]
    exact mul_le_mul_of_nonneg_right
      (calc |deriv (deriv u) x + u x| ≤ |deriv (deriv u) x| + |u x| := abs_add_le _ _
        _ ≤ M2 + M0 := add_le_add (hM2' x hx) (hM0' x hx)) hcos
  have hgpi : (fun θ => deriv u θ * Real.cos θ + u θ * Real.sin θ) (Real.pi / 2) = 0 := by
    simp [Real.cos_pi_div_two, hu1]
  have hgabs : ∀ θ ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ E * (1 - Real.sin θ) :=
    abs_le_of_hasDerivAt_le _ _ hgcont' (fun x hx => hasDerivAt_gfun u hu hx) hgbound hgpi
  -- *the `ψ'` bound*
  have hpsi' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ‖ ≤ E := by
    intro θ hθ
    rw [psi_deriv_formula u hu hθ]
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos2 : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcos
    have hgθ := hgabs θ ⟨le_of_lt hθ.1, hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hle : 1 - Real.sin θ ≤ Real.cos θ ^ 2 := by
      have h := Real.cos_sq_add_sin_sq θ
      nlinarith [hsin0, hsin1]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hcos2, div_le_iff₀ hcos2]
    calc |deriv u θ * Real.cos θ + u θ * Real.sin θ| ≤ E * (1 - Real.sin θ) := hgθ
      _ ≤ E * Real.cos θ ^ 2 := mul_le_mul_of_nonneg_left hle hEnn
  -- *the `ψ` bound*
  have hu_bound : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ M1 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hs' : IsOpen (Set.Ioo (-1) (Real.pi / 2 + 1)) := isOpen_Ioo
    have hdiff : ∀ x ∈ Set.Ioo (-1) (Real.pi / 2 + 1), HasDerivAt u (deriv u x) x := fun x hx =>
      (hu.differentiableOn (by norm_num)).differentiableAt (hs'.mem_nhds hx) |>.hasDerivAt
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := θ) (b := Real.pi / 2) (f := u)
      (f' := deriv u) (C := M1)
      (fun x hx => (hdiff x ⟨by linarith [hx.1, hθ.1], by linarith [hx.2]⟩).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hM1' x ⟨by linarith [hx.1, hθ.1], le_of_lt hx.2⟩)
      (Real.pi / 2) ⟨hθ.2, le_rfl⟩
    rw [hu1, zero_sub, norm_neg, Real.norm_eq_abs] at h
    exact h
  have hpsi : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖Work.FTS.EllipticEst.TanTheta.psi u θ‖ ≤ (Real.pi / 2) * M1 := by
    intro θ hθ
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have htpi : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have hsin : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (Real.pi / 2 - θ) :=
      Real.mul_le_sin ht0 htpi
    have hsin_eq : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
    have ht_le : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
      have hmult := mul_le_mul_of_nonneg_left hsin (le_of_lt Real.pi_pos)
      have h3 : Real.pi * ((2 / Real.pi) * (Real.pi / 2 - θ)) = 2 * (Real.pi / 2 - θ) := by
        field_simp
      rw [h3] at hmult
      rw [hsin_eq] at hmult
      linarith
    have huθ := hu_bound θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    show ‖u θ / Real.cos θ‖ ≤ (Real.pi / 2) * M1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
    calc |u θ| ≤ M1 * (Real.pi / 2 - θ) := huθ
      _ ≤ M1 * ((Real.pi / 2) * Real.cos θ) := mul_le_mul_of_nonneg_left ht_le hM1nn
      _ = (Real.pi / 2) * M1 * Real.cos θ := by ring
  exact ⟨max E ((Real.pi / 2) * M1), hEnn.trans (le_max_left _ _),
    fun θ hθ => ⟨(hpsi θ hθ).trans (le_max_right _ _), (hpsi' θ hθ).trans (le_max_left _ _)⟩⟩

end Work.FTS.EllipticEst.TanTheta
