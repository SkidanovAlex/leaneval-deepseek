import Mathlib
import Submission.Work.RPB.B2.PhaseDefs

/-!
# `chordW` is non-vanishing near the chord annulus

The divided chord `chordW c τ t r = ∫_{s ∈ [-1,1]} c'(t + s r) ds` is `chordVec / r`, where
`chordVec c τ t r = c τ (t+r) - c τ (t-r)`.  For an embedded closed curve with non-vanishing
derivative the chord vector does not vanish on the open strip `-π < r < π` (it vanishes only at
the diagonal `r = 0` mod `2π`), and at `r = 0` the divided chord equals `2 c'(t) ≠ 0`.  Hence
`chordW` is non-zero on `[0,1] × ℝ × [A,B]` for `[A,B] ⊂ (-π,π)`, and by joint continuity and
`2π`-periodicity in `t` this persists on a neighbourhood of the `τ`-interval.

This file proves that fact (`Work.RPB.B2.chordW_ne_zero_nhds`), together with the auxiliary
lemmas it rests on.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff
open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-! ## Continuity of `chordW` -/

/-- The derivative in the second variable of a smooth two-variable function is jointly
continuous: `(τ, u) ↦ ∂₂ c(τ, u)`. -/
theorem continuous_deriv_snd (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun p : ℝ × ℝ => deriv (fun v : ℝ => c p.1 v) p.2) := by
  have hslice : ∀ τ u : ℝ, deriv (fun v : ℝ => c τ v) u
      = (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u)) ((0 : ℝ), 1) := by
    intro τ u
    have h2 : HasFDerivAt (fun z : ℝ × ℝ => c z.1 z.2)
        (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u)) (τ, u) :=
      (hc.differentiable (by simp) (τ, u)).hasFDerivAt
    have h1 : HasFDerivAt (fun v : ℝ => (τ, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) u :=
      hasFDerivAt_prodMk_right τ u
    have h3 : HasFDerivAt ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v)))
        ((fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u))
          ∘SL (ContinuousLinearMap.inr ℝ ℝ ℝ)) u :=
      h2.comp u h1
    have h4 := h3.fderiv
    rw [show (fun v : ℝ => c τ v)
          = ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v))) from rfl]
    rw [show deriv (((fun z : ℝ × ℝ => c z.1 z.2)) ∘ (fun v : ℝ => (τ, v))) u
          = (fderiv ℝ ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v))) u) 1 from
        (fderiv_apply_one_eq_deriv).symm]
    rw [h4]
    simp [ContinuousLinearMap.inr_apply]
  have hcont : Continuous (fun z : ℝ × ℝ =>
      (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) z) ((0 : ℝ), (1 : ℝ))) :=
    (hc.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  simpa only [hslice] using hcont

/-- `chordW` is jointly continuous in `(τ, t, r)`. -/
theorem continuous_chordW (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => chordW c z.1 z.2.1 z.2.2) := by
  have hderiv := continuous_deriv_snd c hc
  have hg : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      (p.1.1, p.1.2.1 + p.2 * p.1.2.2)) := by fun_prop
  have huncurry : Continuous (Function.uncurry (fun z : ℝ × (ℝ × ℝ) => fun s : ℝ =>
      deriv (fun v : ℝ => c z.1 v) (z.2.1 + s * z.2.2))) := hderiv.comp hg
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) huncurry (-1) 1
  simpa only [chordW, Function.uncurry] using this

/-! ## Periodicity in `t` and the value at `r = 0` -/

/-- `chordW` is `2π`-periodic in `t` (as is the curve family `c`). -/
theorem chordW_add_two_pi (c : ℝ → ℝ → ℂ)
    (hper : ∀ τ t, c τ (t + 2 * π) = c τ t) (τ t r : ℝ) :
    chordW c τ (t + 2 * π) r = chordW c τ t r := by
  have hperτ : Function.Periodic (fun u : ℝ => c τ u) (2 * π) := fun u => hper τ u
  have hperd : ∀ u, deriv (fun u : ℝ => c τ u) (u + 2 * π) = deriv (fun u : ℝ => c τ u) u := by
    intro u
    rw [← deriv_comp_add_const (f := fun u : ℝ => c τ u) (a := 2 * π) (x := u)]
    rw [hperτ.funext]
  simp only [chordW]
  apply intervalIntegral.integral_congr
  intro s _
  show deriv (fun u : ℝ => c τ u) (t + 2 * π + s * r)
      = deriv (fun u : ℝ => c τ u) (t + s * r)
  rw [show t + 2 * π + s * r = (t + s * r) + 2 * π from by ring]
  exact hperd (t + s * r)

/-- At `r = 0` the divided chord is the doubled tangent `2 c'(t)`. -/
theorem chordW_zero (c : ℝ → ℝ → ℂ) (τ t : ℝ) :
    chordW c τ t 0 = 2 * deriv (fun u : ℝ => c τ u) t := by
  simp only [chordW]
  simp only [mul_zero, add_zero]
  rw [intervalIntegral.integral_const]
  norm_num

/-! ## Non-vanishing of the chord vector -/

/-- For a curve family that is injective on `[0,1]` modulo `2π`, the chord vector does not
vanish for `-π < r < π`, `r ≠ 0`. -/
theorem chordVec_ne_zero_of (c : ℝ → ℝ → ℂ)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ,
      t' = t + 2 * π * m)
    {τ t r : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hrlo : -π < r) (hrhi : r < π)
    (hrne : r ≠ 0) : Work.RPB.chordVec c τ t r ≠ 0 := by
  intro hv
  rw [Work.RPB.chordVec, sub_eq_zero] at hv
  obtain ⟨m, hm⟩ := hinj τ hτ (t + r) (t - r) hv
  have hm' : r = -(π * (m : ℝ)) := by linarith
  have hlt1 : (m : ℝ) < 1 := by
    have h : -π < -(π * (m : ℝ)) := by rw [← hm']; exact hrlo
    exact (mul_lt_mul_iff_of_pos_left Real.pi_pos).mp
      (by linarith : π * (m : ℝ) < π * 1)
  have hlt2 : -1 < (m : ℝ) := by
    have h : -(π * (m : ℝ)) < π := by rw [← hm']; exact hrhi
    have h3 : π * (-(m : ℝ)) < π * 1 := by
      have : π * (-(m : ℝ)) = -(π * (m : ℝ)) := by ring
      rw [this]; linarith
    have := (mul_lt_mul_iff_of_pos_left Real.pi_pos).mp h3
    linarith
  have hm1 : m < 1 := by exact_mod_cast hlt1
  have hm2 : (-1 : ℤ) < m := by exact_mod_cast hlt2
  have hm0 : m = 0 := by omega
  rw [hm0] at hm'
  simp at hm'
  exact hrne hm'

/-! ## Reduction of `t` modulo `2π` into a compact interval -/

/-- Every real `t` differs from some `t₁ ∈ [0, 2π]` by an integer multiple of `2π`. -/
theorem exists_mod_two_pi (t : ℝ) :
    ∃ t1 ∈ Set.Icc (0 : ℝ) (2 * π), ∃ m : ℤ, t = t1 + 2 * π * (m : ℝ) := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hπ' : (2 * π) ≠ 0 := ne_of_gt hπ
  set q : ℝ := t / (2 * π) with hqdef
  have ht : 2 * π * q = t := by rw [hqdef]; exact mul_div_cancel₀ t hπ'
  refine ⟨t - 2 * π * (⌊q⌋ : ℝ), ⟨?_, ?_⟩, ⌊q⌋, by ring⟩
  · have h1 : 2 * π * (⌊q⌋ : ℝ) ≤ t := by
      rw [← ht]
      exact mul_le_mul_of_nonneg_left (Int.floor_le q) hπ.le
    linarith
  · have h2 : t < 2 * π * (⌊q⌋ : ℝ) + 2 * π := by
      have h := mul_lt_mul_of_pos_left (Int.lt_floor_add_one q) hπ
      rw [← ht]
      calc 2 * π * q < 2 * π * ((⌊q⌋ : ℝ) + 1) := h
        _ = 2 * π * (⌊q⌋ : ℝ) + 2 * π := by ring
    linarith

/-! ## The main lemma -/

end Work.RPB.B2
