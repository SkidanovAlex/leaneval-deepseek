import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.exists_saddleCoord

/-!
# The orbit invariant of the chart model ODE

In a Morse chart of a saddle, `f = c + chartQ (φ ·) s₁ s₂` with `s₁ + s₂ = 0`, and the chart
coordinates `u = φ (x ·)` of a flow line of the model field solve the model ODE

    u₀' = β (‖u‖²) · (s₁ · u₀),     u₁' = β (‖u‖²) · (s₂ · u₁)

(`chartVel`, and the `chartODE` clause of `Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE`).

This file proves the two invariants of that ODE which the *seam* of the saddle window consumes:

* the product `u₀ · u₁` is constant along a solution (because `s₁ + s₂ = 0`), i.e. `Im (Z ·)²` is
  constant, and `Re (Z ·)²` moves at the rate `β`;
* consequently the model `saddlePsi η δ` — whose square is a function of `Im z²` on its collar — is
  **constant along the flow lines** of the model field, which is what makes the picture of the anchor
  level well defined at the interface (`Work.Drive.N2.collarConstancy_of_sq_depends_on_im`).

The last theorem is stated for any flow `Φ` satisfying the `chartODE` clause on a chart source; it is
the exact form in which `Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE` supplies it.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

/-- **The product invariant of the chart model ODE.**  If the two chart coordinates of a curve solve
the model ODE with multiplier `β` and signs `s₁, s₂` at the parameter `t`, then the product of the
coordinates has derivative `(u₀ u₁) · β (‖u‖²) · (s₁ + s₂)` there. -/
theorem hasDerivAt_prod_of_chartODE {w : ℝ → EuclideanSpace ℝ (Fin 2)} {β : ℝ → ℝ} {s₁ s₂ t : ℝ}
    (h0 : HasDerivAt (fun σ => w σ 0) (β (‖w t‖ ^ 2) * (s₁ * w t 0)) t)
    (h1 : HasDerivAt (fun σ => w σ 1) (β (‖w t‖ ^ 2) * (s₂ * w t 1)) t) :
    HasDerivAt (fun σ => w σ 0 * w σ 1) ((w t 0 * w t 1) * β (‖w t‖ ^ 2) * (s₁ + s₂)) t := by
  have h := h0.mul h1
  rw [show (β (‖w t‖ ^ 2) * (s₁ * w t 0)) * (w t 1)
        + (w t 0) * (β (‖w t‖ ^ 2) * (s₂ * w t 1))
      = (w t 0 * w t 1) * β (‖w t‖ ^ 2) * (s₁ + s₂) from by ring] at h
  exact h

/-- **The product is constant along a solution of the model ODE in the saddle sign convention.** -/
theorem prod_eq_of_chartODE {w : ℝ → EuclideanSpace ℝ (Fin 2)} {β : ℝ → ℝ} {s₁ s₂ : ℝ}
    (hs : s₁ + s₂ = 0) {a b : ℝ}
    (h : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun σ => w σ 0) (β (‖w t‖ ^ 2) * (s₁ * w t 0)) t ∧
      HasDerivAt (fun σ => w σ 1) (β (‖w t‖ ^ 2) * (s₂ * w t 1)) t) :
    w b 0 * w b 1 = w a 0 * w a 1 := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun σ => w σ 0 * w σ 1) 0 t := by
    intro t ht
    have hp := hasDerivAt_prod_of_chartODE (h t ht).1 (h t ht).2
    simpa only [hs, mul_zero] using hp
  have hdiff : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ (fun σ => w σ 0 * w σ 1) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hbound : ∀ t ∈ Set.uIcc a b, ‖deriv (fun σ => w σ 0 * w σ 1) t‖ ≤ 0 :=
    fun t ht => by rw [(hderiv t ht).deriv, norm_zero]
  have ha : a ∈ Set.uIcc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  have hb : b ∈ Set.uIcc a b := ⟨min_le_right _ _, le_max_right _ _⟩
  have hle := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hdiff hbound
    (convex_uIcc a b) ha hb
  rw [zero_mul] at hle
  have hzero : (fun σ => w σ 0 * w σ 1) b - (fun σ => w σ 0 * w σ 1) a = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp hzero

/-- The square of the complex chart coordinate is computed from the two real coordinates:
`((a : ℂ) + (b : ℂ) * I)² = (a² - b²) + 2ab i`. -/
theorem im_sq_complex_of_two (a b : ℝ) : (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2).im = 2 * a * b := by
  rw [pow_two]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **`Im (Z ·)²` is constant along a solution of the model ODE in the saddle sign convention.** -/
theorem im_sq_eq_of_chartODE {w : ℝ → EuclideanSpace ℝ (Fin 2)} {β : ℝ → ℝ} {s₁ s₂ : ℝ}
    (hs : s₁ + s₂ = 0) {a b : ℝ}
    (h : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun σ => w σ 0) (β (‖w t‖ ^ 2) * (s₁ * w t 0)) t ∧
      HasDerivAt (fun σ => w σ 1) (β (‖w t‖ ^ 2) * (s₂ * w t 1)) t) :
    (((w b 0 : ℂ) + (w b 1 : ℂ) * Complex.I) ^ 2).im
      = (((w a 0 : ℂ) + (w a 1 : ℂ) * Complex.I) ^ 2).im := by
  rw [im_sq_complex_of_two, im_sq_complex_of_two,
    show (2 : ℝ) * (w b 0) * (w b 1) = 2 * (w b 0 * w b 1) from by ring,
    show (2 : ℝ) * (w a 0) * (w a 1) = 2 * (w a 0 * w a 1) from by ring,
    prod_eq_of_chartODE hs h]

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- **The orbit invariant, packaged for a flow satisfying the chart ODE clause.**

Let `Φ` be a flow whose chart coordinates on the source of a saddle chart `φ` solve the model ODE
with the sign convention `s₁ = 1`, `s₂ = -1` and multiplier `chartMult r` (this is exactly the
`chartODE` clause produced by `Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE`), and let
`Z x = φ x 0 + i · φ x 1` be the corresponding complex coordinate.  Then along the trajectory of a
point `y` that stays in the chart source between the parameters `0` and `t`, the quantity
`Im (Z ·)²` is preserved. -/
theorem im_sq_eq_of_flow_chartODE
    (Φ : ℝ × M → M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (Z : M → ℂ) (hZ : ∀ m : M, Z m = (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I)
    (r : ℝ)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ φ.source) →
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (t, y)) 1)) t)
    (hΦ0 : ∀ m : M, Φ (0, m) = m)
    (y : M) (t : ℝ) (hconf : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ φ.source) :
    ((Z (Φ (t, y))) ^ 2).im = ((Z y) ^ 2).im := by
  have hmain : ∀ τ ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (τ, y)) 0)) τ ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (τ, y)) 1)) τ := by
    intro τ hτ
    refine hODE y τ ?_
    intro u hu
    exact hconf u (by
      have h1 : Set.Icc (min 0 τ) (max 0 τ) ⊆ Set.Icc (min 0 t) (max 0 t) := by
        intro s hs
        obtain ⟨hs1, hs2⟩ := hs
        obtain ⟨hτ1, hτ2⟩ := hτ
        constructor
        · rcases le_total 0 τ with h | h
          · rw [min_eq_left h] at hs1
            linarith [min_le_left (0 : ℝ) t]
          · rw [min_eq_right h] at hs1
            linarith [min_le_left (0 : ℝ) t]
        · rcases le_total 0 τ with h | h
          · rw [max_eq_right h] at hs2
            linarith [le_max_right (0 : ℝ) t]
          · rw [max_eq_left h] at hs2
            exact le_trans hs2 (le_max_left (0 : ℝ) t)
      exact h1 hu)
  have hprod := im_sq_eq_of_chartODE (w := fun σ : ℝ => φ (Φ (σ, y))) (β := chartMult r)
    (s₁ := 1) (s₂ := -1) (by norm_num) hmain
  rw [hΦ0 y] at hprod
  have h1 : Z (Φ (t, y)) = (φ (Φ (t, y)) 0 : ℂ) + (φ (Φ (t, y)) 1 : ℂ) * Complex.I := hZ _
  have h2 : Z y = (φ y 0 : ℂ) + (φ y 1 : ℂ) * Complex.I := by rw [← hΦ0 y]; exact hZ _
  rw [h1, h2]
  exact hprod

end Work.Drive.N2
