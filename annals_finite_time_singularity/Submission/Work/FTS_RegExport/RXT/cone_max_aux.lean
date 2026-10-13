import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary real-analysis lemmas for `cone_max_principle`

Helpers for the cone maximum principle for a first-order transport equation with bounded
coefficients (`Work.FTS_RegExport.RXT.cone_max_principle`).
-/

namespace Work.FTS_RegExport.RXT

namespace ConeAux

/-- `(1-u) * exp (2u) ≥ 1` for `u ∈ [0, 1/2]`. -/
lemma one_le_one_sub_mul_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    1 ≤ (1 - u) * Real.exp (2 * u) := by
  have hexp : 2 * u + 1 ≤ Real.exp (2 * u) := Real.add_one_le_exp (2 * u)
  have h1u : 0 ≤ 1 - u := by linarith
  have h2 : (1 - u) * (2 * u + 1) ≤ (1 - u) * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left hexp h1u
  have h3 : 1 ≤ (1 - u) * (2 * u + 1) := by nlinarith
  linarith

/-- `1/(1-u) ≤ exp (2u)` for `u ∈ [0, 1/2]`. -/
lemma div_one_sub_le_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    1 / (1 - u) ≤ Real.exp (2 * u) := by
  have h : (1:ℝ) ≤ (1 - u) * Real.exp (2 * u) := one_le_one_sub_mul_exp h0 h1
  have hpos : (0:ℝ) < 1 - u := by linarith
  rw [div_le_iff₀ hpos]
  linarith [mul_comm (Real.exp (2*u)) (1-u)]

/-- Arithmetic core of the recursion: from the one-step inequality
`B ≤ M + h·Fη + h·C·B` one gets the value of the discrete scheme at the next time. -/
lemma key_step {K₀ Fη C B h kh : ℝ} (hK₀ : 0 ≤ K₀) (hFη : 0 ≤ Fη) (hC : 0 ≤ C)
    (hkh : 0 ≤ kh) (hh : 0 ≤ h) (hCh : C * h ≤ 1 / 2)
    (haux : B ≤ Real.exp (2 * C * kh) * (K₀ + kh * Fη) + h * Fη + h * C * B) :
    B ≤ Real.exp (2 * C * (kh + h)) * (K₀ + (kh + h) * Fη) := by
  set X : ℝ := Real.exp (2 * C * kh) * (K₀ + kh * Fη) + h * Fη with hX
  have haux' : B ≤ X + h * C * B := by rw [hX]; exact haux
  have h1 : B * (1 - C * h) ≤ X := by nlinarith [haux']
  have hpos : (0:ℝ) < 1 - C * h := by linarith
  have hCh0 : 0 ≤ C * h := mul_nonneg hC hh
  have h3 : (1 - C * h)⁻¹ ≤ Real.exp (2 * (C * h)) := by
    simpa [one_div] using div_one_sub_le_exp hCh0 hCh
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have h4 : B ≤ X * (1 - C * h)⁻¹ := by
    have h4' : B ≤ X / (1 - C * h) := by rw [le_div_iff₀ hpos]; exact h1
    rwa [div_eq_mul_inv] at h4'
  have h5 : X * (1 - C * h)⁻¹ ≤ X * Real.exp (2 * (C * h)) :=
    mul_le_mul_of_nonneg_left h3 hX0
  have h6 : X * Real.exp (2 * (C * h))
      ≤ Real.exp (2 * C * kh) * Real.exp (2 * (C * h)) * (K₀ + (kh + h) * Fη) := by
    have hexp1 : (1:ℝ) ≤ Real.exp (2 * C * kh) := Real.one_le_exp (by nlinarith)
    have hFη' : 0 ≤ h * Fη := mul_nonneg hh hFη
    have hkey2 : h * Fη ≤ Real.exp (2 * C * kh) * (h * Fη) := by
      simpa using mul_le_mul_of_nonneg_right hexp1 hFη'
    have hsum : K₀ + (kh + h) * Fη = (K₀ + kh * Fη) + h * Fη := by ring
    rw [hX, hsum]
    nlinarith [mul_le_mul_of_nonneg_left hkey2 (le_of_lt (Real.exp_pos (2 * (C * h)))),
      Real.exp_pos (2 * (C * h)), Real.exp_pos (2 * C * kh), hK₀,
      mul_nonneg hkh hFη]
  have hexpEq : Real.exp (2 * C * (kh + h))
      = Real.exp (2 * C * kh) * Real.exp (2 * (C * h)) := by
    rw [show 2 * C * (kh + h) = 2 * C * kh + 2 * (C * h) by ring, Real.exp_add]
  rw [hexpEq]
  linarith [h4, h5, h6]

/-- `|a+b+c+d| ≤ |a|+|b|+|c|+|d|`. -/
lemma abs_add4_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- Mean value theorem in slope form, with an explicit derivative. -/
lemma mvt_slope {f fs : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (fs x) x) :
    ∃ c ∈ Set.Ioo a b, f b - f a = fs c * (b - a) := by
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope f fs hab hc hd
  refine ⟨c, hc1, ?_⟩
  rw [hc2]
  rw [div_mul_cancel₀]
  exact ne_of_gt (sub_pos.mpr hab)

/-- Mean-value bound with a frozen derivative: the increment of `g` between `a'` and `a`,
minus `(a - a')·C₁`, is controlled by `C₂·|a - a'|`. -/
lemma mvt_diff_bound {g gs : ℝ → ℝ} {a a' C₁ C₂ : ℝ}
    (hcont : ContinuousOn g (Set.Icc (min a a') (max a a')))
    (hderiv : ∀ s, HasDerivAt g (gs s) s)
    (hbd : ∀ l ∈ Set.Icc (min a a') (max a a'), |gs l - C₁| ≤ C₂) :
    |g a - g a' - (a - a') * C₁| ≤ C₂ * |a - a'| := by
  have key : ∀ c ∈ Set.Ioo (min a a') (max a a'),
      g a - g a' = gs c * (a - a') →
      |g a - g a' - (a - a') * C₁| ≤ C₂ * |a - a'| := by
    intro c hc hceq
    rw [hceq]
    have h1 : gs c * (a - a') - (a - a') * C₁ = (gs c - C₁) * (a - a') := by ring
    rw [h1, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbd c ⟨le_of_lt hc.1, le_of_lt hc.2⟩) (abs_nonneg _)
  rcases lt_trichotomy a a' with h | h | h
  · have := mvt_slope (f := g) (fs := gs)
      h (by simpa [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using hcont)
      (fun x _ => hderiv x)
    obtain ⟨c, hc, hceq⟩ := this
    exact key c (by simpa [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using hc)
      (by linarith)
  · subst h
    simp
  · have h' : a' < a := h
    have := mvt_slope (f := g) (fs := gs)
      h' (by simpa [min_eq_right (le_of_lt h'), max_eq_left (le_of_lt h')] using hcont)
      (fun x _ => hderiv x)
    obtain ⟨c, hc, hceq⟩ := this
    refine key c (by simpa [min_eq_right (le_of_lt h'), max_eq_left (le_of_lt h')] using hc) ?_
    linarith

/-- Distance estimate inside the box: if both spatial coordinates move by at most `dep·A`
and the time coordinate by at most `dep`, with `dep ≤ h`, then the distance of the
corresponding points of `ℝ × ℝ × ℝ` is at most `(A+1)·h`. -/
lemma dist_three_le {A h dep l₁ l₂ q₁ q₂ τ τ' : ℝ} (hA : 0 ≤ A) (hh : 0 < h)
    (hdep : dep ≤ h) (hl₁ : |l₁ - q₁| ≤ dep * A) (hl₂ : |l₂ - q₂| ≤ dep * A)
    (hτ : |τ - τ'| ≤ dep) :
    dist (l₁, l₂, τ) (q₁, q₂, τ') ≤ (A + 1) * h := by
  have h1 : dist (l₁, l₂, τ) (q₁, q₂, τ') = max |l₁ - q₁| (max |l₂ - q₂| |τ - τ'|) := by
    simp [Prod.dist_eq, Real.dist_eq]
  rw [h1, max_le_iff]
  refine ⟨le_trans hl₁ (by nlinarith), ?_⟩
  rw [max_le_iff]
  exact ⟨le_trans hl₂ (by nlinarith), le_trans hτ (by nlinarith)⟩

/-- The `η`-terms of a step: `2·(d·A·(η/(2(A+1)))) ≤ d·η`. -/
lemma two_mul_div_le {A η d : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η) (hd : 0 ≤ d) :
    2 * (d * A * (η / (2 * (A + 1)))) ≤ d * η := by
  have hA1 : (0:ℝ) < A + 1 := by linarith
  have hEq : 2 * (d * A * (η / (2 * (A + 1)))) = d * (A * η) / (A + 1) := by
    field_simp
  rw [hEq, div_le_iff₀ hA1]
  nlinarith

/-- Backward transport: a point that has moved by `dep·A` from a point `q` of the cone at
level `kh + h` still lies in the cone at level `kh`. -/
lemma cone_shift {A dep gap τ₀ kh l q s₀ : ℝ} (hA : 0 ≤ A) (hgap : dep + gap ≤ τ₀ - kh)
    (hl : |l - q| ≤ dep * A) (hq : |q - s₀| ≤ A * gap) :
    |l - s₀| ≤ A * (τ₀ - kh) := by
  have hsub : |l - s₀| ≤ |l - q| + |q - s₀| := by
    rw [show l - s₀ = (l - q) + (q - s₀) by ring]
    exact abs_add_le _ _
  have h4 : dep * A + A * gap ≤ A * (τ₀ - kh) := by
    have hh := mul_le_mul_of_nonneg_left hgap hA
    have hh2 : A * (dep + gap) = dep * A + A * gap := by ring
    linarith [hh, hh2]
  linarith [hsub, hl, hq, h4]

end ConeAux

end Work.FTS_RegExport.RXT
