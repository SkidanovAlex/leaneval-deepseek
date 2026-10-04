import Mathlib
import Submission.Commons.Geometry.Sphere.modelDist_cos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Commons.Geometry.Sphere

/-- The trigonometric identity behind the hinge step (the law of cosines for the "extended"
triangle): with `C = cos t cos s₁ + sin t sin s₁ cos θ`, for `sin s₁ ≠ 0`,
`cos t cos(s₁+s₂) + sin t sin(s₁+s₂) cos θ = C cos s₂ - ((cos t - C cos s₁)/sin s₁) sin s₂`. -/
lemma cos_hinge_identity (t s₁ s₂ θ : ℝ) (hs : Real.sin s₁ ≠ 0) :
    Real.cos t * Real.cos (s₁ + s₂) + Real.sin t * Real.sin (s₁ + s₂) * Real.cos θ
      = (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₂
        - ((Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ)
            * Real.cos s₁) / Real.sin s₁) * Real.sin s₂ := by
  have key :
      Real.sin s₁ * (Real.cos t * Real.cos (s₁ + s₂) + Real.sin t * Real.sin (s₁ + s₂) * Real.cos θ)
        = Real.sin s₁ * ((Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₂)
          - (Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₁)
              * Real.sin s₂ := by
    rw [Real.cos_add, Real.sin_add]
    linear_combination (-(Real.cos t * Real.sin s₂)) * Real.sin_sq_add_cos_sq s₁
  have h2 :
      Real.sin s₁ * ((((Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ)
              * Real.cos s₁) / Real.sin s₁)) * Real.sin s₂)
        = (Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₁)
            * Real.sin s₂ := by
    field_simp
  have hrhs :
      Real.sin s₁ * ((Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₂
          - ((Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ)
              * Real.cos s₁) / Real.sin s₁) * Real.sin s₂)
        = Real.sin s₁ * ((Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₂)
          - (Real.cos t - (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ) * Real.cos s₁)
              * Real.sin s₂ := by
    rw [mul_sub, h2]
  exact mul_left_cancel₀ hs (key.trans hrhs.symm)

theorem modelDist_hinge_step {t s₁ s₂ w θ α' : ℝ}
    (ht : 0 < t) (htπ : t < Real.pi) (hs₁ : 0 < s₁) (hs₁π : s₁ < Real.pi)
    (hs₂ : 0 ≤ s₂) (hss : s₁ + s₂ ≤ Real.pi)
    (hw : 0 < w) (hwπ : w < Real.pi)
    (hwlo : |t - s₁| ≤ w) (hwhi : w ≤ t + s₁)
    (hts : t + s₁ ≤ Real.pi)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) (hα' : α' ∈ Set.Icc (0 : ℝ) Real.pi)
    (h1 : w ≤ Real.arccos (Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ))
    (h2 : t ≤ Real.arccos (Real.cos s₁ * Real.cos w + Real.sin s₁ * Real.sin w * Real.cos α')) :
    Real.arccos (Real.cos w * Real.cos s₂ + Real.sin w * Real.sin s₂ * Real.cos (Real.pi - α'))
      ≤ Real.arccos (Real.cos t * Real.cos (s₁ + s₂) + Real.sin t * Real.sin (s₁ + s₂) * Real.cos θ) := by
  set C := Real.cos t * Real.cos s₁ + Real.sin t * Real.sin s₁ * Real.cos θ with hC
  set D := Real.cos s₁ * Real.cos w + Real.sin s₁ * Real.sin w * Real.cos α' with hD
  have hsin1 : 0 < Real.sin s₁ := Real.sin_pos_of_pos_of_lt_pi hs₁ hs₁π
  have hsin1ne : Real.sin s₁ ≠ 0 := ne_of_gt hsin1
  have hs2le : s₂ ≤ Real.pi := by linarith
  have hsin2 : 0 ≤ Real.sin s₂ := Real.sin_nonneg_of_nonneg_of_le_pi hs₂ hs2le
  have hs12 : 0 ≤ s₁ + s₂ := by linarith
  have hsin12 : 0 ≤ Real.sin (s₁ + s₂) := Real.sin_nonneg_of_nonneg_of_le_pi hs12 hss
  -- `cos (arccos C) = C` and `cos (arccos D) = D`
  have hCcos : Real.cos (Real.arccos C) = C := by
    rw [hC]
    exact modelDist_cos (le_of_lt ht) (le_of_lt htπ) (le_of_lt hs₁) (le_of_lt hs₁π) hθ.1 hθ.2
  have hDcos : Real.cos (Real.arccos D) = D := by
    rw [hD]
    exact modelDist_cos (le_of_lt hs₁) (le_of_lt hs₁π) (le_of_lt hw) (le_of_lt hwπ) hα'.1 hα'.2
  -- `h1` gives `C ≤ cos w`
  have hCw : C ≤ Real.cos w := by
    have hmem_w : w ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hw, le_of_lt hwπ⟩
    have hmem_a : Real.arccos C ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg C, Real.arccos_le_pi C⟩
    have := Real.antitoneOn_cos hmem_w hmem_a h1
    rwa [hCcos] at this
  -- `h2` gives `D ≤ cos t`
  have hDt : D ≤ Real.cos t := by
    have hmem_t : t ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt ht, le_of_lt htπ⟩
    have hmem_a : Real.arccos D ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg D, Real.arccos_le_pi D⟩
    have := Real.antitoneOn_cos hmem_t hmem_a h2
    rwa [hDcos] at this
  have hDt' : Real.cos s₁ * Real.cos w + Real.sin s₁ * Real.sin w * Real.cos α' ≤ Real.cos t := by
    rw [hD] at hDt
    exact hDt
  have hwα : Real.sin w * Real.cos α' ≤ (Real.cos t - Real.cos s₁ * Real.cos w) / Real.sin s₁ := by
    rw [le_div_iff₀ hsin1]
    nlinarith [hDt']
  -- the main comparison of the two cosine expressions
  have hLR : Real.cos t * Real.cos (s₁ + s₂) + Real.sin t * Real.sin (s₁ + s₂) * Real.cos θ
      ≤ Real.cos w * Real.cos s₂ + Real.sin w * Real.sin s₂ * Real.cos (Real.pi - α') := by
    have hid := cos_hinge_identity t s₁ s₂ θ hsin1ne
    rw [← hC] at hid
    rw [hid, Real.cos_pi_sub]
    set U := (Real.cos t - Real.cos s₁ * Real.cos w) / Real.sin s₁ with hU
    have h1' : Real.sin w * Real.cos α' ≤ U := by rw [hU]; exact hwα
    have h2'' : Real.cos w * Real.cos s₂ - U * Real.sin s₂
        ≤ Real.cos w * Real.cos s₂ + Real.sin w * Real.sin s₂ * (-Real.cos α') := by
      have := mul_le_mul_of_nonneg_right h1' hsin2
      linarith
    have h3'' : C * Real.cos s₂ - ((Real.cos t - C * Real.cos s₁) / Real.sin s₁) * Real.sin s₂
        ≤ Real.cos w * Real.cos s₂ - U * Real.sin s₂ := by
      have hkey : (Real.cos w * Real.cos s₂ - U * Real.sin s₂)
            - (C * Real.cos s₂ - ((Real.cos t - C * Real.cos s₁) / Real.sin s₁) * Real.sin s₂)
          = (Real.cos w - C) * (Real.sin (s₁ + s₂) / Real.sin s₁) := by
        rw [hU, Real.sin_add]
        field_simp
        ring
      have hnn : 0 ≤ (Real.cos w - C) * (Real.sin (s₁ + s₂) / Real.sin s₁) :=
        mul_nonneg (by linarith) (div_nonneg hsin12 (le_of_lt hsin1))
      have h0 : 0 ≤ (Real.cos w * Real.cos s₂ - U * Real.sin s₂)
            - (C * Real.cos s₂ - ((Real.cos t - C * Real.cos s₁) / Real.sin s₁) * Real.sin s₂) := by
        rw [hkey]; exact hnn
      linarith
    linarith [h2'', h3'']
  exact Real.arccos_le_arccos hLR

end Commons.Geometry.Sphere
