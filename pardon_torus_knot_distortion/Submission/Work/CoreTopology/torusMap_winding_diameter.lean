import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.CoreTopology.essential_diameter_ge_two

/-!
# A curve on the standard torus with nonzero winding has diameter at least `2`

Let `t ↦ (Θ t, Φ t)` be a continuous path in the parameter plane of the standard
torus of revolution (major radius `2`, minor radius `1`), whose lift over one
period advances by the winding vector `(a, b) ∈ ℤ²`:

`Θ (2π) = Θ 0 + a·2π`, `Φ (2π) = Φ 0 + b·2π`.

If `(a, b) ≠ 0` — i.e. the parameter path represents an essential closed curve on
the torus — then two points of the curve

`t ↦ torusMap (Θ t) (Φ t) = ((2 + cos Φ t) cos Θ t, (2 + cos Φ t) sin Θ t, sin Φ t)`

are at Euclidean distance at least `2`.  The bound is sharp: the meridian circles
(`φ ≡ π/2`, resp. `φ ≡ -π/2` at distance exactly `2` from each other) show that
`2` cannot be improved.

The proof splits on the meridian component `b` of the winding vector.

* If `b ≠ 0`, the meridian angle sweeps an interval of length `≥ 2π` over one
  period, hence `sin Φ` takes both values `1` and `-1` at parameters `t₁`, `t₂`.
  The corresponding points have `z`-coordinates `±1`, so their distance is at
  least `2`.
* If `b = 0` then `a ≠ 0`, so the longitude angle sweeps an interval of length
  `≥ 2π` and hence takes two values differing by exactly `π` at parameters
  `t₁`, `t₂`.  At such a pair the `xy`-projections of the two points are opposite
  multiples of a unit vector with factors `2 + cos Φ t₁`, `2 + cos Φ t₂`, whose
  sum is at least `2`, again giving distance at least `2`.

The two "sweeping" facts are `exists_eq_shift_of_winding` and
`exists_eq_add_pi_of_winding` from `Submission.Work.CoreTopology.essential_diameter_ge_two`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

theorem torusMap_winding_diameter (Θ Φ : ℝ → ℝ) (hΘ : Continuous Θ) (hΦ : Continuous Φ)
    (a b : ℤ) (ha : Θ (2 * Real.pi) = Θ 0 + (a : ℝ) * (2 * Real.pi))
    (hb : Φ (2 * Real.pi) = Φ 0 + (b : ℝ) * (2 * Real.pi)) (h : (a, b) ≠ (0, 0)) :
    ∃ t₁ t₂ : ℝ,
      2 ≤ dist (Work.Core.torusMap (Θ t₁) (Φ t₁)) (Work.Core.torusMap (Θ t₂) (Φ t₂)) := by
  set γ : ℝ → R3 := fun t => Work.Core.torusMap (Θ t) (Φ t) with hγdef
  have hγt : ∀ t : ℝ, γ t = Work.Core.torusMap (Θ t) (Φ t) := fun t => by simp [hγdef]
  have hc0 : ∀ t : ℝ, γ t (0 : Fin 3) = (2 + Real.cos (Φ t)) * Real.cos (Θ t) := fun t => by
    rw [hγt t]; rfl
  have hc1 : ∀ t : ℝ, γ t (1 : Fin 3) = (2 + Real.cos (Φ t)) * Real.sin (Θ t) := fun t => by
    rw [hγt t]; rfl
  have hc2 : ∀ t : ℝ, γ t (2 : Fin 3) = Real.sin (Φ t) := fun t => by
    rw [hγt t]; rfl
  rcases eq_or_ne b 0 with hb0 | hbne
  · -- the meridian component of the winding vector vanishes, so the longitude
    -- component is nonzero and the longitude angle takes two values differing by `π`
    have ha_ne : a ≠ 0 := by
      intro ha0
      exact h (by simp [ha0, hb0])
    obtain ⟨t₁, t₂, hΘ⟩ := exists_eq_add_pi_of_winding Θ hΘ (m := a) ha_ne ha
    refine ⟨t₁, t₂, ?_⟩
    rw [dist_eq_norm]
    have hcos : Real.cos (Θ t₂) = -Real.cos (Θ t₁) := by rw [hΘ, Real.cos_add_pi]
    have hsin : Real.sin (Θ t₂) = -Real.sin (Θ t₁) := by rw [hΘ, Real.sin_add_pi]
    have hsq : ‖γ t₁ - γ t₂‖ ^ 2 = (4 + Real.cos (Φ t₁) + Real.cos (Φ t₂)) ^ 2
        + (Real.sin (Φ t₁) - Real.sin (Φ t₂)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hc0, hc1, hc2]
      rw [hcos, hsin]
      linear_combination ((4 + Real.cos (Φ t₁) + Real.cos (Φ t₂)) ^ 2)
        * Real.cos_sq_add_sin_sq (Θ t₁)
    have hD : 2 ≤ 4 + Real.cos (Φ t₁) + Real.cos (Φ t₂) := by
      linarith [Real.neg_one_le_cos (Φ t₁), Real.neg_one_le_cos (Φ t₂)]
    have hbig : 4 ≤ ‖γ t₁ - γ t₂‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (Real.sin (Φ t₁) - Real.sin (Φ t₂))]
    nlinarith [norm_nonneg (γ t₁ - γ t₂)]
  · -- the meridian component of the winding vector does not vanish: the height
    -- `sin Φ` takes the values `±1`
    obtain ⟨t₁, k₁, h₁⟩ := exists_eq_shift_of_winding Φ hΦ (m := b) hbne hb (Real.pi / 2)
    obtain ⟨t₂, k₂, h₂⟩ := exists_eq_shift_of_winding Φ hΦ (m := b) hbne hb (-(Real.pi / 2))
    have hs₁ : Real.sin (Φ t₁) = 1 := by
      rw [h₁, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
    have hs₂ : Real.sin (Φ t₂) = -1 := by
      rw [h₂, Real.sin_add_int_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
    refine ⟨t₁, t₂, ?_⟩
    rw [dist_eq_norm]
    have hsq : ‖γ t₁ - γ t₂‖ ^ 2 = (γ t₁ (0 : Fin 3) - γ t₂ (0 : Fin 3)) ^ 2
        + (γ t₁ (1 : Fin 3) - γ t₂ (1 : Fin 3)) ^ 2 + (1 - (-1)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hc2, hs₁, hs₂]
    have hbig : 4 ≤ ‖γ t₁ - γ t₂‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (γ t₁ (0 : Fin 3) - γ t₂ (0 : Fin 3)),
        sq_nonneg (γ t₁ (1 : Fin 3) - γ t₂ (1 : Fin 3))]
    nlinarith [norm_nonneg (γ t₁ - γ t₂)]

end

end Work.CoreTopology
