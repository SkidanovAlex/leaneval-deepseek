import Mathlib

namespace Work.RPB1a.Caratheodory.Arc

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- Squared modulus of a point of the circle of radius `ρ` about `-1`: writing
`circleMap (-1) ρ θ = -1 + ρ e^{iθ}`, its squared distance from the origin is
`1 - 2ρ cos θ + ρ²`. -/
lemma normSq_circleMap_neg_one (ρ θ : ℝ) :
    Complex.normSq (circleMap (-1 : ℂ) ρ θ) = 1 - 2 * ρ * Real.cos θ + ρ ^ 2 := by
  rw [circleMap, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h : (-1 : ℂ) + ↑ρ * (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
      = (↑(ρ * Real.cos θ - 1) : ℂ) + ↑(ρ * Real.sin θ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.normSq_add_mul_I]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- Description of the circular arc `sphere (-1) ρ ∩ ball 0 1` (a crosscut of the unit disc at the
boundary point -1) as an interval of angles: a point of the circle of radius ρ about -1 lies in the
open unit disc exactly when its angle θ (measured from the inward direction, θ ∈ (-π,π)) satisfies
cos θ > ρ/2. -/
theorem mem_sphere_neg_one_inter_ball_iff {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    z ∈ sphere (-1 : ℂ) ρ ∩ ball (0 : ℂ) 1 ↔
      ∃ θ ∈ Ioo (-π) π, ρ / 2 < Real.cos θ ∧ z = circleMap (-1 : ℂ) ρ θ := by
  constructor
  · intro hz
    rw [Set.mem_inter_iff, Metric.mem_sphere, Metric.mem_ball] at hz
    obtain ⟨hzs, hzb⟩ := hz
    have hw : ‖z + 1‖ = ρ := by
      rw [Complex.dist_eq] at hzs
      simpa using hzs
    have hzlt : ‖z‖ < 1 := by
      rw [Complex.dist_eq] at hzb; simpa using hzb
    have hzeq : z = circleMap (-1 : ℂ) ρ (Complex.arg (z + 1)) := by
      have h1 := Complex.norm_mul_exp_arg_mul_I (z + 1)
      rw [hw] at h1
      have h2 : circleMap (-1 : ℂ) ρ (Complex.arg (z + 1)) = z := by
        rw [circleMap]
        rw [show (↑ρ : ℂ) * Complex.exp (↑(Complex.arg (z + 1)) * Complex.I) = z + 1 from h1]
        ring
      exact h2.symm
    have hθ : Complex.arg (z + 1) ∈ Ioo (-π) π := by
      have hIoc := Complex.arg_mem_Ioc (z + 1)
      refine ⟨hIoc.1, lt_of_le_of_ne hIoc.2 ?_⟩
      intro hπ
      have h1 := Complex.norm_mul_exp_arg_mul_I (z + 1)
      rw [hw, hπ, Complex.exp_pi_mul_I] at h1
      have h1' : -↑ρ = z + 1 := by
        rw [mul_neg, mul_one] at h1; exact h1
      have hz' : z = -↑ρ - 1 := by
        rw [eq_sub_iff_add_eq]; exact h1'.symm
      have hnsq : Complex.normSq z = (ρ + 1) ^ 2 := by
        rw [hz']
        have : (-↑ρ - 1 : ℂ) = -(↑(ρ + 1) : ℂ) := by push_cast; ring
        rw [this, Complex.normSq_neg, Complex.normSq_ofReal]; ring
      rw [Complex.normSq_eq_norm_sq] at hnsq
      nlinarith [norm_nonneg z, hzlt, hρ]
    have hcos : ρ / 2 < Real.cos (Complex.arg (z + 1)) := by
      have hlt : Complex.normSq z < 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      rw [hzeq, normSq_circleMap_neg_one] at hlt
      nlinarith [hρ]
    exact ⟨Complex.arg (z + 1), hθ, hcos, hzeq⟩
  · rintro ⟨θ, hθ, hcos, rfl⟩
    refine ⟨?_, ?_⟩
    · exact circleMap_mem_sphere (-1) hρ.le θ
    · rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      have h : Complex.normSq (circleMap (-1 : ℂ) ρ θ) < 1 := by
        rw [normSq_circleMap_neg_one]; nlinarith [hρ, hcos]
      rw [Complex.normSq_eq_norm_sq] at h
      nlinarith [norm_nonneg (circleMap (-1 : ℂ) ρ θ)]

end Work.RPB1a.Caratheodory.Arc
