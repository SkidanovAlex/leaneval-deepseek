import Mathlib
import Submission.Work.RPB.Port.Drive.rot90
import Submission.Work.RPB.Port.Drive.curve_normal_sep
import Submission.Work.RPB.Port.Drive.curve_local_tangent_unique

/-!
# The curve crosses its normal line through the base point only at the base point

Let `G : ℝ → ℝ × ℝ` be a continuous closed plane curve of period `2π` that is injective
modulo the period (`hinj`), with nonzero derivative `V` at `0`.  Then, near `G 0`, the curve
meets the normal line `G 0 + span (rot90 V)` only at `G 0` itself: there is `ε > 0` such that
`|τ| ≤ ε` and `G x = G 0 + τ • rot90 V` forces `τ = 0` and `x = 2π k`.

This is the local transversality statement at the base point: the point `G 0` is a simple point
of the curve, and the tangent line `G 0 + span V` there is transverse to the normal line
`G 0 + span (rot90 V)`, so the curve crosses the normal line transversally at `G 0` and nowhere
else nearby.

The proof combines two inputs:

* `Work.RPB.Port.Drive.curve_normal_sep` (uniform separation): on `[0,2π]` the curve is away from `G 0`
  except near `0`, so a point of the curve within a fixed distance of `G 0` has its parameter
  within any prescribed `r > 0` of a multiple of `2π`;
* `Work.RPB.Port.Drive.curve_local_tangent_unique` (local uniqueness): since `G` is differentiable at `0`
  with nonzero derivative `V`, and `V` and `rot90 V` span the plane, the normal line meets the
  curve near `0` only at `t = 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Drive

/-- A `2π`-periodic curve takes the same value at `x` and at `x - 2π k`. -/
lemma periodic_sub_zmul {G : ℝ → ℝ × ℝ} (hper : ∀ t : ℝ, G (t + 2 * Real.pi) = G t)
    (x : ℝ) (k : ℤ) : G (x - 2 * Real.pi * k) = G x := by
  have h : Function.Periodic G (2 * Real.pi) := hper
  have h2 := h.sub_zsmul_eq (x := x) k
  simpa [show k • (2 * Real.pi) = 2 * Real.pi * k by rw [zsmul_eq_mul]; ring] using h2

theorem curve_normal_segment (G : ℝ → ℝ × ℝ) {V : ℝ × ℝ} (hV : V ≠ 0) (hcont : Continuous G)
    (hder : HasDerivAt G V 0) (hper : ∀ t : ℝ, G (t + 2 * Real.pi) = G t)
    (hinj : ∀ s t : ℝ, G s = G t → ∃ k : ℤ, s = t + 2 * Real.pi * k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x τ : ℝ, |τ| ≤ ε → G x = G 0 + τ • rot90 V →
      τ = 0 ∧ ∃ k : ℤ, x = 2 * Real.pi * k := by
  -- the local uniqueness radius
  obtain ⟨η, hηpos, hη⟩ := curve_local_tangent_unique G hV hder
  -- the uniform separation radius, for `r = min η 1 ≤ π`
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨δ, hδpos, hδ⟩ := curve_normal_sep G hcont hper hinj
    (lt_min hηpos one_pos) (le_trans (min_le_right _ _) hπ)
  -- `rot90 V ≠ 0`
  have hcpos : 0 < ‖rot90 V‖ := norm_pos_iff.mpr (rot90_ne_zero hV)
  refine ⟨δ / (‖rot90 V‖ + 1), by positivity, ?_⟩
  intro x τ hτ hx
  -- the curve point `G x` is strictly closer to `G 0` than `δ`
  have hsub : G x - G 0 = τ • rot90 V := by rw [hx, add_sub_cancel_left]
  have hlt : ‖G x - G 0‖ < δ := by
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have h1 : ‖rot90 V‖ < ‖rot90 V‖ + 1 := by linarith
    have h2 : (δ / (‖rot90 V‖ + 1)) * (‖rot90 V‖ + 1) = δ := by
      rw [div_mul_cancel₀]; linarith
    calc |τ| * ‖rot90 V‖ ≤ (δ / (‖rot90 V‖ + 1)) * ‖rot90 V‖ :=
          mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
      _ < (δ / (‖rot90 V‖ + 1)) * (‖rot90 V‖ + 1) :=
          mul_lt_mul_of_pos_left h1 (by positivity)
      _ = δ := h2
  -- so the parameter is within `η` of a multiple of `2π`
  obtain ⟨k, hk⟩ := hδ x hlt
  have hkη : |x - 2 * Real.pi * k| < η := lt_of_lt_of_le hk (min_le_left _ _)
  have hGy : G (x - 2 * Real.pi * k) = G 0 + τ • rot90 V := by
    rw [periodic_sub_zmul hper x k]; exact hx
  have hy0 : x - 2 * Real.pi * k = 0 := hη _ τ hkη hGy
  have hx0 : x = 2 * Real.pi * k := by linarith
  -- hence the point is `G 0` itself, and `τ • rot90 V = 0` with `rot90 V ≠ 0`
  have hτ0 : τ = 0 := by
    have h0 : τ • rot90 V = 0 := by
      have h' := hGy
      rw [hy0] at h'
      exact add_eq_left.mp h'.symm
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (rot90_ne_zero hV)
  exact ⟨hτ0, ⟨k, hx0⟩⟩

end Work.RPB.Port.Drive
