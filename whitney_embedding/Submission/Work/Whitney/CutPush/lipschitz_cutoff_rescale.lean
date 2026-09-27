import Mathlib
import Submission.Work.Whitney.CutPush.lipschitz_smooth_cutoff

/-!
# Rescaling a Lipschitz cutoff (germ recipe, trap 13b)

`Work.Whitney.CutPush.exists_lipschitz_smooth_cutoff` produces a cutoff `χ` equal to `1` on
`closedBall 0 R` and vanishing outside `closedBall 0 R'`, with a Lipschitz constant `C` — but with
**no control of `C` in the radii**.  The assembly `(c)` of the germ recipe
(`NOTES_hasFingerData_S33.md` §13, trap 13b) needs the opposite: it must be free to choose the scale
of the support *after* the tolerance `c` of `exists_fderiv_close_of_contDiff'` is fixed, with the
*product* `Lip χ · (support radius)` independent of the scale.

The fix is this file: rescale a cutoff of a *fixed* shape.  From `χ₁` with radii `(1, 3)` and
Lipschitz constant `C₁`, the map `χ_r u := χ₁ (r⁻¹ • u)` has radii `(r, 3 r)` and Lipschitz constant
`C₁ / r`, so `Lip(χ_r) · (3 r) = 3 C₁` no longer depends on `r`.
-/

open scoped ContDiff

namespace Work.Whitney.CutPush

/-- **Rescaling a cutoff.** -/
theorem lipschitz_cutoff_rescale {N : ℕ}
    (χ : EuclideanSpace ℝ (Fin N) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hb : ∀ u, 0 ≤ χ u ∧ χ u ≤ 1)
    (h1 : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ ≤ 1 → χ u = 1)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin N), 3 ≤ ‖u‖ → χ u = 0)
    (hlip : ∀ x y : EuclideanSpace ℝ (Fin N), ‖χ x - χ y‖ ≤ C * ‖x - y‖)
    (r : ℝ) (hr : 0 < r) :
    ∃ χr : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χr ∧ (∀ u, 0 ≤ χr u ∧ χr u ≤ 1) ∧
      (∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ ≤ r → χr u = 1) ∧
      (∀ u : EuclideanSpace ℝ (Fin N), 3 * r ≤ ‖u‖ → χr u = 0) ∧
      (∀ x y : EuclideanSpace ℝ (Fin N), ‖χr x - χr y‖ ≤ (C / r) * ‖x - y‖) := by
  refine ⟨fun u => χ (r⁻¹ • u), ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro u
    exact hb _
  · intro u hu
    refine h1 _ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc r⁻¹ * ‖u‖ ≤ r⁻¹ * r := by gcongr
      _ = 1 := inv_mul_cancel₀ hr.ne'
  · intro u hu
    refine h0 _ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc (3 : ℝ) = r⁻¹ * (3 * r) := by field_simp
      _ ≤ r⁻¹ * ‖u‖ := by gcongr
  · intro x y
    have h1' := hlip (r⁻¹ • x) (r⁻¹ • y)
    have h2 : ‖r⁻¹ • x - r⁻¹ • y‖ = r⁻¹ * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [h2] at h1'
    calc ‖χ (r⁻¹ • x) - χ (r⁻¹ • y)‖ ≤ C * (r⁻¹ * ‖x - y‖) := h1'
      _ = (C / r) * ‖x - y‖ := by rw [div_eq_mul_inv]; ring

end Work.Whitney.CutPush
