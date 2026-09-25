import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.beurling_bounded
import Submission.Work.Beltrami.beurling_holder_difference

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open Work.Beltrami

/-!
# Schauder (Calderón–Zygmund) estimates for the Beurling transform on `C^{0,α}`

`beurling f` is the Beurling transform of `f` on `ℂ ≅ ℝ²`, defined in
`Submission/Work/Beltrami/Cauchy.lean` as the absolutely convergent integral
`-(1/π) ∫ (f ζ - χ(ζ - z) f z) (ζ - z)⁻² dA(ζ)` against the smooth cutoff `χ = bumpC`.

The two analytic ingredients are proved in sibling modules:

* `Work.Beltrami.beurling_bounded` (module `Submission.Work.Beltrami.beurling_bounded`):
  `‖beurling f z‖ ≤ C (M+K) (1+R)` uniformly in `z`;
* `Work.Beltrami.beurling_holder_difference`
  (module `Submission.Work.Beltrami.beurling_holder_difference`):
  `‖beurling f x - beurling f y‖ ≤ C (M+K) (1+R) ‖x-y‖^α`.

Here they are combined, with the larger of the two constants, into the requested statement.
-/

/-- Schauder (Calderon-Zygmund) estimates for the Beurling transform on `C^{0,alpha}`: if `f` is
bounded by `M`, globally alpha-Holder with constant `K`, and supported in the disc of radius
`R ≥ 0`, then `beurling f` is bounded by `C (M+K) (1+R)` and globally alpha-Holder with constant
`C (M+K) (1+R)`, with `C` depending only on `alpha`. -/
theorem beurling_schauder {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (f : ℂ → ℂ)
    (hM : ∀ z, ‖f z‖ ≤ M) (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ z, ‖beurling f z‖ ≤ C * (M + K) * (1 + R)) ∧
      (∀ x y, ‖beurling f x - beurling f y‖ ≤ C * (M + K) * (1 + R) * ‖x - y‖ ^ α) := by
  obtain ⟨C₁, hC₁, h₁⟩ := beurling_bounded hα hα1 hR f hM hK hsupp
  obtain ⟨C₂, hC₂, h₂⟩ := beurling_holder_difference hα hα1 hR f hM hK hsupp
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h1 : ‖f 1 - f 0‖ ≤ K := by
      have := hK 1 0
      rwa [sub_zero, norm_one, Real.one_rpow, mul_one] at this
    by_contra h
    have h2 : K < 0 := not_le.mp h
    linarith [norm_nonneg (f 1 - f 0)]
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_, ?_⟩
  · intro z
    calc ‖beurling f z‖ ≤ C₁ * (M + K) * (1 + R) := h₁ z
      _ ≤ max C₁ C₂ * (M + K) * (1 + R) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by linarith))
            (by linarith)
  · intro x y
    calc ‖beurling f x - beurling f y‖
        ≤ C₂ * (M + K) * (1 + R) * ‖x - y‖ ^ α := h₂ x y
      _ ≤ max C₁ C₂ * (M + K) * (1 + R) * ‖x - y‖ ^ α := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by linarith))
            (by linarith)

end Work.Beltrami
