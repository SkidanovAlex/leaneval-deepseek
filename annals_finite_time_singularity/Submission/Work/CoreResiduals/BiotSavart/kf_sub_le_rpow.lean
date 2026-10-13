/-
# `Work.CoreResiduals.BiotSavart.kf_sub_le_rpow` — the `C^{0,α}` modulus of the Newtonian kernel

The Biot–Savart kernel `kf b = ‖b‖⁻³ • b` is, up to the factor `‖b‖⁻²` coming from its
degree-`-2` homogeneity, a Hölder-continuous function of `b` away from the origin.  This file
records the exact *weighted* form of that statement that the far-field estimates consume:

  `‖kf p - kf q‖ ≤ 1028 ‖p - q‖ ^ α (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α))`   (`0 < α < 1`).

The structure of the proof is the usual two-regime splitting, with `d = ‖p - q‖` the distance
and `s = max (‖p‖) (‖q‖)` the larger of the two moduli (the statement is symmetric in `p` and
`q`, so we may assume `‖p‖ ≤ ‖q‖`):

* **far regime** `2 d ≤ ‖q‖`: the point `p` is far from `q`, so the second-order Taylor
  expansion of `kf` at `q` is available,
  `kf p - kf q = resid (p - q) q + kDerivCLM q (p - q)`, and the two bounds
  `‖resid (p - q) q‖ ≤ 1024 d² ‖q‖⁻⁴` (`norm_resid_le_far`) and
  `‖kDerivCLM q (p - q)‖ ≤ 4 d ‖q‖⁻³` (`norm_kDerivCLM_le`) give
  `‖kf p - kf q‖ ≤ 1024 d² ‖q‖⁻⁴ + 4 d ‖q‖⁻³`;
  since `d ≤ ‖q‖`, every positive power of `d` can be traded for the same power of `‖q‖`,
  which yields `≤ 1028 d^α ‖q‖ ^ (-2-α) ≤ 1028 d^α (‖p‖ ^ (-2-α) + ‖q‖ ^ (-2-α))`.

* **near regime** `‖q‖ < 2 d`: here no cancellation is available and we use the crude bound
  `‖kf p - kf q‖ ≤ ‖p‖⁻² + ‖q‖⁻² ≤ 2 ‖q‖⁻²`, while `d ≥ ‖q‖/2` *increases* the weight
  `d^α ≥ 2^{-α} ‖q‖^α` so that `1028 d^α ‖q‖ ^ (-2-α) ≥ 1028 · 2^{-α} ‖q‖⁻² ≥ 2 ‖q‖⁻²`.

The two pieces of pure real-variable arithmetic are isolated in
`Work.CoreResiduals.BiotSavart.rpow_far_arith` and
`Work.CoreResiduals.BiotSavart.rpow_near_arith`.

The constant `1028 = 1024 + 4` is an artefact of the (deliberately loose) constants `1024` and
`4` in the two ingredient bounds; only its size matters here.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.CoreResiduals.BiotSavart.norm_resid_le_far
import Submission.Work.CoreResiduals.BiotSavart.rpow_far_arith
import Submission.Work.CoreResiduals.BiotSavart.rpow_near_arith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

/-- `(x ^ n)⁻¹ = x ^ (-(n : ℝ))` for `x ≥ 0`: the integer power `x ^ n` of a nonnegative real is
`x` raised to the *real* exponent `n`, so its inverse is `x` raised to `-n`. -/
lemma inv_pow_eq_rpow_neg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (x ^ n)⁻¹ = x ^ (-(n:ℝ)) := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_neg hx (n:ℝ)]

/-- **Far-regime bound for the difference of two kernel values.**  If the increment `h` is at
most half of `‖y‖`, so that the whole segment `[y, y+h]` stays away from the origin, then
`‖kf (y + h) - kf y‖ ≤ 1024 ‖h‖² ‖y‖⁻⁴ + 4 ‖h‖ ‖y‖⁻³`.  This is the second-order Taylor
expansion of `kf` at `y` (`norm_resid_le_far`) plus the operator-norm bound
`‖kDerivCLM y‖ ≤ 4/‖y‖³` (`norm_kDerivCLM_le`). -/
theorem norm_kf_sub_le_far (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖Work.StabilityFar.Decay.kf (y + h) - Work.StabilityFar.Decay.kf y‖
      ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) + 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
  have hid : Work.StabilityFar.Decay.kf (y + h) - Work.StabilityFar.Decay.kf y
      = resid h y + Work.StabilityFar.Decay.kDerivCLM y h := by
    rw [resid]
    abel
  rw [hid]
  have hres : ‖resid h y‖ ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) := by
    have h0 := norm_resid_le_far h y hy
    have h2 : ‖h‖ ^ (2:ℕ) = ‖h‖ ^ (2:ℝ) := (Real.rpow_two ‖h‖).symm
    rwa [h2] at h0
  have hder : ‖Work.StabilityFar.Decay.kDerivCLM y h‖ ≤ 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
    rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
    · -- degenerate case `y = 0`: then `h = 0` as well and both sides vanish
      have hy00 : y = 0 := by rw [← norm_eq_zero]; exact hy0.symm
      have hh0 : h = 0 := by
        rw [← norm_eq_zero]
        have h2 : 2 * ‖h‖ ≤ 0 := by rw [← hy0] at hy; exact hy
        linarith [norm_nonneg h]
      rw [hy00, hh0]
      simp [kDerivCLM_zero, Real.zero_rpow (by norm_num : (-3:ℝ) ≠ 0)]
    · have hb := Work.StabilityFar.Decay.norm_kDerivCLM_le y ‖y‖ hypos le_rfl
      calc ‖Work.StabilityFar.Decay.kDerivCLM y h‖
          ≤ ‖Work.StabilityFar.Decay.kDerivCLM y‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (4 / ‖y‖ ^ 3) * ‖h‖ := by gcongr
        _ = 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
            rw [show (-3:ℝ) = -(↑(3:ℕ) : ℝ) by norm_num, div_eq_mul_inv,
              inv_pow_eq_rpow_neg ‖y‖ (norm_nonneg y) 3]
            ring
  calc ‖resid h y + Work.StabilityFar.Decay.kDerivCLM y h‖
      ≤ ‖resid h y‖ + ‖Work.StabilityFar.Decay.kDerivCLM y h‖ := norm_add_le _ _
    _ ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) + 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) :=
        add_le_add hres hder

/-- **Hölder-type bound for the Newtonian kernel.**  For `0 < α < 1` there is a constant `C`
such that for all `p q`

  `‖kf p - kf q‖ ≤ C ‖p - q‖ ^ α (‖p‖ ^ (-2-α) + ‖q‖ ^ (-2-α))`.

The two regimes of the argument are described in the header; here it only remains to combine
them with the triangle inequality for `‖kf p‖ = ‖p‖⁻²`. -/
theorem kf_sub_le_rpow {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Work.LWP.R3,
      ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
        ≤ C * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) := by
  refine ⟨1028, by norm_num, ?_⟩
  -- The statement is symmetric in `p` and `q`, so it suffices to treat `‖p‖ ≤ ‖q‖`.
  have key : ∀ p q : Work.LWP.R3, ‖p‖ ≤ ‖q‖ →
      ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
        ≤ 1028 * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) := by
    intro p q hrs
    by_cases hpq : p = q
    · subst hpq
      simp [Real.zero_rpow (ne_of_gt hα)]
    · have hdpos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
      by_cases hfar : 2 * ‖p - q‖ ≤ ‖q‖
      · -- far regime `2‖p - q‖ ≤ ‖q‖`
        have hqpos : 0 < ‖q‖ := by linarith
        have h1 : ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ 1024 * ‖p - q‖ ^ (2:ℝ) * ‖q‖ ^ (-4:ℝ)
              + 4 * ‖p - q‖ * ‖q‖ ^ (-3:ℝ) := by
          have hh := norm_kf_sub_le_far (p - q) q hfar
          rwa [show q + (p - q) = p by abel] at hh
        have h2 := rpow_far_arith hα hα1 hdpos hqpos (by linarith)
        have h3 : 0 ≤ 1028 * ‖p - q‖ ^ α := by
          have := Real.rpow_nonneg (norm_nonneg (p - q)) α
          linarith
        have h4 : ‖q‖ ^ (-2 - α) ≤ ‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α) := by
          have := Real.rpow_nonneg (norm_nonneg p) (-2 - α)
          linarith
        calc ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ 1028 * ‖p - q‖ ^ α * ‖q‖ ^ (-2 - α) := h1.trans h2
          _ ≤ 1028 * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) :=
              mul_le_mul_of_nonneg_left h4 h3
      · -- near regime `‖q‖ < 2‖p - q‖`
        have hnear' : ‖q‖ ≤ 2 * ‖p - q‖ := le_of_lt (not_le.mp hfar)
        have h1 : ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ ‖p‖ ^ (-2:ℝ) + ‖q‖ ^ (-2:ℝ) := by
          calc ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
              ≤ ‖Work.StabilityFar.Decay.kf p‖ + ‖Work.StabilityFar.Decay.kf q‖ :=
                norm_sub_le _ _
            _ = ‖p‖ ^ (-2:ℝ) + ‖q‖ ^ (-2:ℝ) := by rw [norm_kf_eq, norm_kf_eq]
        exact h1.trans (rpow_near_arith hα hα1 (norm_nonneg p) hrs hnear')
  intro p q
  rcases le_total ‖p‖ ‖q‖ with hle | hle
  · exact key p q hle
  · -- swap the roles of `p` and `q`; the statement is symmetric
    have hh := key q p hle
    have e1 : ‖q - p‖ = ‖p - q‖ := norm_sub_rev q p
    have e2 : ‖Work.StabilityFar.Decay.kf q - Work.StabilityFar.Decay.kf p‖
        = ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖ :=
      (norm_sub_rev (Work.StabilityFar.Decay.kf p) (Work.StabilityFar.Decay.kf q)).symm
    have e3 : ‖q‖ ^ (-2 - α) + ‖p‖ ^ (-2 - α)
        = ‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α) := add_comm _ _
    rw [e1, e2, e3] at hh
    exact hh

end Work.CoreResiduals.BiotSavart
