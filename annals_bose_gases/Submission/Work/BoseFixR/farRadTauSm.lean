import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/farRadTauSm.lean` — the far radial kinetic row

`Work.BoseBoxFock.tauSm` is the smoothed kinetic symbol

  `tauSm ε_T s d ℓ k = (1−ε_T) c₁² τ̃(‖k‖/c₁) + ε_T c₂² τ̃(‖k‖/c₂)`,

with `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹` and `τ̃ = Work.BoseBoxFock.tauProf` the smooth profile of
`Work.BoseBoxFock.exists_tauProf`, which *dominates* the kink: `τ̃(r) ≥ (max 0 (r−2))²`.

Rescaling that lower bound (`tauProf_scaled_ge` below: for `c > 0`,
`c² τ̃(r/c) ≥ (max 0 (r − 2c))²`) and dropping the second, nonnegative term gives the radial
lower bound `farRadTauSm`: on the far sphere `‖k‖ ≫ c₁` the symbol is at least
`(1−ε_T)(‖k‖ − 2c₁)²`.
-/

namespace Work.BoseFixR

open Work.BoseBoxFock

/-- The profile of `exists_tauProf` dominates the kink `(·₊)²` shifted by two. -/
lemma farRadTauSm_tauProf_ge (r : ℝ) :
    (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
  Work.BoseBoxFock.tauProf_spec.2.2.1 r

/-- The profile of `exists_tauProf` is nonnegative. -/
lemma farRadTauSm_tauProf_nonneg (r : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf r :=
  le_trans (sq_nonneg _) (farRadTauSm_tauProf_ge r)

/-- **Rescaling the profile's lower bound**: for `c > 0`,
`(max 0 (r − 2c))² ≤ c² τ̃(r/c)`. -/
lemma tauProf_scaled_ge {c r : ℝ} (hc : 0 < c) :
    (max 0 (r - 2 * c)) ^ 2 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) := by
  have hge : (max 0 (r / c - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf (r / c) :=
    farRadTauSm_tauProf_ge (r / c)
  rcases lt_or_ge (0 : ℝ) (r - 2 * c) with h | h
  · -- `r > 2c`: both maxima are attained on the linear branch
    have h2 : 0 < r / c - 2 := by rw [sub_pos, lt_div_iff₀ hc]; linarith
    have hkey : r - 2 * c = c * (r / c - 2) := by
      field_simp
    calc (max 0 (r - 2 * c)) ^ 2 = (r - 2 * c) ^ 2 := by rw [max_eq_right h.le]
      _ = (c * (r / c - 2)) ^ 2 := by rw [hkey]
      _ = c ^ 2 * (r / c - 2) ^ 2 := by rw [mul_pow]
      _ = c ^ 2 * (max 0 (r / c - 2)) ^ 2 := by rw [max_eq_right h2.le]
      _ ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) :=
          mul_le_mul_of_nonneg_left hge (sq_nonneg c)
  · -- `r ≤ 2c`: the left side vanishes
    rw [max_eq_left h]
    simpa using mul_nonneg (sq_nonneg c) (farRadTauSm_tauProf_nonneg (r / c))

theorem farRadTauSm {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    (1 - eT) * (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
      ≤ Work.BoseBoxFock.tauSm eT s d ℓ k := by
  have hc1 : 0 < (2 * s * ℓ)⁻¹ := inv_pos.mpr (by positivity)
  -- the radial (first) term of `tauSm` already dominates the claim
  have hfirst : (1 - eT) * (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
      ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := by
    have h1 : (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
        ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹) :=
      tauProf_scaled_ge hc1
    have h1e : 0 ≤ 1 - eT := by linarith
    calc (1 - eT) * (max 0 (‖k‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
        ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 h1e
      _ = (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := by ring
  -- the second term is nonnegative
  have h2 : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2
      * Work.BoseBoxFock.tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (farRadTauSm_tauProf_nonneg _)
  rw [Work.BoseBoxFock.tauSm]
  linarith [hfirst, h2]

end Work.BoseFixR
