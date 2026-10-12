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
# `Submission.Work.BoseBogFS.tauSm_ge_kink` — the kink domination at the concrete symbol

The smoothed kinetic symbol of the honest box model is

`tauSm eT s d ℓ k = (1-ε_T)·c²·τ̃(‖k‖/c) + ε_T·c'²·τ̃(‖k‖/c')`,  `c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹`,

with the chosen profile `τ̃ = Work.BoseBoxFock.tauProf` of `exists_tauProf`, whose lower
bound *at the doubled argument* is

`(max 0 (r - 2))² ≤ τ̃ r`.

Since the first kink of the smoothed symbol sits at `2c = (sℓ)⁻¹`, the identity

`(max 0 (x - 2c))² = c²·(max 0 (x/c - 2))²` (`c > 0`, `sq_mul_max_zero_sub`)

turns that profile bound into the **kink domination**

`(1-ε_T)·(max 0 (‖k‖ - (sℓ)⁻¹))² ≤ tauSm eT s d ℓ k`

for every `k` (no hypothesis on the side of the kink, and none on `d`: the `ε_T`-weighted
second term is simply discarded as nonnegative).  This is the *unconditional* form of
`Work.BoseBogFS.tauSm_ge_sq` (which assumes `(sℓ)⁻¹ ≤ ‖k‖`) and it is the `RHi`-side row
that bounds `𝒟_k = ½(𝒜_k + √(𝒜_k²-ℬ_k²))` from below by its kinetic part.
-/

noncomputable section

namespace Work.BoseBogFS

open Work.BoseBoxFock

/-- `max 0 (c·y) = c·max 0 y` for `c > 0`. -/
lemma max_zero_mul_eq (c y : ℝ) (hc : 0 < c) : max 0 (c * y) = c * max 0 y := by
  rcases lt_or_ge y 0 with hy | hy
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc.le hy.le), max_eq_left hy.le, mul_zero]
  · rw [max_eq_right (mul_nonneg hc.le hy), max_eq_right hy]

/-- **The rescaling identity behind the kink.**  For `c > 0`,

`(max 0 (x - 2c))² = c²·(max 0 (x/c - 2))²`:

both `max`es are active exactly when `x ≥ 2c`, and then the identity is the algebraic
`(x-2c)² = c²(x/c - 2)²`. -/
lemma sq_mul_max_zero_sub (c x : ℝ) (hc : 0 < c) :
    (max 0 (x - 2 * c)) ^ 2 = c ^ 2 * (max 0 (x / c - 2)) ^ 2 := by
  have hsub : x - 2 * c = c * (x / c - 2) := by field_simp
  rw [hsub, max_zero_mul_eq c (x / c - 2) hc]
  ring

/-- The chosen profile `τ̃` dominates `(r-2)₊²` (`exists_tauProf`). -/
lemma tauProf_ge_kink' (r : ℝ) : (max 0 (r - 2)) ^ 2 ≤ tauProf r :=
  Work.BoseBoxFock.tauProf_spec.2.2.1 r

/-- `τ̃ ≥ 0`, as it dominates `(r-2)₊²`. -/
lemma tauProf_nonneg' (r : ℝ) : 0 ≤ tauProf r :=
  le_trans (sq_nonneg _) (tauProf_ge_kink' r)

/-- **The kink domination at the concrete smoothed symbol.**  For `0 ≤ ε_T ≤ 1`, `s, ℓ > 0`
and every momentum `k`,

`(1-ε_T)·(max 0 (‖k‖ - (sℓ)⁻¹))² ≤ tauSm ε_T s d ℓ k`

(the `ε_T`-weighted second term is discarded as nonnegative, so no hypothesis on `d` is
used). -/
theorem tauSm_ge_kink {eT s d ℓ : ℝ} (h0 : 0 ≤ eT) (h1 : eT ≤ 1) (hs : 0 < s)
    (hd : 0 < d) (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    (1 - eT) * (max 0 (‖k‖ - (s * ℓ)⁻¹)) ^ 2
      ≤ Work.BoseBoxFock.tauSm eT s d ℓ k := by
  have hc : 0 < (2 * s * ℓ)⁻¹ := by positivity
  have h2c : 2 * (2 * s * ℓ)⁻¹ = (s * ℓ)⁻¹ := by field_simp
  have h1eT : 0 ≤ 1 - eT := by linarith
  -- the kink position `(sℓ)⁻¹` is the doubled centre `2c` of the profile argument
  have hkey : (max 0 (‖k‖ - (s * ℓ)⁻¹)) ^ 2
      = ((2 * s * ℓ)⁻¹) ^ 2 * (max 0 (‖k‖ / (2 * s * ℓ)⁻¹ - 2)) ^ 2 := by
    rw [← h2c]
    exact sq_mul_max_zero_sub (2 * s * ℓ)⁻¹ ‖k‖ hc
  have hge : (max 0 (‖k‖ / (2 * s * ℓ)⁻¹ - 2)) ^ 2
      ≤ tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := tauProf_ge_kink' _
  -- the `(1-ε_T)`-weighted first term of `tauSm` dominates the kinked square
  have hmain : (1 - eT) * (max 0 (‖k‖ - (s * ℓ)⁻¹)) ^ 2
      ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := by
    calc (1 - eT) * (max 0 (‖k‖ - (s * ℓ)⁻¹)) ^ 2
        = (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * (max 0 (‖k‖ / (2 * s * ℓ)⁻¹ - 2)) ^ 2) := by
          rw [hkey]
      _ ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hge (sq_nonneg _)) h1eT
      _ = (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹) := by ring
  -- the `ε_T`-weighted second term is nonnegative and is discarded
  have hnn : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg h0 (sq_nonneg _)) (tauProf_nonneg' _)
  simp only [Work.BoseBoxFock.tauSm]
  exact le_trans hmain (le_add_of_nonneg_right hnn)

end Work.BoseBogFS
