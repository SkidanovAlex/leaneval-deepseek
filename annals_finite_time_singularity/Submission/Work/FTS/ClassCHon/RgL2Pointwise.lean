import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.holder_two_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/RgL2Pointwise` — the pointwise bound for `radGreen` in terms of the
weighted `L²`-norm of the source

The existing mode-uniform bound `Work.FTS.ClassCHon.radGreen_size_bound`,
`m² |radGreen α m c z| ≤ A · sup_t |c t|`, consumes a *pointwise* bound on the source `c`.
That is exactly what is unavailable for a source given only by an `ℋ^k`-membership hypothesis
(`HkMem` controls `c` only through *integrated* weighted `L²` quantities, and its mode
coefficients `cmode m F` are not bounded uniformly in the radial variable).

This file proves the companion bound in which the role of `sup_t |c t|` is played by the
weighted `L²`-norm `‖c‖_{w²} = (∫_{t>0} c t² · w t²)^{1/2}`:

  `|z^{-q} ∫_0^z c t^{q-1}| ≤ ‖c‖_{w²} / √(2 q − 1)`   (`q = (2m+5)/α`),
  `|z^{p} ∫_z^∞ c t^{-p-1}| ≤ ‖c‖_{w²} / √(2 p − 3)`    (`p = 2m/α`),

hence `|radGreen α m c z| ≤ (1/(α(4m+5)))·(1/√(2q-1) + 1/√(2p-3))·‖c‖_{w²}`, and since
`q ≥ 8m`, `p ≥ 8m` on the standing range `α ≤ 1/4`, `m ≥ 1`, also

  `|radGreen α m c z| ≤ ‖c‖_{w²} / (4 α m^{3/2})`.

The proof is Cauchy–Schwarz against the weight `w`: the two kernels are split as
`c t · t^{q-1} = (c t · w t) · (t^{q-1} / w t)` (resp. `c t · t^{-p-1}`), so the two `L²`-factors
are the source norm and the explicit weight integrals
`∫_{(0,z)} t^{2q-2}/w² = ∫_{(0,z)} t^{2q+2}/(1+t)⁴` and `∫_{(z,∞)} t^{-2p-2}/w²`, which are
pinned by `1/w(t)² = t⁴/(1+t)⁴ ≤ t⁴` resp. `≤ 1`:

  `∫_{(0,z)} t^{2q-2}/w² ≤ z^{2q}/(2q-1)`,   `∫_{(z,∞)} t^{-2p-2}/w² ≤ z^{-2p}/(2p-3)`.

Nothing here uses regularity, support or sign hypotheses on `c`: only the weighted
`L²`-integrability `∫_{t>0} c²w² < ∞` (which `HkMem` supplies through its slicewise conjunct)
and the a.e. strong measurability of `c·w` on `(0,∞)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon

local notation "w" => Work.Spaces.w

/-- The weight `w` is positive at `t > 0`. -/
theorem w_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < w t := by
  rw [Work.Spaces.w]
  positivity

/-- `1 / w(t)² = t⁴/(1+t)⁴`. -/
theorem one_div_w_sq_eq {t : ℝ} (ht : 0 < t) :
    1 / (w t) ^ 2 = t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ) := by
  have hw : (w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [Work.Spaces.w, div_pow]
    ring
  rw [hw, one_div, inv_div]
  rw [Real.rpow_ofNat, Real.rpow_ofNat]

/-- `t^{2Q-2}/w(t)² = t^{2Q+2}/(1+t)⁴` for `0 ≤ t`, `Q > 1`. -/
theorem near_pow_form {Q t : ℝ} (ht : 0 ≤ t) (hQ : 1 < Q) :
    t ^ (2 * Q - 2) / (w t) ^ 2 = t ^ (2 * Q + 2) / (1 + t) ^ (4 : ℝ) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    have h1 : w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [h1, Real.zero_rpow (by linarith : 2 * Q - 2 ≠ 0),
      Real.zero_rpow (by linarith : 2 * Q + 2 ≠ 0)]
    norm_num
  · have hsplit : t ^ (2 * Q - 2) * t ^ (4 : ℝ) = t ^ (2 * Q + 2) := by
      rw [← Real.rpow_add h]; ring_nf
    calc t ^ (2 * Q - 2) / (w t) ^ 2
        = t ^ (2 * Q - 2) * (1 / (w t) ^ 2) := by ring
      _ = t ^ (2 * Q - 2) * (t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ)) := by rw [one_div_w_sq_eq h]
      _ = t ^ (2 * Q + 2) / (1 + t) ^ (4 : ℝ) := by rw [← hsplit]; ring

/-- `t^{-2P-2}/w(t)² = t^{-2P+2}/(1+t)⁴` for `0 ≤ t`. -/
theorem far_pow_form {P t : ℝ} (ht : 0 ≤ t) (hP : 3 / 2 < P) :
    t ^ (-2 * P - 2) / (w t) ^ 2 = t ^ (-2 * P + 2) / (1 + t) ^ (4 : ℝ) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    have h1 : w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [h1, Real.zero_rpow (by linarith : -2 * P - 2 ≠ 0),
      Real.zero_rpow (by linarith : -2 * P + 2 ≠ 0)]
    norm_num
  · have hsplit : t ^ (-2 * P - 2) * t ^ (4 : ℝ) = t ^ (-2 * P + 2) := by
      rw [← Real.rpow_add h]; ring_nf
    calc t ^ (-2 * P - 2) / (w t) ^ 2
        = t ^ (-2 * P - 2) * (1 / (w t) ^ 2) := by ring
      _ = t ^ (-2 * P - 2) * (t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ)) := by rw [one_div_w_sq_eq h]
      _ = t ^ (-2 * P + 2) / (1 + t) ^ (4 : ℝ) := by rw [← hsplit]; ring

/-! ## The pointwise dominations -/

/-- `t^{2Q-2}/w(t)² ≤ t^{2Q+2}` for `t > 0`. -/
theorem near_div_w_sq_le_rpow {Q t : ℝ} (ht : 0 < t) (hQ : 1 < Q) :
    t ^ (2 * Q - 2) / (w t) ^ 2 ≤ t ^ (2 * Q + 2) := by
  rw [near_pow_form ht.le hQ, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  exact le_mul_of_one_le_right (Real.rpow_nonneg ht.le _) (Real.one_le_rpow (by linarith) (by norm_num))

/-- `t^{-2P-2}/w(t)² ≤ t^{-2P+2}` for `t > 0`. -/
theorem far_div_w_sq_le_rpow {P t : ℝ} (ht : 0 < t) (hP : 3 / 2 < P) :
    t ^ (-2 * P - 2) / (w t) ^ 2 ≤ t ^ (-2 * P + 2) := by
  rw [far_pow_form ht.le hP, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  exact le_mul_of_one_le_right (Real.rpow_nonneg ht.le _) (Real.one_le_rpow (by linarith) (by norm_num))

/-- `t^{2Q-2}/w(t)² ≤ t^{2Q-2}` for `t > 0`. -/
theorem near_div_w_sq_le_self {Q t : ℝ} (ht : 0 < t) (hQ : 1 < Q) :
    t ^ (2 * Q - 2) / (w t) ^ 2 ≤ t ^ (2 * Q - 2) := by
  rw [near_pow_form ht.le hQ, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  rw [show t ^ (2 * Q + 2) = t ^ (2 * Q - 2) * t ^ (4 : ℝ) by
    rw [← Real.rpow_add ht]; ring_nf]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
    (Real.rpow_nonneg ht.le _)

/-- `t^{-2P-2}/w(t)² ≤ t^{-2P-2}` for `t > 0`. -/
theorem far_div_w_sq_le_self {P t : ℝ} (ht : 0 < t) (hP : 3 / 2 < P) :
    t ^ (-2 * P - 2) / (w t) ^ 2 ≤ t ^ (-2 * P - 2) := by
  rw [far_pow_form ht.le hP, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  rw [show t ^ (-2 * P + 2) = t ^ (-2 * P - 2) * t ^ (4 : ℝ) by
    rw [← Real.rpow_add ht]; ring_nf]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
    (Real.rpow_nonneg ht.le _)

/-! ## The elementary rpow integrals and the two weight integrals -/

/-- The elementary rpow integral `∫_{(0,z)} t^{r} = z^{r+1}/(r+1)` for `-1 < r`. -/
theorem integral_Ioc_rpow_eq {z r : ℝ} (hz : 0 < z) (hr : -1 < r) :
    ∫ t in Set.Ioc (0 : ℝ) z, t ^ r = z ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hz.le, integral_rpow (Or.inl hr)]
  rw [Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]


end Work.FTS.ClassCHon
