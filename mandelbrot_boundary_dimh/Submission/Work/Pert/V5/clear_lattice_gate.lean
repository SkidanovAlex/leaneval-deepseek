import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.band_Qm_margins

/-!
# `Work.Pert.V5.clear_lattice_gate`

The elementary lattice-avoidance estimate for a point `w` with **bounded real part**
`|Re w| ≤ 20 (M+2+Ξ)` and `‖w‖ ≥ 2^10`, when `α ∈ 𝓕₁` is small
(`‖α‖ ≤ 1 / (32 (M+2+Ξ))`): for every integer `k`,

`‖α‖ · 2^10 ≤ ‖α w − k‖`,  equivalently `2^10 ≤ ‖w − k/α‖`.

Two ingredients:

* `Re (1/α) ≥ 1/(√2 ‖α‖) ≥ 22 (M+2+Ξ)`: `InF1 α` says `|Im α| < Re α`, so
  `‖α‖^2 = (Re α)^2 + (Im α)^2 < 2 (Re α)^2`, i.e. `‖α‖ ≤ √2 · Re α`, and
  `Re (1/α) = Re α / ‖α‖^2 ≥ 1/(√2 ‖α‖)`.  Hence the lattice `(1/α)ℤ` is spaced by
  more than `20 (M+2+Ξ)` *along the real axis*, strictly to the right of `0`;
* consequently, for `k ≠ 0`, `Re (k/α)` dominates `Re w` by at least
  `22(M+2+Ξ) − 20(M+2+Ξ) = 2(M+2+Ξ) ≥ 2^10`, and for `k = 0` we use `‖w‖ ≥ 2^10`.

Compare `Work.Pert.V5.clear_lattice_band`, which treats the case where `w` lies in the band
`-(Ξ+2^10+2M) ≤ Re w ≤ -(Ξ+2^10)`; there the weaker bound `Re (1/α) ≥ Ξ + 2M + 2·2^10` suffices,
whereas here the hypothesis on `Re w` is two-sided and the sharp bound `1/(√2‖α‖)` is needed.
-/

namespace Work.Pert.V5

open Complex

/-- `√2 ≤ 16/11` (both sides are positive and `2 ≤ (16/11)^2`). -/
private lemma sqrt_two_le : Real.sqrt 2 ≤ (16 : ℝ) / 11 := by
  rw [Real.sqrt_le_iff]
  norm_num

/-- For `α ∈ 𝓕₁` (`|Im α| < Re α`): `Re (1/α) ≥ 1/(√2 ‖α‖)`.

(Compare `Work.Pert.V5.clear_lattice_band`'s `inv_re_lower`, which only gives `1/(2 Re α)`; the
sharper constant here comes from `‖α‖ ≤ √2 Re α`, and is what makes `Re (1/α) ≥ 22 (M+2+Ξ)`
rather than `≥ 16 (M+2+Ξ)` available below.) -/
private lemma inv_re_lower_sqrt {α : ℂ} (h : |α.im| < α.re) :
    1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) h
  have hne : α ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hR : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have him : α.im ^ 2 < α.re ^ 2 := by
    have h' : |α.im| < |α.re| := by rwa [abs_of_pos hre]
    have h2 := (sq_lt_sq).mpr h'
    simpa only [sq_abs] using h2
  -- `‖α‖ ≤ √2 · Re α`
  have hRle : ‖α‖ ≤ Real.sqrt 2 * α.re := by
    have hsq : ‖α‖ ^ 2 ≤ (Real.sqrt 2 * α.re) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [him]
    have h4 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg α), abs_of_nonneg (by positivity)] at h4
  have h3 : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.sq_norm]
  rw [h3]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 * ‖α‖)
    (by positivity : (0 : ℝ) < ‖α‖ ^ 2)]
  nlinarith [hRle, hR]

/-- **The lattice gate.** For `α ∈ 𝓕₁` with `‖α‖ ≤ 1/(32 (M+2+Ξ))`, `M ≥ 2^10`, `Ξ > 0`, and `w`
with `|Re w| ≤ 20 (M+2+Ξ)`, `‖w‖ ≥ 2^10`, the lattice `(1/α)ℤ` stays at distance `≥ 2^10` from
`w` — equivalently `‖α w − k‖ ≥ ‖α‖ 2^10` for every integer `k`. -/
theorem clear_lattice_gate {Ξ M : ℝ} {α : ℂ} {w : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hwr : |w.re| ≤ 20 * (M + 2 + Ξ)) (hlow : 2 ^ 10 ≤ ‖w‖) :
    ∀ k : ℤ, ‖α‖ * 2 ^ 10 ≤ ‖α * w - (k : ℂ)‖ := by
  have hF1 : |α.im| < α.re := hInF1
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hαre
    simp at hαre
  have hnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hA : 0 < M + 2 + Ξ := by
    have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
    linarith [hM, hΞ]
  have h32pos : (0 : ℝ) < 32 * (M + 2 + Ξ) := by linarith
  -- ### the lattice `(1/α)ℤ` is spaced by `≥ 22 (M+2+Ξ)` along the real axis
  have hρ : 22 * (M + 2 + Ξ) ≤ (1 / α).re := by
    have h0 := inv_re_lower_sqrt hF1
    have hRinv : 32 * (M + 2 + Ξ) ≤ 1 / ‖α‖ := by
      rw [le_div_iff₀ hnormpos]
      have h32ne : 32 * (M + 2 + Ξ) ≠ 0 := ne_of_gt h32pos
      calc 32 * (M + 2 + Ξ) * ‖α‖
          ≤ 32 * (M + 2 + Ξ) * (1 / (32 * (M + 2 + Ξ))) :=
            mul_le_mul_of_nonneg_left hα h32pos.le
        _ = 1 := mul_one_div_cancel h32ne
    have hinv : (11 : ℝ) / 16 ≤ 1 / Real.sqrt 2 := by
      have h' := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) sqrt_two_le
      simpa using h'
    have hid : (1 : ℝ) / (Real.sqrt 2 * ‖α‖) = (1 / Real.sqrt 2) * (1 / ‖α‖) := by
      rw [one_div_mul_one_div]
    have hprod : 22 * (M + 2 + Ξ) ≤ (1 / Real.sqrt 2) * (1 / ‖α‖) := by
      have hm := mul_le_mul hinv hRinv h32pos.le
        (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2)
      have hc : (11 : ℝ) / 16 * (32 * (M + 2 + Ξ)) = 22 * (M + 2 + Ξ) := by ring
      linarith [hm, hc]
    rw [← hid] at hprod
    linarith [h0, hprod]
  -- ### reduce to a statement about `w - k/α`
  intro k
  have hfac : α * w - (k : ℂ) = α * (w - (k : ℂ) / α) := by
    have h1 : α * ((k : ℂ) / α) = (k : ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm α (k : ℂ), mul_assoc, mul_inv_cancel₀ hαne,
        mul_one]
    rw [mul_sub, h1]
  rw [hfac, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ hnormpos.le
  have hrek : (w - (k : ℂ) / α).re = w.re - (k : ℝ) * (1 / α).re := by
    have h2 : ((k : ℂ) / α).re = (k : ℝ) * (1 / α).re := by
      rw [div_eq_mul_inv, one_div, Complex.mul_re]
      simp
    rw [Complex.sub_re, h2]
  by_cases hk : k = 0
  · -- `k = 0`: use `‖w‖ ≥ 2^10`
    subst hk
    simpa using hlow
  · -- `k ≠ 0`: `|Re (k/α)| ≥ 22 (M+2+Ξ)` dominates `|Re w| ≤ 20 (M+2+Ξ)`
    have hρpos : 0 < (1 / α).re := by linarith [hρ, hA]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk
    have hbig : 22 * (M + 2 + Ξ) ≤ |(k : ℝ) * (1 / α).re| := by
      rw [abs_mul, abs_of_pos hρpos]
      calc 22 * (M + 2 + Ξ) ≤ 1 * (1 / α).re := by linarith
        _ ≤ |(k : ℝ)| * (1 / α).re := mul_le_mul_of_nonneg_right hk1 hρpos.le
    have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
    have htri : |(k : ℝ) * (1 / α).re| - |w.re| ≤ |w.re - (k : ℝ) * (1 / α).re| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * (1 / α).re) w.re
      rw [abs_sub_comm] at h
      linarith
    have hgoal : (2 : ℝ) ^ 10 ≤ |w.re - (k : ℝ) * (1 / α).re| := by
      have : (2 : ℝ) ^ 10 ≤ |(k : ℝ) * (1 / α).re| - |w.re| := by
        linarith [hbig, hwr, h1024, hM, hΞ]
      linarith
    calc (2 : ℝ) ^ 10 ≤ |w.re - (k : ℝ) * (1 / α).re| := hgoal
      _ = |(w - (k : ℂ) / α).re| := by rw [hrek]
      _ ≤ ‖w - (k : ℂ) / α‖ := Complex.abs_re_le_norm _

end Work.Pert.V5
