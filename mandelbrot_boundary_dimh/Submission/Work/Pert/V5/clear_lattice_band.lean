import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.V5.clear_lattice_band`

The elementary lattice-avoidance estimate for points `w` of the **band**

`-(Ξ + 2^10 + 2M) ≤ Re w ≤ -(Ξ + 2^10)`

when `α ∈ 𝓕₁` is small (`‖α‖ ≤ 1 / (32 (M+2+Ξ))`): for every integer `k`,

`‖α‖ · 2^10 ≤ ‖α w − k‖`,  equivalently `2^10 ≤ ‖w − k/α‖`.

Two ingredients:

* `Re (1/α) ≥ 1/(2 Re α) ≥ 1/(2‖α‖) ≥ 16 (M+2+Ξ) ≥ Ξ + 2M + 2·2^10`: the lattice `(1/α)ℤ`
  has spacing `≥ Ξ + 2M + 2·2^10`, so no lattice point other than `0` can come near the band
  (recall `‖1/α‖ ≥ 32(M+2+Ξ)`, and `InF1` controls the phase of `1/α` too);
* the band itself is at distance `> 2^10` from `0`.

Since `‖w − k/α‖ ≥ |Re (w − k/α)| = |Re w − k Re(1/α)|`, the conclusion follows.
-/

namespace Work.Pert.V5

open Complex

/-- For `α ∈ 𝓕₁` (`|Im α| < Re α`): `Re (1/α) ≥ 1/(2 Re α)`. -/
private lemma inv_re_lower {α : ℂ} (h : |α.im| < α.re) :
    1 / (2 * α.re) ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) h
  have hne : α ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  have him : α.im ^ 2 < α.re ^ 2 := by
    have h' : |α.im| < |α.re| := by rwa [abs_of_pos hre]
    have h2 := (sq_lt_sq).mpr h'
    simpa only [sq_abs] using h2
  have hden : Complex.normSq α ≤ 2 * α.re ^ 2 := by
    rw [Complex.normSq_apply]
    nlinarith [him]
  have h1 : α.re / (2 * α.re ^ 2) ≤ α.re / Complex.normSq α :=
    div_le_div_of_nonneg_left hre.le hns hden
  have h2 : α.re / (2 * α.re ^ 2) = 1 / (2 * α.re) := by
    field_simp
  have h3 : (1 / α).re = α.re / Complex.normSq α := by
    rw [Complex.div_re]
    simp
  rw [h3, ← h2]
  exact h1

theorem clear_lattice_band {Ξ M : ℝ} {α : ℂ} {w : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hre : -(Ξ + 2 ^ 10 + 2 * M) ≤ w.re) (hre' : w.re ≤ -(Ξ + 2 ^ 10)) :
    ∀ k : ℤ, ‖α‖ * 2 ^ 10 ≤ ‖α * w - (k : ℂ)‖ := by
  have hF1 : |α.im| < α.re := hInF1
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hαre
    simp at hαre
  have hnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have h32pos : (0 : ℝ) < 32 * (M + 2 + Ξ) := by
    have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
    linarith [hM, hΞ, h1024]
  -- ### Step 1: `Re (1/α) ≥ Ξ + 2M + 2·2^10`, i.e. the lattice `(1/α)ℤ` is coarser than the band
  have hρlow : Ξ + 2 * M + 2 * (2 : ℝ) ^ 10 ≤ (1 / α).re := by
    have hstep1 : 1 / (2 * α.re) ≤ (1 / α).re := inv_re_lower hF1
    have hnorm_ge : α.re ≤ ‖α‖ := by
      have h1 := Complex.abs_re_le_norm α
      rwa [abs_of_pos hαre] at h1
    have hstep2 : 16 * (M + 2 + Ξ) ≤ 1 / (2 * α.re) := by
      have h4 : 1 / (2 * ‖α‖) ≤ 1 / (2 * α.re) :=
        one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 2 * α.re)
          (by linarith : 2 * α.re ≤ 2 * ‖α‖)
      have hprod : 32 * (M + 2 + Ξ) * ‖α‖ ≤ 1 := by
        have h32ne : (32 * (M + 2 + Ξ)) ≠ 0 := ne_of_gt h32pos
        calc 32 * (M + 2 + Ξ) * ‖α‖
            ≤ 32 * (M + 2 + Ξ) * (1 / (32 * (M + 2 + Ξ))) :=
              mul_le_mul_of_nonneg_left hα h32pos.le
          _ = 1 := mul_one_div_cancel h32ne
      have h5 : 16 * (M + 2 + Ξ) ≤ 1 / (2 * ‖α‖) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ‖α‖)]
        nlinarith [hprod]
      linarith [h4, h5]
    have h6 : Ξ + 2 * M + 2 * (2 : ℝ) ^ 10 ≤ 16 * (M + 2 + Ξ) := by
      have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
      nlinarith [hM, hΞ, h1024]
    linarith [hstep1, hstep2, h6]
  have hρpos : 0 < (1 / α).re := by
    have h := inv_re_lower hF1
    linarith [hαre, h]
  -- ### Step 2: reduce to a statement about the real part
  intro k
  have hfac : α * w - (k : ℂ) = α * (w - (k : ℂ) / α) := by
    have h1 : α * ((k : ℂ) / α) = (k : ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm α (k : ℂ), mul_assoc, mul_inv_cancel₀ hαne,
        mul_one]
    rw [mul_sub, h1]
  rw [hfac, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ hnormpos.le
  have hre_k : (w - (k : ℂ) / α).re = w.re - (k : ℝ) * (1 / α).re := by
    have h2 : ((k : ℂ) / α).re = (k : ℝ) * (1 / α).re := by
      rw [div_eq_mul_inv, one_div, Complex.mul_re]
      simp
    rw [Complex.sub_re, h2]
  have hband : (2 : ℝ) ^ 10 ≤ |w.re - (k : ℝ) * (1 / α).re| := by
    by_cases hk : (0 : ℝ) ≤ (k : ℝ)
    · -- `k ≥ 0`: the band lies left of `0`, and `k Re (1/α) ≥ 0`
      have hmul : 0 ≤ (k : ℝ) * (1 / α).re := mul_nonneg hk hρpos.le
      have hx : w.re - (k : ℝ) * (1 / α).re ≤ 0 := by linarith [hre']
      rw [abs_of_nonpos hx]
      have h1 : Ξ + (2 : ℝ) ^ 10 ≤ -w.re := by linarith [hre']
      linarith [h1, hmul]
    · -- `k < 0`: the band is `≥ Ξ + 2M` to the left of `0`, and `(-k) Re (1/α) ≥ Re (1/α)`
      have hkneg : (k : ℝ) < 0 := not_le.mp hk
      have hkZ : k < 0 := by exact_mod_cast hkneg
      have hk1Z : k ≤ -1 := by omega
      have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast hk1Z
      have hm : (1 : ℝ) ≤ -(k : ℝ) := by linarith
      have hmul : (1 : ℝ) * (1 / α).re ≤ (-(k : ℝ)) * ((1 / α).re) :=
        mul_le_mul_of_nonneg_right hm hρpos.le
      have he : w.re - (k : ℝ) * (1 / α).re = w.re + (-(k : ℝ)) * ((1 / α).re) := by ring
      have hpos : 0 ≤ w.re - (k : ℝ) * (1 / α).re := by
        rw [he]
        linarith [hre, hmul, hρlow]
      rw [abs_of_nonneg hpos, he]
      linarith [hre, hmul, hρlow]
  calc (2 : ℝ) ^ 10 ≤ |(w - (k : ℂ) / α).re| := by rwa [hre_k]
    _ ≤ ‖w - (k : ℂ) / α‖ := Complex.abs_re_le_norm _

end Work.Pert.V5
