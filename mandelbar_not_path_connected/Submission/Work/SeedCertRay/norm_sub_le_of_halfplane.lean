import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- **Half-plane distance bound.**  If `w` and `w0` both lie outside the disk of radius `s`
about the origin, if the angle between them is at most `π/2` (`0 ≤ Re (w * conj w0)`), and if
`‖w ^ 2 - w0 ^ 2‖ ≤ R` with `R ≤ ρ * s`, then `‖w - w0‖ ≤ ρ`.

The proof factors `w ^ 2 - w0 ^ 2 = (w - w0) * (w + w0)`, uses
`‖w + w0‖ ^ 2 = ‖w‖ ^ 2 + ‖w0‖ ^ 2 + 2 * Re (w * conj w0) ≥ 2 * s ^ 2` to get `s ≤ ‖w + w0‖`,
and cancels the factor `s`.  The degenerate case `s = 0` is handled separately: it forces
`w ^ 2 = w0 ^ 2`, and the half-plane hypothesis rules out `w = -w0` unless `w0 = 0`. -/
theorem norm_sub_le_of_halfplane {w w0 : ℂ} {s R ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (hs2 : s ^ 2 ≤ ‖w0‖ ^ 2) (hsq : s ^ 2 ≤ ‖w‖ ^ 2) (hhp : 0 ≤ (w * starRingEnd ℂ w0).re) (h : ‖w ^ 2 - w0 ^ 2‖ ≤ R) (hR : R ≤ ρ * s) : ‖w - w0‖ ≤ ρ := by
  -- Factor `w ^ 2 - w0 ^ 2` and pass to norms.
  have hfac : w ^ 2 - w0 ^ 2 = (w - w0) * (w + w0) := by ring
  have hnorm : ‖w - w0‖ * ‖w + w0‖ = ‖w ^ 2 - w0 ^ 2‖ := by
    rw [hfac, norm_mul]
  -- Norm identity behind the half-plane hypothesis.
  have key : ‖w + w0‖ ^ 2 = ‖w‖ ^ 2 + ‖w0‖ ^ 2 + 2 * (w * starRingEnd ℂ w0).re := by
    have hh := Complex.normSq_add w w0
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hh
    exact hh
  have hv2 : 2 * s ^ 2 ≤ ‖w + w0‖ ^ 2 := by
    rw [key]
    nlinarith [hs2, hsq, hhp]
  have hvsq : s ^ 2 ≤ ‖w + w0‖ ^ 2 := by nlinarith [hv2, sq_nonneg s]
  have hvs : s ≤ ‖w + w0‖ := by
    have := (sq_le_sq.mp hvsq)
    rwa [abs_of_nonneg hs, abs_of_nonneg (norm_nonneg (w + w0))] at this
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- Degenerate case `s = 0`.
    have hR0 : R = 0 :=
      le_antisymm (by rw [← hs0, mul_zero] at hR; exact hR) (le_trans (norm_nonneg _) h)
    have hn0 : ‖w ^ 2 - w0 ^ 2‖ = 0 := le_antisymm (by rw [hR0] at h; exact h) (norm_nonneg _)
    have hsqq : w ^ 2 = w0 ^ 2 := sub_eq_zero.mp (norm_eq_zero.mp hn0)
    have hfac0 : (w - w0) * (w + w0) = 0 := by rw [← hfac, sub_eq_zero]; exact hsqq
    rcases mul_eq_zero.mp hfac0 with h1 | h2
    · have hw : w = w0 := sub_eq_zero.mp h1
      rw [hw]
      simpa using hρ
    · have hw : w = -w0 := add_eq_zero_iff_eq_neg.mp h2
      have hconj : (w * starRingEnd ℂ w0).re = -(Complex.normSq w0) := by
        rw [hw, neg_mul, Complex.neg_re, Complex.mul_conj w0, Complex.ofReal_re]
      have hnn : Complex.normSq w0 = 0 := by
        have : 0 ≤ -(Complex.normSq w0) := by rw [← hconj]; exact hhp
        linarith [Complex.normSq_nonneg w0]
      have hw0 : w0 = 0 := Complex.normSq_eq_zero.mp hnn
      have hwz : w = 0 := by rw [hw, hw0, neg_zero]
      rw [hwz, hw0]
      simp [hρ]
  · -- Non-degenerate case `0 < s`: cancel the factor `s`.
    have h1 : ‖w - w0‖ * ‖w + w0‖ ≤ ρ * s := by rw [hnorm]; exact le_trans h hR
    have h2 : ‖w - w0‖ * s ≤ ‖w - w0‖ * ‖w + w0‖ :=
      mul_le_mul_of_nonneg_left hvs (norm_nonneg _)
    exact le_of_mul_le_mul_right (le_trans h2 h1) hspos

end Work.SeedCertRay
