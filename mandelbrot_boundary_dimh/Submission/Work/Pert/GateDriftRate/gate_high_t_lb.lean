import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_geom_facts

/-!
# PERT · `Work.Pert.GateDriftRate.gate_high_t_lb`

The *lower* bound on the "level" `t = Im (α w)` of a point `w` of the lower gate
`Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` lying in the upper half plane:

  `((Re α - Im α)/2) * (|Im w| - Re w - Ξ) + (Re α * Ξ - 1) ≤ Im (α w)`.

## Math

Write `p + i q = 1/α`, so that `(1/α).re = p > 0` and `|q| ≤ p`, and set
`z = w - Ξ` (so `Im z = Im w > 0`).  The first cone condition defining the gate reads
`Re z + p + |Im z + q| > 0`, while the statement, cleared of denominators, is the single
inequality

  `((Re α + Im α)/2) * (Re z + Im z) ≥ -1`.

Since `z⁻¹ = p + i q` gives `(Re α + Im α)/2 = (p - q)/(2 (p² + q²))`, this becomes
`(p - q) (Re z + Im z) ≥ -2 (p² + q²)`, and the gate condition yields
`Re z + Im z > -(p + |q|)`.  Multiplying by the positive `p - q` it suffices to know
`(p - q) (p + |q|) ≤ 2 (p² + q²)`, which holds in both cases (`q ≥ 0`: `p² - q² ≤ 2(p²+q²)`;
`q < 0`: `(p - q)² ≤ 2(p² + q²)`).

The second cone condition (`Re w + Ξ < |Im w|`) is not needed here.
-/

namespace Work.Pert.GateDriftRate

open Complex

theorem gate_high_t_lb {Ξ : ℝ} {α w : ℂ}
    (hInF1 : MandelDim.InF1 α) (hw : w ∈ Work.Pert.Qm Ξ α) (hy : 0 < w.im) :
    (α.re - α.im) / 2 * (|w.im| - w.re - Ξ) + (α.re * Ξ - 1) ≤ (α * w).im := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hαne : α ≠ 0 := by intro h; rw [h] at hαre; simp at hαre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have hlt := abs_lt.mp hInF1
  have hAsum : 0 < (α.re + α.im) / 2 := by linarith [hlt.1]
  -- The key identity `(Re α + Im α) * |1/α|² = Re (1/α) - Im (1/α)`.
  have hkey_id : (α.re + α.im) * ((1/α).re ^ 2 + (1/α).im ^ 2)
      = (1/α).re - (1/α).im := by
    have hns' : Complex.normSq α ≠ 0 := ne_of_gt hns
    rw [one_div, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    field_simp
    ring
  set p := (1/α).re with hp
  set q := (1/α).im with hq
  have hid : ((α.re + α.im)/2) * (2 * (p^2 + q^2)) = p - q := by linarith [hkey_id]
  have hp_pos : 0 < p := by rw [hp, one_div, Complex.inv_re]; exact div_pos hαre hns
  have hspos : 0 < 2 * (p^2 + q^2) := by nlinarith [sq_nonneg q, hp_pos]
  have hpq_lt : 0 < p - q := by
    have h := mul_pos hAsum hspos; linarith [hid]
  -- The first cone condition of the gate, in coordinates.
  have hkey := (Work.Pert.gate_geom_facts hInF1 hw).2.2.1
  have hkey' : w.re + |w.im + q| > Ξ - p := hkey
  have hx : -(p + |q|) < w.re + w.im - Ξ := by
    have h1 : |w.im + q| ≤ w.im + |q| := by
      simpa [abs_of_pos hy] using abs_add_le w.im q
    linarith
  have hprod : (p - q) * (p + |q|) ≤ 2 * (p^2 + q^2) := by
    rcases le_or_gt 0 q with hq0 | hq0
    · rw [abs_of_nonneg hq0]; nlinarith [sq_nonneg q]
    · rw [abs_of_neg hq0]; nlinarith [sq_nonneg (p + q)]
  have hbmul : -(2 * (p^2 + q^2)) ≤ (p - q) * (w.re + w.im - Ξ) := by
    have h2 : (p - q) * (-(p + |q|)) ≤ (p - q) * (w.re + w.im - Ξ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hx) (le_of_lt hpq_lt)
    nlinarith [h2, hprod]
  have hAeq : (α.re + α.im)/2 = (p - q)/(2 * (p^2 + q^2)) := by
    rw [eq_div_iff (ne_of_gt hspos)]; linarith [hid]
  have hfin : -1 ≤ ((α.re + α.im)/2) * (w.re + w.im - Ξ) := by
    rw [hAeq, div_mul_eq_mul_div, le_div_iff₀ hspos]
    nlinarith [hbmul]
  rw [abs_of_pos hy, Complex.mul_im]
  linarith [hfin]

end Work.Pert.GateDriftRate
