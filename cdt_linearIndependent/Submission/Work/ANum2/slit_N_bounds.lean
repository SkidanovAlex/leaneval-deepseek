import Mathlib
import Submission.Work.ANum2.Der2

namespace Work.ANum2

open Submission.CDTPlan Complex

noncomputable section

/-! ## Elementary norm helpers

The bounds below are obtained by the triangle inequality applied to the explicit closed forms of
`Nf`, `Nd`, `Ndd` (see `Der2`), so we first collect the small bookkeeping lemmas about norms in `ℂ`
that the case analysis needs. -/

/-- The norm of a real number viewed in `ℂ` is its absolute value. -/
lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-- Triangle inequality for a sum of four terms. -/
lemma norm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le (a + b + c) d
    _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by linarith [norm_add_le (a + b) c]
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by linarith [norm_add_le a b]

/-- Triangle inequality for `a - b + c + d`. -/
lemma norm_sub_add_add_le (a b c d : ℂ) : ‖a - b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a - b + c + d‖ ≤ ‖a - b + c‖ + ‖d‖ := norm_add_le (a - b + c) d
    _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by linarith [norm_add_le (a - b) c]
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by linarith [norm_sub_le a b]

/-- Triangle inequality for a sum of three terms. -/
lemma norm_add3_le (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le a b]

/-- Quotient version of the triangle inequality: an upper bound for the numerator together with a
positive lower bound for the denominator bounds the quotient. -/
lemma norm_div_le' {a b : ℂ} {C D : ℝ} (hC : 0 ≤ C) (ha : ‖a‖ ≤ C) (hD : 0 < D)
    (hb : D ≤ ‖b‖) : ‖a / b‖ ≤ C / D := by
  rw [norm_div]
  exact div_le_div₀ hC ha hD hb

/-- **Magnitude bounds for `N`, `N'`, `N''` on a disc.**

With `Q r z = (1+r)² - 2(1-6r+r²)z + (1+r)²z²`, `S r z = √(Q r z)` (principal branch),
`P r z = (1+r)² - 2(r-1)²z + (1+r)²z²` and
`N = P + (1+r)(z-1)S`, `N' = -2(r-1)² + 2(1+r)²z + (1+r)S + (1+r)(z-1)Q'/(2S)`,
`N'' = 2(1+r)² + (1+r)Q'/S + (1+r)(z-1)(2QQ''-Q'²)/(4S³)`, and given a disc
`{z : ‖z - c‖ ≤ ρ}` contained in the open unit disc on which `Q` is bounded away from `0`
(the hypothesis `hQlo`), the three values at `w` are bounded by the stated explicit quantities:
`A = (1+r)²`, `Qp` an upper bound for `|Q'|`, `Qc` the size of `Q(c)`, `Qhi` an upper bound and
`Slo²` a lower bound for `|Q|`, `whi`/`wm1` upper bounds for `|w|`/`|w-1|` and `Shi` an upper
bound for `|S w|`. -/
theorem slit_N_bounds (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (c w : ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hw : ‖w - c‖ ≤ ρ) (hdisc : ‖c‖ + ρ < 1) (hwlo : ρ < ‖c‖)
    (hQlo : ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) <
      ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖) :
    let A : ℝ := (1 + r) ^ 2
    let Qp : ℝ := ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * A)
    let Qc : ℝ := ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
    let Qhi : ℝ := Qc + ρ * Qp
    let Slo : ℝ := Real.sqrt (Qc - ρ * Qp)
    let Shi : ℝ := Real.sqrt Qhi
    let whi : ℝ := ‖c‖ + ρ
    let wm1 : ℝ := ‖c - 1‖ + ρ
    ‖Work.ANum2.Ndd r w‖ ≤ 2 * A + (1 + r) * Qp / Slo
        + (1 + r) * wm1 * (2 * Qhi * (2 * A) + Qp ^ 2) / (4 * Slo ^ 3) ∧
    ‖Work.ANum2.Nd r w‖ ≤ 2 * (r - 1) ^ 2 + 2 * A * whi + (1 + r) * Shi
        + (1 + r) * wm1 * Qp / (2 * Slo) ∧
    ‖Work.ANum2.Nf r w‖ ≤ A + 2 * (r - 1) ^ 2 * whi + A * whi ^ 2 + (1 + r) * wm1 * Shi := by
  dsimp only
  -- name the auxiliary real quantities and unfold the dependent ones
  set A : ℝ := (1 + r) ^ 2 with hA
  set Qp : ℝ := ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * A) with hQp
  set Qc : ℝ := ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖ with hQc
  set Qhi : ℝ := Qc + ρ * Qp with hQhi
  set Slo : ℝ := Real.sqrt (Qc - ρ * Qp) with hSlo
  set Shi : ℝ := Real.sqrt Qhi with hShi
  set whi : ℝ := ‖c‖ + ρ with hwhi
  set wm1 : ℝ := ‖c - 1‖ + ρ with hwm1
  have hA0 : 0 < A := by rw [hA]; exact pow_pos (by linarith : (0:ℝ) < 1 + r) 2
  -- `Qp` is `‖Q'(c)‖ + ρ‖Q''‖`
  have hQp_eq : Qp = ‖Qd r c‖ + ρ * (2 * A) := by rw [hQp, Qd_apply]
  have hQp0 : 0 ≤ Qp := by rw [hQp_eq]; positivity
  -- distance bounds
  have hwhi_le : ‖w‖ ≤ whi := by
    rw [hwhi]
    calc ‖w‖ = ‖(w - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ρ + ‖c‖ := by linarith
      _ = ‖c‖ + ρ := by ring
  have hwm1_le : ‖w - 1‖ ≤ wm1 := by
    rw [hwm1]
    calc ‖w - 1‖ ≤ ‖w - c‖ + ‖c - 1‖ := by
            have h : w - 1 = (w - c) + (c - 1) := by ring
            rw [h]; exact norm_add_le _ _
      _ ≤ ρ + ‖c - 1‖ := by linarith
      _ = ‖c - 1‖ + ρ := by ring
  -- Taylor expansion of the quadratic `Q` about `c` (`Q` is a degree-two polynomial)
  have hQdiffeq : Qf r w - Qf r c = Qd r c * (w - c) + (((1 + r) ^ 2 : ℝ) : ℂ) * (w - c) ^ 2 := by
    rw [Qf_apply r w, Qf_apply r c, Qd_apply r c]
    push_cast
    ring
  have hQdiff : ‖Qf r w - Qf r c‖ ≤ ρ * Qp := by
    rw [hQdiffeq]
    have h1 : ‖Qd r c * (w - c)‖ = ‖Qd r c‖ * ‖w - c‖ := norm_mul _ _
    have h2 : ‖(((1 + r) ^ 2 : ℝ) : ℂ) * (w - c) ^ 2‖ = (1 + r) ^ 2 * ‖w - c‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_ofReal_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖Qd r c * (w - c) + (((1 + r) ^ 2 : ℝ) : ℂ) * (w - c) ^ 2‖
        ≤ ‖Qd r c * (w - c)‖ + ‖(((1 + r) ^ 2 : ℝ) : ℂ) * (w - c) ^ 2‖ := norm_add_le _ _
      _ = ‖Qd r c‖ * ‖w - c‖ + (1 + r) ^ 2 * ‖w - c‖ ^ 2 := by rw [h1, h2]
      _ ≤ ‖Qd r c‖ * ρ + (1 + r) ^ 2 * ρ ^ 2 := by
          have hw0 : 0 ≤ ‖w - c‖ := norm_nonneg _
          have hsq : ‖w - c‖ ^ 2 ≤ ρ ^ 2 := by nlinarith
          have hle1 : ‖Qd r c‖ * ‖w - c‖ ≤ ‖Qd r c‖ * ρ :=
            mul_le_mul_of_nonneg_left hw (norm_nonneg _)
          have hle2 : (1 + r) ^ 2 * ‖w - c‖ ^ 2 ≤ (1 + r) ^ 2 * ρ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          linarith
      _ ≤ ρ * Qp := by
          rw [hQp_eq, hA]
          have hnn : 0 ≤ (1 + r) ^ 2 * ρ ^ 2 := by positivity
          nlinarith [hnn]
  have hQdweq : Qd r w = Qd r c + (((2 * (1 + r) ^ 2 : ℝ)) : ℂ) * (w - c) := by
    rw [Qd_apply r w, Qd_apply r c]
    push_cast
    ring
  have hQd_w : ‖Qd r w‖ ≤ Qp := by
    rw [hQdweq]
    calc ‖Qd r c + (((2 * (1 + r) ^ 2 : ℝ)) : ℂ) * (w - c)‖
        ≤ ‖Qd r c‖ + ‖(((2 * (1 + r) ^ 2 : ℝ)) : ℂ) * (w - c)‖ := norm_add_le _ _
      _ = ‖Qd r c‖ + 2 * (1 + r) ^ 2 * ‖w - c‖ := by
            rw [norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ ‖Qd r c‖ + 2 * (1 + r) ^ 2 * ρ := by
            have : 2 * (1+r)^2 * ‖w-c‖ ≤ 2*(1+r)^2*ρ := mul_le_mul_of_nonneg_left hw (by positivity)
            linarith
      _ ≤ Qp := by
            rw [hQp_eq, hA]
            nlinarith
  -- `Qc` is the size of `Q(c)`
  have hQfc : Qf r c = (1 + (r:ℂ))^2 * c^2 - 2*(1 - 6*(r:ℂ) + (r:ℂ)^2)*c + (1+(r:ℂ))^2 := by
    rw [Qf_apply r c]; ring
  have hQc_eq : Qc = ‖Qf r c‖ := by rw [hQc, hQfc]
  -- upper and lower bounds for `|Q(w)|`
  have hQhi0 : ‖Qf r w‖ ≤ Qhi := by
    rw [hQhi, hQc_eq]
    calc ‖Qf r w‖ = ‖Qf r c + (Qf r w - Qf r c)‖ := by
            rw [show Qf r c + (Qf r w - Qf r c) = Qf r w by ring]
      _ ≤ ‖Qf r c‖ + ‖Qf r w - Qf r c‖ := norm_add_le _ _
      _ ≤ ‖Qf r c‖ + ρ * Qp := by linarith [hQdiff]
  have hQlo0 : Qc - ρ * Qp ≤ ‖Qf r w‖ := by
    rw [hQc_eq]
    have h1 : ‖Qf r c‖ ≤ ‖Qf r c - Qf r w‖ + ‖Qf r w‖ := by
      calc ‖Qf r c‖ = ‖(Qf r c - Qf r w) + Qf r w‖ := by
              rw [show (Qf r c - Qf r w) + Qf r w = Qf r c by ring]
        _ ≤ ‖Qf r c - Qf r w‖ + ‖Qf r w‖ := norm_add_le _ _
    have h2 : ‖Qf r c - Qf r w‖ ≤ ρ * Qp := by rw [norm_sub_rev]; exact hQdiff
    linarith
  have hwhi1 : ‖w‖ < 1 := lt_of_le_of_lt hwhi_le hdisc
  have hQw_ne : Qf r w ≠ 0 := by
    rw [show Qf r w = Work.APsi.slitQ r w from by rw [Qf_apply r w]; rfl]
    exact Work.APsi.slitQ_ne_zero_of_norm_lt_one r hr0 hr1 hwhi1
  have hSfsq : ‖Sf r w‖ ^ 2 = ‖Qf r w‖ := by rw [← norm_pow, Sf_sq]
  have hQhi0n : 0 ≤ Qhi := by rw [hQhi, hQc_eq]; positivity
  -- the bounds on `|S w|`
  have hSlole : Slo ≤ ‖Sf r w‖ := by
    rw [hSlo, Real.sqrt_le_left (norm_nonneg _), hSfsq]
    exact hQlo0
  have hSfhi : ‖Sf r w‖ ≤ Shi := by
    rw [hShi, Real.le_sqrt (norm_nonneg _) hQhi0n, hSfsq]
    exact hQhi0
  have hSlopos : 0 < Slo := by
    rw [hSlo]; exact Real.sqrt_pos_of_pos (by linarith)
  have h2c : ‖(2:ℂ)‖ = 2 := by norm_num
  have h4c : ‖(4:ℂ)‖ = 4 := by norm_num
  have hsq1 : (1 + (r:ℂ))^2 = (((1+r)^2 : ℝ) : ℂ) := by push_cast; ring
  have hc3 : (1 + (r:ℂ)) = ((1+r : ℝ) : ℂ) := by push_cast; ring
  have hsq2 : ((r:ℂ) - 1)^2 = (((r-1)^2 : ℝ) : ℂ) := by push_cast; ring
  have hneg : -2 * ((r:ℂ)-1)^2 = -(((2*(r-1)^2 : ℝ)) : ℂ) := by push_cast; ring
  -- ### the bound on `N`
  have hNfval : Nf r w = (1 + (r:ℂ))^2 - 2*((r:ℂ)-1)^2 * w + (1+(r:ℂ))^2 * w^2
      + (1+(r:ℂ)) * (w - 1) * Sf r w := by
    rw [Nf_apply r w, ← Sf_apply r w]
  have hNf : ‖Nf r w‖ ≤ A + 2*(r-1)^2*whi + A*whi^2 + (1+r)*wm1*Shi := by
    rw [hNfval]
    have e1 : ‖(1 + (r:ℂ))^2‖ = (1+r)^2 := by
      rw [hsq1, norm_ofReal_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have e2 : ‖2*((r:ℂ)-1)^2 * w‖ = 2*(r-1)^2*‖w‖ := by
      rw [hsq2, norm_mul, norm_mul, h2c, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    have e3 : ‖(1+(r:ℂ))^2 * w^2‖ = (1+r)^2 * ‖w‖^2 := by
      rw [hsq1, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (sq_nonneg _), norm_pow]
    have e4 : ‖(1+(r:ℂ)) * (w-1) * Sf r w‖ = (1+r) * ‖w-1‖ * ‖Sf r w‖ := by
      rw [hc3, norm_mul, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by linarith [hr0])]
    calc ‖(1 + (r:ℂ))^2 - 2*((r:ℂ)-1)^2 * w + (1+(r:ℂ))^2 * w^2 + (1+(r:ℂ)) * (w-1) * Sf r w‖
        ≤ ‖(1 + (r:ℂ))^2‖ + ‖2*((r:ℂ)-1)^2 * w‖ + ‖(1+(r:ℂ))^2 * w^2‖ + ‖(1+(r:ℂ)) * (w-1) * Sf r w‖ :=
          norm_sub_add_add_le _ _ _ _
      _ = (1+r)^2 + 2*(r-1)^2*‖w‖ + (1+r)^2*‖w‖^2 + (1+r)*‖w-1‖*‖Sf r w‖ := by rw [e1,e2,e3,e4]
      _ ≤ A + 2*(r-1)^2*whi + A*whi^2 + (1+r)*wm1*Shi := by
          rw [hA]
          have h1 : 2*(r-1)^2*‖w‖ ≤ 2*(r-1)^2*whi :=
            mul_le_mul_of_nonneg_left hwhi_le (by positivity)
          have h2 : (1+r)^2*‖w‖^2 ≤ (1+r)^2*whi^2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwhi_le 2) (by positivity)
          have h3 : (1+r)*‖w-1‖*‖Sf r w‖ ≤ (1+r)*wm1*Shi := by
            have hb : ‖w-1‖*‖Sf r w‖ ≤ wm1*Shi :=
              mul_le_mul hwm1_le hSfhi (norm_nonneg _) (le_trans (norm_nonneg _) hwm1_le)
            calc (1+r)*‖w-1‖*‖Sf r w‖ = (1+r)*(‖w-1‖*‖Sf r w‖) := by ring
              _ ≤ (1+r)*(wm1*Shi) := mul_le_mul_of_nonneg_left hb (by linarith [hr0])
              _ = (1+r)*wm1*Shi := by ring
          linarith
  -- ### the bound on `N'`
  have hNdval : Nd r w = -2*((r:ℂ)-1)^2 + 2*(1+(r:ℂ))^2 * w
      + (1+(r:ℂ)) * Sf r w + (1+(r:ℂ)) * (w-1) * (Qd r w / (2 * Sf r w)) := by
    rw [Nd_apply r w]
  have hNd : ‖Nd r w‖ ≤ 2*(r-1)^2 + 2*A*whi + (1+r)*Shi + (1+r)*wm1*Qp/(2*Slo) := by
    rw [hNdval]
    have e1 : ‖-2*((r:ℂ)-1)^2‖ = 2*(r-1)^2 := by
      rw [hneg, norm_neg, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    have e2 : ‖2*(1+(r:ℂ))^2 * w‖ = 2*(1+r)^2*‖w‖ := by
      rw [hsq1, norm_mul, norm_mul, h2c, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    have e3 : ‖(1+(r:ℂ)) * Sf r w‖ = (1+r)*‖Sf r w‖ := by
      rw [hc3, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by linarith [hr0])]
    have e4 : ‖(1+(r:ℂ)) * (w-1) * (Qd r w / (2 * Sf r w))‖
        = (1+r)*‖w-1‖*‖Qd r w / (2 * Sf r w)‖ := by
      rw [hc3, norm_mul, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by linarith [hr0])]
    have e5 : ‖Qd r w / (2 * Sf r w)‖ ≤ Qp / (2*Slo) := by
      apply norm_div_le' hQp0 hQd_w (by linarith)
      rw [norm_mul, h2c]
      linarith [hSlole]
    have e4b : (1+r)*‖w-1‖*‖Qd r w / (2 * Sf r w)‖ ≤ (1+r)*wm1*Qp/(2*Slo) := by
      have hb : ‖w-1‖ * ‖Qd r w / (2*Sf r w)‖ ≤ wm1 * (Qp/(2*Slo)) :=
        mul_le_mul hwm1_le e5 (norm_nonneg _) (le_trans (norm_nonneg _) hwm1_le)
      calc (1+r)*‖w-1‖*‖Qd r w / (2*Sf r w)‖ = (1+r)*(‖w-1‖*‖Qd r w / (2*Sf r w)‖) := by ring
        _ ≤ (1+r)*(wm1*(Qp/(2*Slo))) := mul_le_mul_of_nonneg_left hb (by linarith [hr0])
        _ = (1+r)*wm1*Qp/(2*Slo) := by ring
    calc ‖-2*((r:ℂ)-1)^2 + 2*(1+(r:ℂ))^2 * w + (1+(r:ℂ)) * Sf r w
            + (1+(r:ℂ)) * (w-1) * (Qd r w / (2 * Sf r w))‖
        ≤ ‖-2*((r:ℂ)-1)^2‖ + ‖2*(1+(r:ℂ))^2 * w‖ + ‖(1+(r:ℂ)) * Sf r w‖
            + ‖(1+(r:ℂ)) * (w-1) * (Qd r w / (2 * Sf r w))‖ := norm_add4_le _ _ _ _
      _ = 2*(r-1)^2 + 2*(1+r)^2*‖w‖ + (1+r)*‖Sf r w‖ + (1+r)*‖w-1‖*‖Qd r w / (2*Sf r w)‖ :=
            by rw [e1,e2,e3,e4]
      _ ≤ 2*(r-1)^2 + 2*A*whi + (1+r)*Shi + (1+r)*wm1*Qp/(2*Slo) := by
          rw [hA]
          have h1 : 2*(1+r)^2*‖w‖ ≤ 2*(1+r)^2*whi :=
            mul_le_mul_of_nonneg_left hwhi_le (by positivity)
          have h2 : (1+r)*‖Sf r w‖ ≤ (1+r)*Shi :=
            mul_le_mul_of_nonneg_left hSfhi (by linarith [hr0])
          linarith [e4b]
  -- ### the bound on `N''`
  have hNddval : Ndd r w = 2*(1+(r:ℂ))^2 + (1+(r:ℂ)) * (Qd r w / Sf r w)
      + (1+(r:ℂ)) * (w-1) * ((2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)) := by
    rw [Ndd_apply r w]
  have hNdd : ‖Ndd r w‖ ≤ 2*A + (1+r)*Qp/Slo + (1+r)*wm1*(2*Qhi*(2*A) + Qp^2)/(4*Slo^3) := by
    rw [hNddval]
    have e1 : ‖2*(1+(r:ℂ))^2‖ = 2*(1+r)^2 := by
      rw [hsq1, norm_mul, h2c, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    have e2 : ‖(1+(r:ℂ)) * (Qd r w / Sf r w)‖ = (1+r)*‖Qd r w / Sf r w‖ := by
      rw [hc3, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by linarith [hr0])]
    have e3 : ‖(1+(r:ℂ)) * (w-1) * ((2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3))‖
        = (1+r)*‖w-1‖*‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖ := by
      rw [hc3, norm_mul, norm_mul, norm_ofReal_eq_abs, abs_of_nonneg (by linarith [hr0])]
    have e4 : ‖Qd r w / Sf r w‖ ≤ Qp / Slo := norm_div_le' hQp0 hQd_w hSlopos hSlole
    have hQddn : ‖Qdd r w‖ = 2*(1+r)^2 := by
      rw [Qdd_apply, norm_mul, hsq1, h2c, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]
    have hnum : ‖2*Qf r w*Qdd r w - Qd r w*Qd r w‖ ≤ 2*Qhi*(2*A) + Qp^2 := by
      have hnd : ‖2*Qf r w*Qdd r w‖ = 2*‖Qf r w‖*‖Qdd r w‖ := by
        rw [norm_mul, norm_mul, h2c]
      calc ‖2*Qf r w*Qdd r w - Qd r w*Qd r w‖
          ≤ ‖2*Qf r w*Qdd r w‖ + ‖Qd r w*Qd r w‖ := norm_sub_le _ _
        _ = 2*‖Qf r w‖*‖Qdd r w‖ + ‖Qd r w‖^2 := by rw [hnd, norm_mul]; ring
        _ ≤ 2*Qhi*(2*A) + Qp^2 := by
            have hqd0 : 0 ≤ ‖Qdd r w‖ := norm_nonneg _
            have h1 : 2*‖Qf r w‖*‖Qdd r w‖ ≤ 2*Qhi*‖Qdd r w‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQhi0 (by norm_num)) hqd0
            have h2 : 2*Qhi*‖Qdd r w‖ = 2*Qhi*(2*A) := by rw [hQddn, hA]
            have h3 : ‖Qd r w‖^2 ≤ Qp^2 := pow_le_pow_left₀ (norm_nonneg _) hQd_w 2
            linarith
    have e5 : ‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖
        ≤ (2*Qhi*(2*A) + Qp^2)/(4*Slo^3) := by
      apply norm_div_le' (by positivity) hnum (by positivity) _
      rw [norm_mul, h4c, norm_pow]
      have h3 : Slo^3 ≤ ‖Sf r w‖^3 := pow_le_pow_left₀ (le_of_lt hSlopos) hSlole 3
      linarith
    have e3b : (1+r)*‖w-1‖*‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖
        ≤ (1+r)*wm1*(2*Qhi*(2*A) + Qp^2)/(4*Slo^3) := by
      have hb : ‖w-1‖ * ‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖
          ≤ wm1 * ((2*Qhi*(2*A) + Qp^2)/(4*Slo^3)) :=
        mul_le_mul hwm1_le e5 (norm_nonneg _) (le_trans (norm_nonneg _) hwm1_le)
      calc (1+r)*‖w-1‖*‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖
            = (1+r)*(‖w-1‖*‖(2*Qf r w*Qdd r w - Qd r w*Qd r w) / (4 * Sf r w^3)‖) := by ring
        _ ≤ (1+r)*(wm1*((2*Qhi*(2*A) + Qp^2)/(4*Slo^3))) :=
              mul_le_mul_of_nonneg_left hb (by linarith [hr0])
        _ = (1+r)*wm1*(2*Qhi*(2*A) + Qp^2)/(4*Slo^3) := by ring
    calc ‖2*(1+(r:ℂ))^2 + (1+(r:ℂ))*(Qd r w/Sf r w)
            + (1+(r:ℂ))*(w-1)*((2*Qf r w*Qdd r w - Qd r w*Qd r w)/(4 * Sf r w^3))‖
        ≤ ‖2*(1+(r:ℂ))^2‖ + ‖(1+(r:ℂ))*(Qd r w/Sf r w)‖
            + ‖(1+(r:ℂ))*(w-1)*((2*Qf r w*Qdd r w - Qd r w*Qd r w)/(4 * Sf r w^3))‖ :=
              norm_add3_le _ _ _
      _ = 2*(1+r)^2 + (1+r)*‖Qd r w/Sf r w‖
            + (1+r)*‖w-1‖*‖(2*Qf r w*Qdd r w - Qd r w*Qd r w)/(4 * Sf r w^3)‖ := by rw [e1,e2,e3]
      _ ≤ 2*A + (1+r)*Qp/Slo + (1+r)*wm1*(2*Qhi*(2*A) + Qp^2)/(4*Slo^3) := by
          rw [hA]
          have h1 : (1+r)*‖Qd r w/Sf r w‖ ≤ (1+r)*(Qp/Slo) :=
            mul_le_mul_of_nonneg_left e4 (by linarith [hr0])
          have h1b : (1+r)*(Qp/Slo) = (1+r)*Qp/Slo := by ring
          linarith [e3b, h1, h1b]
  exact ⟨hNdd, hNd, hNf⟩

end

end Work.ANum2
