import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge
import Submission.Work.Pert.PinLogDev.tau_num_le

/-!
# `Work.Pert.PinLogDev.tauC_sub_tau0_alpha`

Uniform comparison of the perturbed chart `τ_f = Work.Pert.tauC σ α`,
`σ = 1 - exp (2πiα)`, with the unperturbed chart `τ₀ w = -1/w` (`MandelDim.tau0`), in the
*relative* lattice regime

  `dist (α w) ℤ ≥ c ‖α‖ ‖w‖`,   `‖α‖ ‖w‖ ≤ 2`,   `c ≤ ‖w‖`,   `0 < c ≤ 1`.

**Two regimes.**

* `2π‖α‖‖w‖ ≤ 1/2`.  Then `‖αw‖ ≤ 1/(4π)` and the sharp Laurent expansion of `1/(1-e^{-z})` —
  encoded in the already-proved `Work.Pert.tauC_add_inv_le` — applies:
  `‖τ_f w + 1/w‖ ≤ ‖σ/α + 2πi‖/(π c) + 4π‖α‖`.  The second-order Taylor bound
  `‖e^{2πiα} - 1 - 2πiα‖ ≤ (2π‖α‖)² e^{2π‖α‖}` gives `‖σ/α + 2πi‖ ≤ 4π²‖α‖ e^{2π‖α‖}`,
  and `‖α‖ ≤ 2/c`, so `‖τ_f w - τ₀ w‖ ≤ [(4π/c)e^{2π‖α‖} + 4π]‖α‖`.
* `1/2 < 2π‖α‖‖w‖`.  Then `‖αw‖ > 1/(4π)`, so the lattice hypothesis forces the *absolute*
  separation `dist (αw) ℤ > c/(4π)`, and the elementary lower bound
  `Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge` gives `‖1 - e^{-2πiαw}‖ ≥ (3/4)(c/(4π))`.  The
  crude triangle inequality `‖τ_f w - τ₀ w‖ ≤ ‖σ‖/‖1 - e^{-2πiαw}‖ + 1/‖w‖` together with
  `‖σ‖ ≤ 2π‖α‖ e^{2π‖α‖}` and `1/‖w‖ = ‖α‖/‖αw‖ ≤ 4π‖α‖` then gives
  `‖τ_f w - τ₀ w‖ ≤ [(32π²/(3c))e^{2π‖α‖} + 4π]‖α‖`.

Both branches are absorbed into the single generous constant
`C = 100 · exp (2000/c + 100)` via `absorb_div_exp`.
-/

namespace Work.Pert.PinLogDev

open Complex

noncomputable section

/-- `u ≤ exp u` for every real `u`. -/
lemma le_exp_self (u : ℝ) : u ≤ Real.exp u := by
  have := Real.add_one_le_exp u
  linarith

/-- The second-order Taylor bound `‖exp x - 1 - x‖ ≤ ‖x‖² exp ‖x‖`, for every `x : ℂ`
(no smallness hypothesis). -/
lemma norm_exp_sub_one_sub_le (x : ℂ) :
    ‖Complex.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp x 2
  have hsum : (∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℂ)) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hsum] at h
  rw [show Complex.exp x - 1 - x = Complex.exp x - (1 + x) by ring]
  exact h

/-- Absorption of a `1/c`-factor into the exponential: for `0 < c`, `0 ≤ A ≤ 1000` and
`P ≤ 1000/c` one has `(A/c) · exp P ≤ exp (2000/c)`. -/
lemma absorb_div_exp {c A P : ℝ} (hc : 0 < c)
    (hA : A ≤ 1000) (hP : P ≤ 1000 / c) :
    (A / c) * Real.exp P ≤ Real.exp (2000 / c) := by
  have h1 : A / c ≤ 1000 / c := div_le_div_of_nonneg_right hA hc.le
  have h2 : 1000 / c ≤ Real.exp (1000 / c) := le_exp_self (1000 / c)
  have h3 : Real.exp P ≤ Real.exp (1000 / c) := Real.exp_le_exp.mpr hP
  have h4 : (A / c) * Real.exp P ≤ (1000 / c) * Real.exp (1000 / c) :=
    mul_le_mul h1 h3 (Real.exp_pos _).le (by positivity)
  have h5 : (1000 / c) * Real.exp (1000 / c) ≤ Real.exp (1000 / c) * Real.exp (1000 / c) :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have h6 : Real.exp (1000 / c) * Real.exp (1000 / c) = Real.exp (2000 / c) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h6] at h5
  linarith

/-- `‖1 - exp (2πiα)‖ ≤ 2π‖α‖ exp (2π‖α‖)`. -/
lemma norm_one_sub_exp_two_pi_I_mul_le (α : ℂ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖
      ≤ 2 * Real.pi * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖) := by
  have hx : ‖(2 * (Real.pi : ℂ) * Complex.I * α)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num
  have h := norm_one_sub_exp_le_mul_exp (2 * (Real.pi : ℂ) * Complex.I * α)
  rw [hx] at h
  exact h

theorem tauC_sub_tau0_alpha {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {σ α w : ℂ},
      σ = 1 - Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      c ≤ ‖w‖ → ‖α‖ * ‖w‖ ≤ 2 →
      c * (‖α‖ * ‖w‖) ≤ (⨅ k : ℤ, dist (α * w) (k : ℂ)) →
      ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ C * ‖α‖ := by
  refine ⟨100 * Real.exp (2000 / c + 100), by positivity, ?_⟩
  intro σ α w hσ hα hw hαw hlat
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hc hw
  have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hlat' : ∀ k : ℤ, c * (‖α‖ * ‖w‖) ≤ dist (α * w) (k : ℂ) := fun k =>
    le_trans hlat (ciInf_le ⟨0, by rintro b ⟨j, rfl⟩; exact dist_nonneg⟩ k)
  have hαle : ‖α‖ ≤ 2 / c := by
    rw [le_div_iff₀ hc]
    calc ‖α‖ * c ≤ ‖α‖ * ‖w‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg α)
      _ ≤ 2 := hαw
  have hp : 2 * Real.pi * ‖α‖ ≤ 1000 / c := by
    have h1 : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (2 / c) :=
      mul_le_mul_of_nonneg_left hαle (by positivity)
    have h2 : 2 * Real.pi * (2 / c) = 4 * Real.pi / c := by ring
    rw [h2] at h1
    have h3 : 4 * Real.pi / c ≤ 1000 / c :=
      div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) hc.le
    linarith
  have h4pi : 4 * Real.pi ≤ Real.exp (2000 / c) := by
    have h1 := le_exp_self (2000 / c)
    have h8 : (2000 : ℝ) ≤ 2000 / c := by
      rw [le_div_iff₀ hc]; nlinarith [hc1]
    linarith [Real.pi_lt_d2]
  have hc100 : (2 : ℝ) * Real.exp (2000 / c)
      ≤ 100 * Real.exp (2000 / c + 100) := by
    have h1 : (1 : ℝ) ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
    have h2 : Real.exp (2000 / c + 100) = Real.exp (2000 / c) * Real.exp 100 :=
      Real.exp_add _ _
    rw [h2]
    nlinarith [Real.exp_pos (2000 / c), h1]
  by_cases hcase : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2
  · -- ## Regime 1: `2π‖α‖‖w‖ ≤ 1/2`
    have h1 := Work.Pert.tauC_add_inv_le σ α w hα hwne hc hw hcase
    have hbeta : ‖σ / α + 2 * Real.pi * Complex.I‖
        ≤ 4 * Real.pi ^ 2 * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖) := by
      have hxn : ‖(2 * (Real.pi : ℂ) * Complex.I * α)‖ = 2 * Real.pi * ‖α‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
        norm_num
      have htail := norm_exp_sub_one_sub_le (2 * (Real.pi : ℂ) * Complex.I * α)
      rw [hxn] at htail
      have hnum : ‖σ + 2 * (Real.pi : ℂ) * Complex.I * α‖
          ≤ (2 * Real.pi * ‖α‖) ^ 2 * Real.exp (2 * Real.pi * ‖α‖) := by
        rw [hσ]
        rw [show 1 - Complex.exp (2 * Real.pi * Complex.I * α)
              + 2 * (Real.pi : ℂ) * Complex.I * α
            = -(Complex.exp (2 * Real.pi * Complex.I * α) - 1
                - 2 * (Real.pi : ℂ) * Complex.I * α) by ring, norm_neg]
        exact htail
      have hsplit : σ / α + 2 * Real.pi * Complex.I
          = (σ + 2 * (Real.pi : ℂ) * Complex.I * α) / α := by
        field_simp
        try ring
      rw [hsplit, norm_div, div_le_iff₀ hαpos]
      calc ‖σ + 2 * (Real.pi : ℂ) * Complex.I * α‖
          ≤ (2 * Real.pi * ‖α‖) ^ 2 * Real.exp (2 * Real.pi * ‖α‖) := hnum
        _ = (4 * Real.pi ^ 2 * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖)) * ‖α‖ := by ring
    have hB1 : ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * c)
        ≤ (4 * Real.pi ^ 2 * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖)) / (Real.pi * c) :=
      div_le_div_of_nonneg_right hbeta (by positivity)
    have hB2 : (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi = 4 * Real.pi * ‖α‖ := by
      rw [div_eq_iff Real.pi_ne_zero]; ring
    have hAc : (4 * Real.pi / c) * Real.exp (2 * Real.pi * ‖α‖)
        ≤ Real.exp (2000 / c) :=
      absorb_div_exp hc (by linarith [Real.pi_lt_d2]) hp
    have htau0 : Work.Pert.tauC σ α w - MandelDim.tau0 w
        = Work.Pert.tauC σ α w + 1 / w := by
      rw [MandelDim.tau0]; ring
    rw [htau0]
    calc ‖Work.Pert.tauC σ α w + 1 / w‖
        ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * c)
            + (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi := h1
      _ ≤ (4 * Real.pi ^ 2 * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖)) / (Real.pi * c)
            + 4 * Real.pi * ‖α‖ := by
          rw [hB2]; exact add_le_add hB1 le_rfl
      _ = ((4 * Real.pi / c) * Real.exp (2 * Real.pi * ‖α‖) + 4 * Real.pi) * ‖α‖ := by
          field_simp
          try ring
      _ ≤ (Real.exp (2000 / c) + Real.exp (2000 / c)) * ‖α‖ :=
          mul_le_mul_of_nonneg_right (add_le_add hAc h4pi) (norm_nonneg α)
      _ = 2 * Real.exp (2000 / c) * ‖α‖ := by ring
      _ ≤ 100 * Real.exp (2000 / c + 100) * ‖α‖ :=
          mul_le_mul_of_nonneg_right hc100 (norm_nonneg α)
  · -- ## Regime 2: `1/2 < 2π‖α‖‖w‖`
    have hbig : 1 / 2 < 2 * Real.pi * ‖α‖ * ‖w‖ := lt_of_not_ge hcase
    have hzgt : 1 / (4 * Real.pi) < ‖α‖ * ‖w‖ := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)]
      nlinarith [hbig, Real.pi_pos]
    have hκ : 0 < c / (4 * Real.pi) := by positivity
    have hsep : ∀ k : ℤ, c / (4 * Real.pi) ≤ ‖-(α * w) + (k : ℂ)‖ := by
      intro k
      have h1 := hlat' k
      have h3 : c / (4 * Real.pi) < c * (‖α‖ * ‖w‖) := by
        have h2 : c * (1 / (4 * Real.pi)) < c * (‖α‖ * ‖w‖) :=
          mul_lt_mul_of_pos_left hzgt hc
        have h5 : c / (4 * Real.pi) = c * (1 / (4 * Real.pi)) := by ring
        rw [h5]; exact h2
      have h4 : ‖α * w - (k : ℂ)‖ = dist (α * w) (k : ℂ) := (dist_eq_norm _ _).symm
      rw [show -(α * w) + (k : ℂ) = -(α * w - (k : ℂ)) by ring, norm_neg, h4]
      linarith
    have hden0 := Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge (-(α * w)) (c / (4 * Real.pi))
      hκ hsep
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (-(α * w))
        = -(2 * Real.pi * Complex.I * α * w) := by ring
    rw [harg] at hden0
    have hmin : min 1 (c / (4 * Real.pi)) = c / (4 * Real.pi) := by
      apply min_eq_right
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)).mpr
        (by nlinarith [hc1, Real.pi_gt_three])
    have hden : (3 / 4) * (c / (4 * Real.pi))
        ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖ := by
      rwa [hmin] at hden0
    have hdenpos : 0 < (3 / 4) * (c / (4 * Real.pi)) := by positivity
    have hσnorm := norm_one_sub_exp_two_pi_I_mul_le α
    have hw1 : 1 / ‖w‖ ≤ 4 * Real.pi * ‖α‖ := by
      have h1 : 1 < 4 * Real.pi * (‖α‖ * ‖w‖) := by
        have h := hzgt
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)] at h
        linarith [h]
      have h2 : 1 / ‖w‖ = ‖α‖ / (‖α‖ * ‖w‖) := by
        field_simp
      rw [h2, div_le_iff₀ (by positivity : (0 : ℝ) < ‖α‖ * ‖w‖)]
      nlinarith [h1, norm_nonneg α]
    have h2 : ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖
        ≤ (2 * Real.pi * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖))
            / ((3 / 4) * (c / (4 * Real.pi))) := by
      rw [hσ]
      exact div_le_div₀ (by positivity) hσnorm hdenpos hden
    have hA32 : 32 * Real.pi ^ 2 / 3 ≤ 1000 := by
      have hp4 : Real.pi < 4 := by linarith [Real.pi_lt_d2]
      have h1 : Real.pi ^ 2 ≤ 16 := by nlinarith [hp4, Real.pi_pos]
      linarith
    have hBC0 : ((32 * Real.pi ^ 2 / 3) / c) * Real.exp (2 * Real.pi * ‖α‖)
        ≤ Real.exp (2000 / c) := absorb_div_exp hc hA32 hp
    have hBC : (32 * Real.pi ^ 2 / (3 * c)) * Real.exp (2 * Real.pi * ‖α‖)
        ≤ Real.exp (2000 / c) := by
      rwa [show (32 * Real.pi ^ 2 / 3) / c = 32 * Real.pi ^ 2 / (3 * c) by ring] at hBC0
    have hsplit : Work.Pert.tauC σ α w - MandelDim.tau0 w
        = σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))) + 1 / w := by
      rw [Work.Pert.tauC, MandelDim.tau0]; ring
    rw [hsplit]
    calc ‖σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))) + 1 / w‖
        ≤ ‖σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w)))‖ + ‖1 / w‖ :=
          norm_add_le _ _
      _ = ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖ + 1 / ‖w‖ := by
          rw [norm_div]; simp
      _ ≤ (2 * Real.pi * ‖α‖ * Real.exp (2 * Real.pi * ‖α‖))
            / ((3 / 4) * (c / (4 * Real.pi))) + 4 * Real.pi * ‖α‖ := add_le_add h2 hw1
      _ = ((32 * Real.pi ^ 2 / (3 * c)) * Real.exp (2 * Real.pi * ‖α‖)
            + 4 * Real.pi) * ‖α‖ := by
          field_simp
          try ring
      _ ≤ (Real.exp (2000 / c) + Real.exp (2000 / c)) * ‖α‖ :=
          mul_le_mul_of_nonneg_right (add_le_add hBC h4pi) (norm_nonneg α)
      _ = 2 * Real.exp (2000 / c) * ‖α‖ := by ring
      _ ≤ 100 * Real.exp (2000 / c + 100) * ‖α‖ :=
          mul_le_mul_of_nonneg_right hc100 (norm_nonneg α)

end

end Work.Pert.PinLogDev
