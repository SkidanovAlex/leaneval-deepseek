import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.TauCGate.one_sub_exp_two_pi_I_ge
import Submission.Work.Pert.TauCGate.one_sub_exp_two_pi_I_le
import Submission.Work.Pert.TauCGate.sfun_sub_sigma_u0_le

/-!
# PERT · `Work.Pert.tauC_norm_le_gate_five`

The near-translation hypothesis `‖F_f w - (w + 1)‖ ≤ 1/32` on the lower gate `Qm Ξ α` is strong
enough to bound the point value of the universal cover `τ_f = tauC σ α` by the absolute constant
`5`, uniformly in the perturbation:

  `∀ w ∈ Qm Ξ α, ‖τ_f w‖ ≤ 5` .

No smallness of `Ξ` or of `‖α‖ Ξ` enters, and the distance to the lattice `ℤ/α` is never used: it
is the near-translation, not the geometry of the gate, that bounds `τ_f` here.

## Proof

Write `z = 2πi α`, `τ = τ_f w`, `s = sfun u σ α w = σ u(τ)/(1 + τ u(τ))`.  The hypothesis
`‖F_f w - (w+1)‖ ≤ 1/32` reads `‖log (1-s)/(2πi α) - 1‖ ≤ 1/32`, i.e.

  `log (1 - s) = z + δ`,  `‖δ‖ ≤ π ‖α‖/16` ,

and (since `1 - s = 0` would force `δ = -z`, impossible as `δ` is small and `α ≠ 0`) also
`1 - s = exp (z + δ)`.  Together with the normalisation `1 - σ u 0 = exp z =: q` this gives

  `s - σ u 0 = q - exp (z + δ)`,  so  `‖s - σ u 0‖ ≤ ‖α‖/4`

(the `exp` difference is `q(1 - exp δ)` and `e^{2π‖α‖}(‖δ‖ + ‖δ‖²) ≤ 0.225‖α‖`).  On the other
hand `‖σ u 0‖ = ‖1 - exp z‖` lies between `(28/5)‖α‖` and `(36/5)‖α‖`, so

  `‖s‖ ≥ (28/5 - 1/4)‖α‖ = (107/20)‖α‖`,  `‖σ‖ ≤ 2·(36/5)‖α‖ = (72/5)‖α‖`.

Finally `s(1 + τ u τ) = σ u τ` (the case `1 + τ u τ = 0` is excluded because it would give `s = 0`)
and hence `s τ u τ = σ u τ - s`, so

  `‖τ‖ = ‖σ u τ - s‖/(‖s‖ ‖u τ‖) ≤ ‖σ‖/‖s‖ + 1/‖u τ‖ ≤ (72/5)/(107/20) + 2 ≤ 3 + 2 = 5`,

using `‖u τ‖ ≥ 1/2` from the hypothesis `hτQ` (`τ` lands in the ball on which `u` is bounded below
by `1/2`) and `u 0` likewise.

The two `exp` bounds and the `δ`-estimate are proved in `Submission/Work/Pert/TauCGate/`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- Lower bound `(28/5)‖α‖ ≤ ‖1 - exp (2πi α)‖` for `‖α‖ ≤ 1/64` (see
`Work.Pert.TauCGate.one_sub_exp_two_pi_I_ge`). -/
private theorem one_sub_exp_two_pi_I_ge_local {α : ℂ} (hα : ‖α‖ ≤ 1 / 64) :
    (28 / 5) * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ :=
  Work.Pert.TauCGate.one_sub_exp_two_pi_I_ge hα

/-- Upper bound `‖1 - exp (2πi α)‖ ≤ (36/5)‖α‖` for `‖α‖ ≤ 1/64` (see
`Work.Pert.TauCGate.one_sub_exp_two_pi_I_le`). -/
private theorem one_sub_exp_two_pi_I_le_local {α : ℂ} (hα : ‖α‖ ≤ 1 / 64) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ ≤ (36 / 5) * ‖α‖ :=
  Work.Pert.TauCGate.one_sub_exp_two_pi_I_le hα

/-- The near-translation forces `sfun` to be within `‖α‖/4` of the normalisation value `σ u 0`
(see `Work.Pert.TauCGate.sfun_sub_sigma_u0_le`). -/
private theorem sfun_sub_sigma_u0_le_local {α σ : ℂ} {u : ℂ → ℂ} {w : ℂ}
    (hα64 : ‖α‖ ≤ 1 / 64) (hαne : α ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hD : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    ‖Work.Pert.sfun u σ α w - σ * u 0‖ ≤ ‖α‖ / 4 :=
  Work.Pert.TauCGate.sfun_sub_sigma_u0_le hα64 hαne hnorm hD

theorem tauC_norm_le_gate_five {Ξ rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hα64 : ‖α‖ ≤ 1 / 64) (hσ : σ ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.tauC σ α w‖ ≤ 5 := by
  intro w hw
  rcases eq_or_ne α 0 with hα0 | hαne
  · -- `α = 0`: `τ_f ≡ 0` (the denominator of `tauC` vanishes identically)
    subst hα0
    simp [Work.Pert.tauC]
  by_cases hrr : 0 < rr
  swap
  · -- `rr ≤ 0`: the ball is empty, hence so is the gate by `hτQ`
    have hrrle : rr ≤ 0 := le_of_not_gt hrr
    have hmem : ‖Work.Pert.tauC σ α w‖ < rr := by
      have h := hτQ w hw
      rwa [Metric.mem_ball, dist_zero_right] at h
    exact absurd (lt_of_lt_of_le hmem hrrle) (not_lt.mpr (norm_nonneg _))
  · -- main case
    have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    set A : ℝ := ‖α‖ with hAdef
    have hApos : 0 < A := by rw [hAdef]; exact hαpos
    set τ : ℂ := Work.Pert.tauC σ α w with hτdef
    set s : ℂ := Work.Pert.sfun u σ α w with hsdef
    have hτmem : τ ∈ Metric.ball (0 : ℂ) rr := by rw [hτdef]; exact hτQ w hw
    have huτ : 1 / 2 ≤ ‖u τ‖ ∧ ‖u τ‖ ≤ 2 := hu2 τ hτmem
    have hu0 : 1 / 2 ≤ ‖u 0‖ := (hu2 0 (Metric.mem_ball_self hrr)).1
    have hsu0 : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
      linear_combination -hnorm
    -- ## the two bounds on `‖σ u 0‖ = ‖1 - exp (2πi α)‖`
    have hσu0le : ‖σ * u 0‖ ≤ (36 / 5) * A := by
      rw [hAdef, hsu0]
      exact one_sub_exp_two_pi_I_le_local hα64
    have hσu0ge : (28 / 5) * A ≤ ‖σ * u 0‖ := by
      rw [hAdef, hsu0]
      exact one_sub_exp_two_pi_I_ge_local hα64
    -- ## the normalisation bound on `σ`
    have hσ_le : ‖σ‖ ≤ (72 / 5) * A := by
      have h1 : ‖σ‖ * (1 / 2) ≤ ‖σ * u 0‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
      linarith
    -- ## `s` is close to `σ u 0`, hence bounded below
    have hsd : ‖s - σ * u 0‖ ≤ A / 4 := by
      rw [hAdef, hsdef]
      exact sfun_sub_sigma_u0_le_local hα64 hαne hnorm (hNT w hw)
    have hs_lb : (107 / 20) * A ≤ ‖s‖ := by
      have h1 : ‖σ * u 0‖ ≤ ‖s‖ + ‖s - σ * u 0‖ := by
        have h2 : ‖s - (s - σ * u 0)‖ ≤ ‖s‖ + ‖s - σ * u 0‖ := norm_sub_le s (s - σ * u 0)
        convert h2 using 2
        ring
      linarith
    have hs_pos : 0 < ‖s‖ :=
      lt_of_lt_of_le (by linarith [hApos] : (0 : ℝ) < 107 / 20 * A) hs_lb
    have hs_ne : s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hs_pos
      exact lt_irrefl 0 hs_pos
    have huτ_pos : 0 < ‖u τ‖ := lt_of_lt_of_le (by norm_num) huτ.1
    -- ## the algebraic relation `s (1 + τ u τ) = σ u τ`
    have hsτ : s = σ * u τ / (1 + τ * u τ) := by
      rw [hsdef, hτdef]
      rfl
    have hden0 : 1 + τ * u τ ≠ 0 := by
      intro h0
      have hsz : s = 0 := by rw [hsτ, h0, div_zero]
      exact hs_ne hsz
    have hrel : s * τ * u τ = σ * u τ - s := by
      have hden0' : 1 + (Work.Pert.tauC σ α w) * u (Work.Pert.tauC σ α w) ≠ 0 := by
        rw [← hτdef]; exact hden0
      have h2 : s * (1 + τ * u τ) = σ * u τ := by
        rw [hsdef, hτdef]
        exact div_mul_cancel₀ _ hden0'
      linear_combination h2
    -- ## `‖τ‖` from the relation
    have hτ_eq : ‖τ‖ = ‖σ * u τ - s‖ / (‖s‖ * ‖u τ‖) := by
      have h1 : ‖s‖ * ‖τ‖ * ‖u τ‖ = ‖σ * u τ - s‖ := by
        have h2 : ‖s * τ * u τ‖ = ‖σ * u τ - s‖ := by rw [hrel]
        rwa [norm_mul, norm_mul] at h2
      rw [← h1, eq_div_iff (mul_ne_zero (ne_of_gt hs_pos) (ne_of_gt huτ_pos))]
      ring
    -- ## the two ratio estimates
    have hσ_s : ‖σ‖ / ‖s‖ ≤ 3 := by
      rw [div_le_iff₀ hs_pos]
      calc ‖σ‖ ≤ (72 / 5) * A := hσ_le
        _ ≤ 3 * ((107 / 20) * A) := by linarith
        _ ≤ 3 * ‖s‖ := by linarith
    have hu_inv : 1 / ‖u τ‖ ≤ 2 := by
      rw [div_le_iff₀ huτ_pos]
      linarith [huτ.1]
    calc ‖τ‖ = ‖σ * u τ - s‖ / (‖s‖ * ‖u τ‖) := hτ_eq
      _ ≤ (‖σ‖ * ‖u τ‖ + ‖s‖) / (‖s‖ * ‖u τ‖) := by
            refine div_le_div_of_nonneg_right ?_ (mul_nonneg (norm_nonneg s) (norm_nonneg (u τ)))
            calc ‖σ * u τ - s‖ ≤ ‖σ * u τ‖ + ‖s‖ := norm_sub_le _ _
              _ = ‖σ‖ * ‖u τ‖ + ‖s‖ := by rw [norm_mul]
      _ = ‖σ‖ / ‖s‖ + 1 / ‖u τ‖ := by
            field_simp
      _ ≤ 3 + 2 := add_le_add hσ_s hu_inv
      _ = 5 := by norm_num

end

end Work.Pert
