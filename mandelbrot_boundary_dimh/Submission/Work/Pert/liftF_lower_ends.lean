import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.norm_sigma_mul_u_sigma_le
import Submission.Work.Pert.Qm_exists_im_lt
import Submission.Work.Pert.norm_log_sub_log_le

/-!
# PERT · `Work.Pert.liftF_lower_ends`

Shishikura §4.2, the **lower end** of the lower gate `Qm Ξ α`.  The perturbed coordinate
`F_f = liftF u σ α` of the germ `f z = z + z (z - σ) u z` is the lift of `f` on the cylinder and
satisfies

  `F_f z = z + (1/(2πiα)) log (1 - s_f z)`,   `s_f z = σ u(τ_f z)/(1 + τ_f z u(τ_f z))`,

where `τ_f z = σ/(1 - exp (-2πiα z))` is the universal cover of `ℂ ∖ {0, σ}`.  As `z.im → -∞`
inside the gate one has `τ_f z → σ`, hence `s_f z → σ u σ / (1 + σ u σ)` and therefore

  `F_f z → z + ρ`,   `ρ = log (1/(1 + σ u σ)) / (2πiα)`,

so the lift is *eventually the translation by* `ρ`, not by `1`.  This file proves that

* the convergence is exponential with the same rate as the convergence of `s_f` (`hsfun`), and
* `‖ρ - 1‖ ≤ 1/32` — the size hypothesis the lower branch of `MandelDim.FatouEnds` /
  `PertData.R_close_dn` needs.

The second point is *not* a consequence of the data `(σ, u, α)` alone: the algebraic identity
`σ u 0 = 1 - exp (2πiα)` only pins `σ u σ` down to `O(‖α‖)`, and `ρ - 1 = 2πiα + O(‖α‖²)` has
modulus `≈ 2π/64 > 1/32` at the extreme `‖α‖ = 1/64` (see `Work.Pert.liftF_lower_counterexample`).
It is the hypothesis `hval` — the *value* normalisation `‖F_f z - (z + 1)‖ ≤ 1/32` of the gate —
that fixes it: since `Qm Ξ α` contains points with arbitrarily negative imaginary part, the limit
`ρ` of `F_f z - z` at the lower end is a limit of points of the ball `B(1, 1/32)`, hence itself
in that ball.

The three numerical / analytic inputs are delegated:

* `Work.Pert.norm_sigma_mul_u_sigma_le` — `‖σ u σ‖ ≤ π/4` (so that `1 + σ u σ` is bounded away
  from `0` and `L = (1 + σ u σ)⁻¹` has positive real part);
* `Work.Pert.norm_log_sub_log_le` — `Complex.log` is Lipschitz, with constant `4/‖L‖`, on every
  ball around a point `L` of the right half plane of radius `≤ ‖L‖/2` (the ball misses the branch
  cut, and `‖z‖ ≥ ‖L‖/2` throughout);
* `Work.Pert.Qm_exists_im_lt` — `Qm Ξ α` meets every half plane `Im z < -T`.
-/

namespace Work.Pert

set_option linter.unusedVariables false

theorem liftF_lower_ends {Ξ rr M κ Y : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hrr : 0 < rr) (hσr : ‖σ‖ < rr)
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hM : 0 < M) (hκ : 0 < κ)
    (hsfun : ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
      ‖(1 - Work.Pert.sfun u σ α z) - 1 / (1 + σ * u σ)‖ ≤ M * Real.exp (κ * z.im))
    (hval : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∃ ρ : ℂ, ‖ρ - 1‖ ≤ 1 / 32 ∧ ∃ M' κ' Y' : ℝ, 0 < M' ∧ 0 < κ' ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y' →
        ‖Work.Pert.liftF u σ α z - (z + ρ)‖ ≤ M' * Real.exp (κ' * z.im) := by
  -- `α ≠ 0`, from `|α.im| < α.re`
  have hαne : α ≠ 0 := by
    intro h0
    have h : MandelDim.InF1 (0 : ℂ) := by rw [← h0]; exact hInF1
    rw [MandelDim.InF1] at h
    simp at h
  -- the two `2πiα`'s of the argument
  set A : ℂ := 2 * Real.pi * Complex.I * α with hA
  have hAne : A ≠ 0 := by
    rw [hA]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hαne
  -- the limit value `L = 1/(1 + σuσ) = 1/f'(σ)` and the displacement `ρ = log L / A`
  set L : ℂ := (1 + σ * u σ)⁻¹ with hL
  have hσuσ_le : ‖σ * u σ‖ ≤ Real.pi / 4 :=
    norm_sigma_mul_u_sigma_le hrr hσr hα64 hnorm hu2
  have hpi4lt : Real.pi / 4 < 1 := by nlinarith [Real.pi_lt_four]
  have hre1 : 0 < (1 + σ * u σ).re := by
    have hb : -‖σ * u σ‖ ≤ (σ * u σ).re := (abs_le.mp (Complex.abs_re_le_norm (σ * u σ))).1
    have h2 : (1 + σ * u σ).re = 1 + (σ * u σ).re := by simp
    rw [h2]; linarith
  have hnorm1 : 0 < ‖1 + σ * u σ‖ := by
    have hb : (1 + σ * u σ).re ≤ ‖1 + σ * u σ‖ :=
      (abs_le.mp (Complex.abs_re_le_norm (1 + σ * u σ))).2
    linarith
  have hsq : 0 < Complex.normSq (1 + σ * u σ) := by
    rw [← Complex.sq_norm]; positivity
  have hLre : 0 < L.re := by
    rw [hL, Complex.inv_re]
    exact div_pos hre1 hsq
  have hLne : L ≠ 0 := by
    intro h
    rw [h] at hLre
    simp at hLre
  have hLnormpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  set ρ : ℂ := Complex.log L / A with hρ
  set M' : ℝ := ‖A⁻¹‖ * (4 / ‖L‖) * M with hM'
  set Y' : ℝ := max Y (Real.log (2 * M / ‖L‖) / κ) with hY'
  have hM'pos : 0 < M' := by
    rw [hM']
    have h1 : 0 < ‖A⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hAne)
    exact mul_pos (mul_pos h1 (by positivity : (0:ℝ) < 4 / ‖L‖)) hM
  -- **the exponential decay**: `log` is Lipschitz near `L = 1/(1+σuσ) ≠ 0`
  have hdecay : ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y' →
      ‖Work.Pert.liftF u σ α z - (z + ρ)‖ ≤ M' * Real.exp (κ * z.im) := by
    intro z hz hzY'
    have hzY : z.im < -Y := by
      have h1 : Y ≤ Y' := by rw [hY']; exact le_max_left _ _
      linarith
    have hone : 1 / (1 + σ * u σ) = L := by rw [one_div, ← hL]
    have hw := hsfun z hz hzY
    rw [hone] at hw
    -- `M exp (κ z.im) < ‖L‖/2`, so `1 - s_f z` stays in the ball `B(L, ‖L‖/2)`
    have hYlog : Real.log (2 * M / ‖L‖) / κ ≤ Y' := by rw [hY']; exact le_max_right _ _
    have hzlt : z.im < -(Real.log (2 * M / ‖L‖) / κ) := by
      have h2 := neg_le_neg hYlog
      linarith
    have hmlt : κ * z.im < -(Real.log (2 * M / ‖L‖)) := by
      have h3 := mul_lt_mul_of_pos_left hzlt hκ
      rwa [mul_neg, mul_div_cancel₀ _ (ne_of_gt hκ)] at h3
    have hexplt : Real.exp (κ * z.im) < ‖L‖ / (2 * M) := by
      have h1 : Real.exp (κ * z.im) < Real.exp (-(Real.log (2 * M / ‖L‖))) :=
        Real.exp_lt_exp.mpr hmlt
      have h2 : Real.exp (-(Real.log (2 * M / ‖L‖))) = ‖L‖ / (2 * M) := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      linarith
    have hw' : ‖(1 - Work.Pert.sfun u σ α z) - L‖ ≤ ‖L‖ / 2 := by
      have h1 := mul_lt_mul_of_pos_left hexplt hM
      have h3 : M * (‖L‖ / (2 * M)) = ‖L‖ / 2 := by field_simp
      linarith [hw, h1, h3]
    have hlog := norm_log_sub_log_le (L := L) (w := 1 - Work.Pert.sfun u σ α z)
        (r := ‖L‖ / 2) hLre (by linarith) le_rfl hw'
    have hsplit : Work.Pert.liftF u σ α z - (z + ρ)
        = A⁻¹ * (Complex.log (1 - Work.Pert.sfun u σ α z) - Complex.log L) := by
      rw [Work.Pert.liftF, hρ, hA, one_div, div_eq_mul_inv]
      ring
    rw [hsplit, norm_mul]
    calc ‖A⁻¹‖ * ‖Complex.log (1 - Work.Pert.sfun u σ α z) - Complex.log L‖
        ≤ ‖A⁻¹‖ * (4 / ‖L‖ * ‖(1 - Work.Pert.sfun u σ α z) - L‖) :=
          mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
      _ ≤ ‖A⁻¹‖ * (4 / ‖L‖ * (M * Real.exp (κ * z.im))) := by
          have h4 : 0 ≤ 4 / ‖L‖ := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw h4) (norm_nonneg _)
      _ = M' * Real.exp (κ * z.im) := by rw [hM']; ring
  -- **the normalisation** `‖ρ - 1‖ ≤ 1/32`, from `hval` and points of the gate with `Im → -∞`
  have hρ1 : ‖ρ - 1‖ ≤ 1 / 32 := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    set T : ℝ := max Y' (Real.log (M' / ε) / κ) with hT
    obtain ⟨z, hzQ, hzT⟩ := Qm_exists_im_lt (Ξ := Ξ) (α := α) T
    have hzY' : z.im < -Y' := by
      have h1 : Y' ≤ T := by rw [hT]; exact le_max_left _ _
      linarith
    have hd := hdecay z hzQ hzY'
    have hv := hval z hzQ
    have hlogT : Real.log (M' / ε) / κ ≤ T := by rw [hT]; exact le_max_right _ _
    have hzlt : z.im < -(Real.log (M' / ε) / κ) := by linarith
    have hmlt : κ * z.im < -(Real.log (M' / ε)) := by
      have h3 := mul_lt_mul_of_pos_left hzlt hκ
      rwa [mul_neg, mul_div_cancel₀ _ (ne_of_gt hκ)] at h3
    have hexplt : Real.exp (κ * z.im) < ε / M' := by
      have h1 : Real.exp (κ * z.im) < Real.exp (-(Real.log (M' / ε))) :=
        Real.exp_lt_exp.mpr hmlt
      have h2 : Real.exp (-(Real.log (M' / ε))) = ε / M' := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      linarith
    have hexp_le : M' * Real.exp (κ * z.im) ≤ ε := by
      have h1 := mul_lt_mul_of_pos_left hexplt hM'pos
      have h3 : M' * (ε / M') = ε := by field_simp
      linarith
    calc ‖ρ - 1‖ = ‖((z + ρ) - Work.Pert.liftF u σ α z)
            + (Work.Pert.liftF u σ α z - (z + 1))‖ := by congr 1; ring
      _ ≤ ‖(z + ρ) - Work.Pert.liftF u σ α z‖
            + ‖Work.Pert.liftF u σ α z - (z + 1)‖ := norm_add_le _ _
      _ = ‖Work.Pert.liftF u σ α z - (z + ρ)‖
            + ‖Work.Pert.liftF u σ α z - (z + 1)‖ := by rw [norm_sub_rev]
      _ ≤ M' * Real.exp (κ * z.im) + 1 / 32 := add_le_add hd hv
      _ ≤ ε + 1 / 32 := by linarith
      _ = 1 / 32 + ε := by ring
  exact ⟨ρ, hρ1, M', κ, Y', hM'pos, hκ, hdecay⟩

end Work.Pert
