import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.scale_cauchy
import Submission.Work.Pert.LiftExp.liftF_sub_translation_le_explicit
import Submission.Work.Pert.LiftExp.lipschitz_u_on_ball
import Submission.Work.Pert.LiftExp.norm_sigma_add_one_le_two
import Submission.Work.Pert.LiftExp.arith_max_le

/-!
# PERT · `Work.Pert.liftF_defect_le_tau_explicit`

The **explicit-constant** form of `Work.Pert.liftF_defect_le_tauC`: on the gate `Qm Ξ α` the defect
of the lift `F_f = liftF u σ α` of the perturbed Fatou coordinate is bounded by `τ_f = tauC σ α`
with the constant `2 ^ 12 * (1 + 1 / rr)` — a function of the radius `rr` of the disc on which `u`
is holomorphic and bounded by `[1/2, 2]` alone:

    ‖liftF u σ α z - (z + 1)‖ ≤ (2 ^ 12 * (1 + 1 / rr)) * ‖tauC σ α z‖ .

Nothing here depends on the particular `u` beyond `rr`: the whole point is that the constant is
*uniform* over the perturbation, which is what the assembly of `PertData` (and the `1/32`-form
`FatouStatement`) needs.

## Proof

Exactly the two-branch argument of `Work.Pert.liftF_defect_le_tauC`, but with every constant
tracked:

* **Lipschitz data.**  `Work.Pert.LiftExp.lipschitz_u_on_ball` (Cauchy estimate
  `Work.Pert.scale_cauchy` + the mean value inequality) gives `u` Lipschitz on `ball 0 (rr/2)`
  with constant `C := 8/rr`.
* **Small `τ_f`.**  `Work.Pert.LiftExp.liftF_sub_translation_le_explicit` is the algebraic identity
  `1 - s = A(1 + E)` of (A.1.7) with the threshold and constant of the proof made explicit: for
  `‖τ_f z‖ ≤ ε := min (rr/4) (min (1/8) (1/(16(‖σ‖+1)(C+4))))` it gives
  `‖F_f z - (z+1)‖ ≤ 16(C+4) ‖τ_f z‖`.
* **Large `τ_f`.**  There the near-translation hypothesis `hNT` (`≤ 1/32`) and
  `1/32 = (1/(32ε)) · ε < (1/(32ε)) ‖τ_f z‖` apply.
* **The arithmetic.**  `‖σ‖ + 1 ≤ 2` follows from the normalisation (`Work.Pert.LiftExp.
  norm_sigma_add_one_le_two`), so both `16(C+4) = 128/rr + 64` and `1/(32ε)` are dominated by
  `2 ^ 12 (1 + 1/rr)` (`Work.Pert.LiftExp.arith_max_le`).

The remaining hypotheses of the statement (`hΞ`, `hσ`, `hτQ`) as well as `hInF1` (which only
serves to make `α ≠ 0`) are not needed by the estimate itself; they belong to the surrounding
geometry in which the lemma is applied.
-/

namespace Work.Pert

open Work.Pert.LiftExp

theorem liftF_defect_le_tau_explicit {Ξ rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hInF1 : MandelDim.InF1 α)
    (hα64 : ‖α‖ ≤ 1 / 64) (hσ : σ ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∀ z ∈ Work.Pert.Qm Ξ α,
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ (2 ^ 12 * (1 + 1 / rr)) * ‖Work.Pert.tauC σ α z‖ := by
  -- `α ≠ 0`, from the geometry `|α.im| < α.re`
  have hαne : α ≠ 0 := by
    intro h0
    subst h0
    simp only [MandelDim.InF1, Complex.zero_re, Complex.zero_im, abs_zero] at hInF1
    exact absurd hInF1 (lt_irrefl 0)
  -- the boundedness data is inherited by the half ball
  have hu2' : ∀ z ∈ Metric.ball (0 : ℂ) (rr / 2), 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2 :=
    fun z hz => hu2 z (Metric.ball_subset_ball (by linarith) hz)
  have huL := lipschitz_u_on_ball hrr hu (fun z hz => (hu2 z hz).2)
  have hC8 : (0 : ℝ) ≤ 8 / rr := by positivity
  -- the explicit local estimate, with `r = rr/2` and `C = 8/rr`
  have htr := liftF_sub_translation_le_explicit (u := u) (σ := σ) (α := α)
    (r := rr / 2) (C := 8 / rr) (by linarith) hC8 hu2' huL hnorm hαne hα64
  -- `‖σ‖ + 1 ≤ 2` from the normalisation, and the two arithmetic facts
  have hσ2 : ‖σ‖ + 1 ≤ 2 :=
    norm_sigma_add_one_le_two hα64 hnorm (hu2 0 (Metric.mem_ball_self hrr)).1
  have harith := arith_max_le (rr := rr) (S := ‖σ‖ + 1) hrr (by positivity) hσ2
  have hK : 16 * (8 / rr + 4) ≤ 2 ^ 12 * (1 + 1 / rr) := (max_le_iff.mp harith).1
  have hε : 1 / (32 * min (rr / 4) (min (1 / 8) (1 / (16 * (‖σ‖ + 1) * (8 / rr + 4)))))
      ≤ 2 ^ 12 * (1 + 1 / rr) := (max_le_iff.mp harith).2
  set m : ℝ := min (rr / 4) (min (1 / 8) (1 / (16 * (‖σ‖ + 1) * (8 / rr + 4)))) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  have hε' : 1 / (32 * m) ≤ 2 ^ 12 * (1 + 1 / rr) := by
    rw [hm]; exact hε
  intro z hz
  -- ## the threshold split at `m = min (rr/4) (min (1/8) …)`
  by_cases hsmall : ‖Work.Pert.tauC σ α z‖ ≤ m
  · -- `‖τ_f z‖` below the threshold: the analytic (Taylor) estimate applies
    calc ‖Work.Pert.liftF u σ α z - (z + 1)‖
        ≤ 16 * (8 / rr + 4) * ‖Work.Pert.tauC σ α z‖ :=
          htr z (by rw [show (rr / 2 / 2 : ℝ) = rr / 4 by ring, ← hm]; exact hsmall)
      _ ≤ (2 ^ 12 * (1 + 1 / rr)) * ‖Work.Pert.tauC σ α z‖ :=
            mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  · -- `‖τ_f z‖` above the threshold: use `hNT` and `1/32 = (1/(32 m)) · m`
    have hm_lt : m < ‖Work.Pert.tauC σ α z‖ := lt_of_not_ge hsmall
    have h32m : (32 : ℝ) * m ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hmpos)
    have hkey : (1 : ℝ) / 32 = (1 / (32 * m)) * m := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by norm_num : (32 : ℝ) ≠ 0) h32m]
      ring
    calc ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := hNT z hz
      _ = (1 / (32 * m)) * m := hkey
      _ ≤ (1 / (32 * m)) * ‖Work.Pert.tauC σ α z‖ :=
            mul_le_mul_of_nonneg_left (le_of_lt hm_lt)
              (le_of_lt (div_pos one_pos (mul_pos (by norm_num) hmpos)))
      _ ≤ (2 ^ 12 * (1 + 1 / rr)) * ‖Work.Pert.tauC σ α z‖ :=
            mul_le_mul_of_nonneg_right hε' (norm_nonneg _)

end Work.Pert
