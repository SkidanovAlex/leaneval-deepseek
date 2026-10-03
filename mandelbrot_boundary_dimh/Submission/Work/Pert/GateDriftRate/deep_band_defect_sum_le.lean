import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.Setup
import Submission.Work.Pert.defect_sub_endDefect_le
import Submission.Work.Pert.sigma_le_half_rr
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.GateDriftRate.high_decay_sum_uniform

/-!
# PERT · `Work.Pert.GateDriftRate.deep_band_defect_sum_le`

The deep-band (`Im (α w_j) ≤ -1`) part of the drift estimate: along a legal walk of the lifted
perturbed Fatou coordinate the *reduced* per-step defects `d(w_j) - D` (`D = endDefect u σ α`) are
summable, with the `log`-factor constant of the drift estimate.

## Structure

* `conj_mem_Qm`: the gate `Qm Ξ α` is transported by conjugation with `α ↦ conj α`;
* `deep_decay_sum_uniform`: the deep-band decay sum.  This is *exactly* the high-band sum
  `Work.Pert.GateDriftRate.high_decay_sum_uniform` applied to the conjugated configuration
  `(conj α, conj ∘ w)`, because `Im (conj α · conj w) = - Im (α w)` while conjugation preserves
  both the walk and the gate;
* the assembly: pointwise `‖d - D‖ ≤ 2^11 (1 + 1/rr) ‖τ_f w - σ‖`
  (`Work.Pert.defect_sub_endDefect_le`), `‖τ_f w - σ‖ ≤ 2 ‖σ‖ exp (2π Im (α w))` on the band
  (from `τ_f w - σ = σ E/(1 - E)` with `‖E‖ = exp (2π Im (α w)) ≤ 1/2`), and
  `‖σ‖ ≤ 32 ‖α‖` (`Work.Pert.sigma_le_norm_alpha`); the final arithmetic only uses
  `2^23 (1 + 1/rr) ≤ 2^29 (1 + Ξ + 1/Ξ + 1/rr) (1 + log (2+M) + log (2+‖z‖))`.
-/

namespace Work.Pert.GateDriftRate

open Complex MandelDim
open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Conjugation transport of the gate -/

/-- The gate `Qm Ξ α` is transported by complex conjugation (with `α` conjugated):
`conj w ∈ Qm Ξ (conj α) ↔ w ∈ Qm Ξ α`. -/
theorem conj_mem_Qm {Ξ : ℝ} {α w : ℂ} :
    conj w ∈ Work.Pert.Qm Ξ (conj α) ↔ w ∈ Work.Pert.Qm Ξ α := by
  have hc : (1 / conj α : ℂ) = conj (1 / α) := by rw [one_div, one_div, map_inv₀]
  rw [Work.Pert.Qm_mem_iff, Work.Pert.Qm_mem_iff, hc]
  simp only [Complex.conj_re, Complex.conj_im, ← neg_add, abs_neg]

/-! ### The deep-band decay sum -/

/-- **Uniform deep-band decay sum.**  For a `1/32`-near-translation walk in the lower gate
`Qm Ξ α` with `‖α‖ ≤ 1/64`, the weighted sum of `exp (2π Im (α w_j))` over the deep indices
`Im (α w_j) ≤ -1` is bounded by the absolute constant `2 ^ 6`, uniformly in the gate width `Ξ` and
in the length `n` of the walk.

This is the high-regime statement `Work.Pert.GateDriftRate.high_decay_sum_uniform` read through
complex conjugation: `conj` maps the walk in `Qm Ξ α` to a walk in `Qm Ξ (conj α)`
(`conj_mem_Qm`) and turns the deep band `Im (α w) ≤ -1` into the high band
`1 ≤ Im (conj α · conj w)`. -/
theorem deep_decay_sum_uniform {Ξ : ℝ} {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    ‖α‖ * (∑ j ∈ Finset.range n,
        (if (α * w j).im ≤ -1 then Real.exp (2 * Real.pi * (α * w j).im) else 0))
      ≤ 2 ^ 6 := by
  have hInF1' : MandelDim.InF1 (conj α) := by
    have h := hInF1
    simp only [MandelDim.InF1] at h ⊢
    simpa using h
  have hα64' : ‖conj α‖ ≤ 1 / 64 := by rwa [Complex.norm_conj]
  have hstep' : ∀ j < n, ‖conj (w (j + 1)) - (conj (w j) + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have h := hstep j hj
    have he : conj (w (j + 1)) - (conj (w j) + 1) = conj (w (j + 1) - (w j + 1)) := by
      rw [map_sub, map_add, map_one]
    rw [he, Complex.norm_conj]
    exact h
  have hgate' : ∀ j ≤ n, conj (w j) ∈ Work.Pert.Qm Ξ (conj α) :=
    fun j hj => conj_mem_Qm.mpr (hgate j hj)
  have hmain := Work.Pert.GateDriftRate.high_decay_sum_uniform (Ξ := Ξ) (α := conj α)
    (w := fun j => conj (w j)) (n := n) hΞ hInF1' hα64' hstep' hgate'
  have hnorm : ‖conj α‖ = ‖α‖ := Complex.norm_conj α
  have hterm : ∀ j : ℕ, (conj α * conj (w j)).im = -((α * w j).im) := by
    intro j
    rw [← map_mul, Complex.conj_im]
  have hiff : ∀ j : ℕ, (1 ≤ (conj α * conj (w j)).im) ↔ ((α * w j).im ≤ -1) := by
    intro j
    rw [hterm j]
    constructor <;> intro h <;> linarith
  have hexp : ∀ j : ℕ, Real.exp (-(2 * Real.pi * (conj α * conj (w j)).im))
      = Real.exp (2 * Real.pi * (α * w j).im) := by
    intro j
    rw [hterm j]
    congr 1
    ring
  have hsum : (∑ j ∈ Finset.range n,
        (if (α * w j).im ≤ -1 then Real.exp (2 * Real.pi * (α * w j).im) else 0))
      = ∑ j ∈ Finset.range n,
        (if 1 ≤ (conj α * conj (w j)).im
          then Real.exp (-(2 * Real.pi * (conj α * conj (w j)).im)) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (α * w j).im ≤ -1
    · rw [if_pos h, if_pos ((hiff j).mpr h), hexp j]
    · rw [if_neg h, if_neg (fun hc => h ((hiff j).mp hc))]
  rw [hsum, ← hnorm]
  exact hmain

/-! ### Pointwise facts about the perturbed coordinate -/

/-- `-(‖z‖) ≤ z.re`. -/
private lemma neg_norm_le_re (z : ℂ) : -(‖z‖) ≤ z.re := by
  have h := Complex.abs_re_le_norm z
  rw [abs_le] at h
  linarith [h.1]

/-- `τ_f w - σ = σ E / (1 - E)` with `E = exp (-2πi α w)`. -/
private lemma tauC_sub_sigma_eq {σ α w : ℂ}
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1) :
    Work.Pert.tauC σ α w - σ
      = σ * Complex.exp (-(2 * Real.pi * Complex.I * α * w))
        / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))) := by
  have h1 : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hE)
  rw [Work.Pert.tauC]
  field_simp
  ring

/-- `‖exp (-2πi α w)‖ = exp (2π Im (α w))`. -/
private lemma norm_exp_neg {α w : ℂ} :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖
      = Real.exp (2 * Real.pi * (α * w).im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

/-! ### The main estimate -/

/-- The deep-band defect sum, in the form in which the walk is an abstract sequence `w`. -/
theorem deep_band_defect_sum_le_aux {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    ∑ j ∈ (Finset.range n).filter (fun j => (α * w j).im ≤ -1),
        ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 23 * (1 + 1 / rr) := by
  classical
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h := hM
    norm_num at h ⊢
    exact h
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    refine le_trans hα (one_div_le_one_div_of_le (by norm_num) ?_)
    nlinarith [hM1024, hΞ]
  have hσle : ‖σ‖ ≤ 32 * ‖α‖ :=
    Work.Pert.sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  have hσhalf : ‖σ‖ ≤ rr / 2 := Work.Pert.sigma_le_half_rr hΞ hrr hM hInF1 hα hτQ
  have hσ1026 : ‖σ‖ ≤ 1 / 1026 := by
    have h1 : 32 * ‖α‖ ≤ 1 / (M + 2 + Ξ) := by
      calc 32 * ‖α‖ ≤ 32 * (1 / (32 * (M + 2 + Ξ))) := by linarith [hα]
        _ = 1 / (M + 2 + Ξ) := by field_simp
    have h2 : 1 / (M + 2 + Ξ) ≤ 1 / 1026 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [hσle, h1, h2]
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hσhalf, hrr]
  have hA1 : 0 < (1 + σ * u σ).re := by
    have h1 : ‖σ * u σ‖ ≤ 2 * ‖σ‖ := by
      rw [norm_mul]
      nlinarith [(hu2 σ hσmem).2, norm_nonneg σ]
    have h2 : -‖σ * u σ‖ ≤ (σ * u σ).re := neg_norm_le_re _
    simp only [Complex.add_re, Complex.one_re]
    linarith [h2, h1, hσ1026]
  have hrr0 : (0 : ℝ) < 1 / rr := one_div_pos.mpr hrr
  have hK0 : (0 : ℝ) ≤ 2 ^ 11 * (1 + 1 / rr) := by nlinarith
  have hK1 : (0 : ℝ) ≤ 2 ^ 11 * (1 + 1 / rr) * 64 := by nlinarith
  -- the deep index set
  set J : Finset ℕ := (Finset.range n).filter (fun j => (α * w j).im ≤ -1) with hJdef
  have hJmem : ∀ j, j ∈ J ↔ (j < n ∧ (α * w j).im ≤ -1) := by
    intro j
    rw [hJdef]
    simp [Finset.mem_filter, Finset.mem_range]
  have hdec : ‖α‖ * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im)) ≤ 2 ^ 6 := by
    have h := deep_decay_sum_uniform (Ξ := Ξ) (α := α) (w := w) (n := n) hΞ hInF1 hα64 hstep
      hgate
    have h' : (∑ j ∈ Finset.range n,
        (if (α * w j).im ≤ -1 then Real.exp (2 * Real.pi * (α * w j).im) else 0))
        = ∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im) := by
      rw [hJdef, Finset.sum_filter]
    rwa [h'] at h
  -- the pointwise value bound
  have hτb : ∀ j ∈ J, ‖Work.Pert.tauC σ α (w j) - σ‖
      ≤ 2 * ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im) := by
    intro j hj
    obtain ⟨hjn, htj⟩ := (hJmem j).mp hj
    set E : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * α * w j)) with hEdef
    have hEeq : ‖E‖ = Real.exp (2 * Real.pi * (α * w j).im) := by
      rw [hEdef]
      exact norm_exp_neg
    have hlog : Real.log 2 ≤ 2 * Real.pi := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have hnormE : ‖E‖ ≤ 1 / 2 := by
      rw [hEeq]
      have h3 : 2 * Real.pi * (α * w j).im ≤ -(Real.log 2) := by
        nlinarith [htj, Real.pi_pos, hlog]
      calc Real.exp (2 * Real.pi * (α * w j).im) ≤ Real.exp (-(Real.log 2)) :=
            Real.exp_le_exp.mpr h3
        _ = 1 / 2 := by
            rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    have hEne : E ≠ 1 := by
      intro h1
      have h2 : ‖E‖ = 1 := by rw [h1, norm_one]
      linarith [hnormE]
    have h1mE : 1 / 2 ≤ ‖1 - E‖ := by
      have h := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at h
      linarith [h, hnormE]
    have hsplit : Work.Pert.tauC σ α (w j) - σ = σ * E / (1 - E) := by
      rw [hEdef]
      exact tauC_sub_sigma_eq hEne
    rw [hsplit, norm_div, norm_mul, hEeq]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 - E‖)]
    have h10 : 1 ≤ 2 * ‖1 - E‖ := by linarith
    have hA0 : (0 : ℝ) ≤ ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im) :=
      mul_nonneg (norm_nonneg σ) (Real.exp_pos _).le
    calc ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im)
        = ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im) * 1 := by ring
      _ ≤ ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im) * (2 * ‖1 - E‖) :=
          mul_le_mul_of_nonneg_left h10 hA0
      _ = (2 * ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im)) * ‖1 - E‖ := by ring
  -- the pointwise defect bound
  have hpt : ∀ j ∈ J,
      ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
        ≤ 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im)) := by
    intro j hj
    obtain ⟨hjn, htj⟩ := (hJmem j).mp hj
    have hjm : w j ∈ Work.Pert.Qm Ξ α := hgate j (le_of_lt hjn)
    have hd := Work.Pert.defect_sub_endDefect_le (rr := rr) (α := α) (σ := σ) (u := u)
      (w := w j) hrr hα64 hαne hu hu2 hσhalf (hτQ (w j) hjm) (hNT (w j) hjm)
      (by
        refine le_trans (hτb j hj) ?_
        have h1 : Real.exp (2 * Real.pi * (α * w j).im) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [htj, Real.pi_pos]
        have h2 : 0 ≤ ‖σ‖ := norm_nonneg σ
        nlinarith [h1, h2, hσ1026])
      hA1
    refine le_trans hd ?_
    exact mul_le_mul_of_nonneg_left (hτb j hj) hK0
  -- assembly
  have hsum1 : ∑ j ∈ J, ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖)
          * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im)) := by
    calc ∑ j ∈ J, ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
        ≤ ∑ j ∈ J, 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖ * Real.exp (2 * Real.pi * (α * w j).im)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖)
            * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  have hfac : (2 : ℝ) * ‖σ‖ ≤ 64 * ‖α‖ := by linarith [hσle]
  have hSnn : 0 ≤ ∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  calc ∑ j ∈ J, ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖)
          * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im)) := hsum1
    _ ≤ 2 ^ 11 * (1 + 1 / rr) * (64 * ‖α‖)
          * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im)) := by
        have h1 : 2 ^ 11 * (1 + 1 / rr) * (2 * ‖σ‖) ≤ 2 ^ 11 * (1 + 1 / rr) * (64 * ‖α‖) :=
          mul_le_mul_of_nonneg_left hfac hK0
        exact mul_le_mul_of_nonneg_right h1 hSnn
    _ = 2 ^ 11 * (1 + 1 / rr) * 64
          * (‖α‖ * (∑ j ∈ J, Real.exp (2 * Real.pi * (α * w j).im))) := by ring
    _ ≤ 2 ^ 11 * (1 + 1 / rr) * 64 * 2 ^ 6 :=
        mul_le_mul_of_nonneg_left hdec hK1
    _ = 2 ^ 23 * (1 + 1 / rr) := by ring

theorem deep_band_defect_sum_le {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ∑ j ∈ (Finset.range n).filter
            (fun j => (α * (Work.Pert.liftF u σ α)^[j] z).im ≤ -1),
        ‖Work.Pert.liftF u σ α ((Work.Pert.liftF u σ α)^[j] z)
          - ((Work.Pert.liftF u σ α)^[j] z + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
  set w : ℕ → ℂ := fun j => (Work.Pert.liftF u σ α)^[j] z with hw
  have hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have h1 : w (j + 1) = Work.Pert.liftF u σ α (w j) := by
      simp only [hw, Function.iterate_succ_apply']
    rw [h1]
    exact hNT (w j) (hwalk j (le_of_lt hj))
  have hkey := deep_band_defect_sum_le_aux (Ξ := Ξ) (rr := rr) (M := M) (α := α) (σ := σ)
    (u := u) (w := w) (n := n) hΞ hrr hM hInF1 hα hσ hnorm hu hu2 hτQ hNT hstep hwalk
  have hL : (1 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
    have h1 : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (2 + ‖z‖) :=
      Real.log_nonneg (by have h := norm_nonneg z; linarith)
    linarith
  have hX : (0 : ℝ) ≤ Ξ + 1 / Ξ := by
    have h := one_div_pos.mpr hΞ
    linarith
  have hrr0 : (0 : ℝ) < 1 / rr := one_div_pos.mpr hrr
  calc ∑ j ∈ (Finset.range n).filter (fun j => (α * w j).im ≤ -1),
        ‖Work.Pert.liftF u σ α (w j) - (w j + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 23 * (1 + 1 / rr) := hkey
    _ ≤ 2 ^ 29 * (1 + 1 / rr) := by
        have h1 : (2 : ℝ) ^ 23 ≤ 2 ^ 29 := by norm_num
        have h2 : (0 : ℝ) ≤ 1 + 1 / rr := by linarith
        nlinarith [h1, h2]
    _ ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
        have h1 : (1 : ℝ) + 1 / rr ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by linarith
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
        have h1 : (0 : ℝ) ≤ 2 ^ 29 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
          have h2 := one_div_pos.mpr hΞ
          have h3 := one_div_pos.mpr hrr
          nlinarith
        nlinarith [h1, hL]

end

end Work.Pert.GateDriftRate
