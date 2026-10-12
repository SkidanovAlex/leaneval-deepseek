import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixR.LatGreen.heatK3_head_le
import Submission.Work.BoseFixR.LatGreen.heatK3_tail_ge
import Submission.Work.BoseFixR.LatGreen.integral_tsum_Ioc
import Submission.Work.BoseFixR.LatGreen.latticeGaussSum_le
import Submission.Work.BoseFixR.LatGreen.latticeGaussSummable
import Submission.Work.BoseFixR.LatGreen.tailIntegral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `madelung_smooth_nonpos` — the sharp Madelung sign on the Voronoi cell

Target: for `u ≠ 0` with `|u i| ≤ 1/2` (so that `u` lies in the Voronoi cell of the origin),

`latGreenSmooth u = latGreen u − 1/(4π‖u‖) ≤ 0`.

## Proof strategy (Ewald splitting with the freed heat-kernel term)

Split `latGreen u = ∫_0^∞ (heatPeriod t u − 1) dt` at `η = 1/10` and write

`∫_0^η (heatPeriod t u − 1) = ∫_0^η (heatPeriod t u − heatK3 t u) + ∫_0^η heatK3 t u − η`.

The third term is handled *sharply*: `∫_0^η heatK3 t u ≤ 1/(4π‖u‖) − T` where
`T = 1/(4π^{3/2}√η) − ‖u‖²/(48π^{3/2}η^{3/2})` is the elementary lower bound of the heat-kernel
tail (from `e^{-z} ≥ 1 - z`); the `1/(4π‖u‖)` cancels against the definition of `latGreenSmooth`.

The short-time piece is bounded termwise by the direct lattice sum over `n ≠ 0` with the
per-term Gaussian majorant `√η e^{-‖u-n‖²/(4η)}/(8π^{3/2}a_n)`, and the long-time piece by the
Fourier tail estimate.  With `A = √η/(2π^{3/2})`, `B = 1/(4π^{3/2}√η)`, `C = 1/(48π^{3/2}η^{3/2})`,
`M = max(‖u‖²,1/4)`, the ledger is the purely numerical inequality `ledger_bound`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen


/-! ## Geometry of the Voronoi cell `[-1/2,1/2]³` -/

/-- `‖u - latVec n‖²` in coordinates. -/
lemma norm_sub_latVec_sq_eq (u : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    ‖u - latVec n‖ ^ 2 = ∑ i, (u i - (n i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [WithLp.ofLp_sub, Pi.sub_apply, latVec_apply]

/-- **Voronoi**: for `u` in the half-cell and `n ≠ 0`, `u` is at least as close to `0` as to `n`. -/
lemma norm_sub_latVec_sq_ge {u : EuclideanSpace ℝ (Fin 3)} (hu : ∀ i, |u i| ≤ 1 / 2) (n : Fin 3 → ℤ) :
    ‖u‖ ^ 2 ≤ ‖u - latVec n‖ ^ 2 := by
  rw [norm_sub_latVec_sq_eq, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨hl, hr⟩ := abs_le.mp (hu i)
  have hkey : (u i - (n i : ℝ)) ^ 2 - (u i) ^ 2 = (n i : ℝ) * ((n i : ℝ) - 2 * u i) := by ring
  have hnn : 0 ≤ (n i : ℝ) * ((n i : ℝ) - 2 * u i) := by
    rcases lt_trichotomy (n i) 0 with h | h | h
    · have h1 : ((n i : ℤ) : ℝ) ≤ -1 := by
        have : n i ≤ -1 := by omega
        exact_mod_cast this
      have h2 : ((n i : ℤ) : ℝ) ≤ 0 := by linarith
      have h3 : ((n i : ℤ) : ℝ) - 2 * u i ≤ 0 := by linarith
      exact mul_nonneg_of_nonpos_of_nonpos h2 h3
    · rw [h]; simp
    · have h1 : (1 : ℝ) ≤ ((n i : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ n i := by omega
        exact_mod_cast this
      have h2 : 0 ≤ ((n i : ℤ) : ℝ) := by linarith
      have h3 : 0 ≤ ((n i : ℤ) : ℝ) - 2 * u i := by linarith
      exact mul_nonneg h2 h3
  linarith [hkey, hnn]

/-- For `u` in the half-cell and `n ≠ 0`, the distance `‖u − n‖` is at least `1/2`. -/
lemma quarter_le_norm_sub_latVec_sq {u : EuclideanSpace ℝ (Fin 3)} (hu : ∀ i, |u i| ≤ 1 / 2) {n : Fin 3 → ℤ}
    (hn : n ≠ 0) : (1 / 4 : ℝ) ≤ ‖u - latVec n‖ ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    apply hn
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  rw [norm_sub_latVec_sq_eq]
  have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have h1' : (1 : ℤ) ≤ |n i| := by
      rcases lt_or_gt_of_ne hi with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    rw [← Int.cast_abs]
    exact_mod_cast h1'
  have h2 : (1 / 2 : ℝ) ≤ |u i - (n i : ℝ)| := by
    have h3 : |((n i : ℤ) : ℝ)| - |u i| ≤ |u i - (n i : ℝ)| := by
      simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub ((n i : ℤ) : ℝ) (u i)
    have := hu i
    linarith
  have h4 : (1 / 4 : ℝ) ≤ (u i - (n i : ℝ)) ^ 2 := by
    have := sq_abs (u i - (n i : ℝ))
    nlinarith [h2, this]
  exact le_trans h4 (Finset.single_le_sum (f := fun j => (u j - (n j : ℝ)) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- The weighted Voronoi bound used to compare the lattice sum with its `n = 0` term. -/
lemma inv_norm_sub_latVec_sq_le {u : EuclideanSpace ℝ (Fin 3)} (hu : ∀ i, |u i| ≤ 1 / 2) {n : Fin 3 → ℤ}
    (hn : n ≠ 0) :
    1 / ‖u - latVec n‖ ^ 2 ≤ 1 / max (‖u‖ ^ 2) (1 / 4) := by
  have hM : max (‖u‖ ^ 2) (1 / 4) ≤ ‖u - latVec n‖ ^ 2 :=
    max_le (norm_sub_latVec_sq_ge hu n) (quarter_le_norm_sub_latVec_sq hu hn)
  have h1 : 0 < max (‖u‖ ^ 2) (1 / 4) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  exact one_div_le_one_div_of_le h1 hM

/-! ## The numerical ledger -/

/-- `π ^ (3/2) = π √π`. -/
lemma pi_rpow_three_halves : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
    Real.rpow_one, Real.sqrt_eq_rpow]

lemma pi_rpow_three_halves_gt : (5.5578 : ℝ) < Real.pi ^ (3 / 2 : ℝ) := by
  rw [pi_rpow_three_halves]
  have hsqrt : (1.772 : ℝ) < Real.sqrt Real.pi := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith [Real.pi_gt_d2]
  nlinarith [Real.pi_gt_d2, hsqrt]

lemma pi_rpow_three_halves_lt : Real.pi ^ (3 / 2 : ℝ) < (5.5908 : ℝ) := by
  rw [pi_rpow_three_halves]
  have hpi : Real.pi < (3.1416 : ℝ) := lt_trans Real.pi_lt_d20 (by norm_num)
  have hsqrt : Real.sqrt Real.pi < (1.77246 : ℝ) := by
    rw [Real.sqrt_lt Real.pi_pos.le (by norm_num)]
    nlinarith [Real.pi_lt_d20]
  have h2 : Real.pi * Real.sqrt Real.pi ≤ 3.1416 * 1.77246 :=
    mul_le_mul hpi.le hsqrt.le (Real.sqrt_nonneg _) (by norm_num)
  linarith

lemma sqrt_one_tenth_lt : Real.sqrt (1 / 10) < (0.31623 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

lemma sqrt_one_tenth_gt : (0.31622 : ℝ) < Real.sqrt (1 / 10) := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- `A = √η/(2π^{3/2}) ≤ 0.0285` at `η = 1/10`. -/
lemma const_A_le : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) ≤ 0.0285 := by
  have h1 : (0 : ℝ) < 2 * Real.pi ^ (3 / 2 : ℝ) := by
    have := pi_rpow_three_halves_gt; linarith
  rw [div_le_iff₀ h1]
  have h2 : Real.sqrt (1 / 10) ≤ (0.31623 : ℝ) := le_of_lt sqrt_one_tenth_lt
  have h3 : (0.31623 : ℝ) ≤ 0.0285 * (2 * Real.pi ^ (3 / 2 : ℝ)) := by
    have := pi_rpow_three_halves_gt; linarith
  linarith

/-- `B = 1/(4π^{3/2}√η) ≥ 0.14` at `η = 1/10`. -/
lemma const_B_ge : (0.14 : ℝ) ≤ 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10)) := by
  have h3 : (0 : ℝ) < Real.sqrt (1 / 10) := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (0 : ℝ) < 4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10) := by
    have h2 := pi_rpow_three_halves_gt
    positivity
  rw [le_div_iff₀ h1]
  have h2 : Real.pi ^ (3 / 2 : ℝ) ≤ (5.5908 : ℝ) := le_of_lt pi_rpow_three_halves_lt
  have h4 : Real.sqrt (1 / 10) ≤ (0.31623 : ℝ) := le_of_lt sqrt_one_tenth_lt
  have h5 : Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10) ≤ 5.5908 * 0.31623 :=
    mul_le_mul h2 h4 (le_of_lt h3) (by norm_num)
  nlinarith [h5]

/-- `C = 1/(48π^{3/2}η^{3/2}) ≤ 0.125` at `η = 1/10`. -/
lemma const_C_le : 1 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ)) ≤ 0.125 := by
  have h1 : (0 : ℝ) < 48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ) := by
    have h2 := pi_rpow_three_halves_gt
    have h3 : (0 : ℝ) < (1 / 10 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  rw [div_le_iff₀ h1]
  have h2 : (5.5578 : ℝ) ≤ Real.pi ^ (3 / 2 : ℝ) := le_of_lt pi_rpow_three_halves_gt
  have hlow : (0.0316 : ℝ) ≤ (1 / 10 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 10),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    have h3 : (0.31622 : ℝ) ≤ Real.sqrt (1 / 10) := le_of_lt sqrt_one_tenth_gt
    have h3' : (0.1 : ℝ) * 0.31622 ≤ 0.1 * Real.sqrt (1 / 10) :=
      mul_le_mul_of_nonneg_left h3 (by norm_num)
    linarith [h3']
  have hprod : 5.5578 * 0.0316 ≤ Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ) :=
    mul_le_mul h2 hlow (by norm_num) (by positivity)
  nlinarith [hprod]

/-- **The numerical ledger** with `η = 1/10` (all constants are explicit rationals).

For `0 ≤ ρ² ≤ 3/4` the bound obtained from the Ewald splitting is nonpositive:
`A (1/M) (1.65 - e^{-5ρ²/2}) - η + 1/250 - (B - C ρ²) ≤ 0` with `M = max(ρ²,1/4)`. -/
lemma ledger_bound {r2 : ℝ} (h0 : 0 ≤ r2) (h1 : r2 ≤ 3 / 4) :
    Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / max r2 (1 / 4))
        * (1.65 - Real.exp (-(5 / 2) * r2))
      - 1 / 10 + 1 / 250
      - (1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10))
          - r2 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))) ≤ 0 := by
  have hA := const_A_le
  have hB := const_B_ge
  have hC := const_C_le
  have hexp : (0 : ℝ) < Real.exp (-(5 / 2) * r2) := Real.exp_pos _
  have hexp1 : Real.exp (-(5 / 2) * r2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rcases lt_or_ge r2 (1 / 4) with hr | hr
  · have hm : max r2 (1 / 4) = 1 / 4 := max_eq_right hr.le
    rw [hm]
    have hstep : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / (1 / 4))
        * (1.65 - Real.exp (-(5 / 2) * r2)) ≤ 0.0285 * 4 * 1.65 := by
      have h2 : 1.65 - Real.exp (-(5 / 2) * r2) ≤ 1.65 := by linarith [hexp]
      have h3 : (0 : ℝ) ≤ 1.65 - Real.exp (-(5 / 2) * r2) := by linarith [hexp1]
      have h4 : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / (1 / 4))
          ≤ 4 * 0.0285 := by
        have h5 : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / (1 / 4))
            = 4 * (Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ))) := by ring
        rw [h5]
        linarith [mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 4)]
      calc Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / (1 / 4))
            * (1.65 - Real.exp (-(5 / 2) * r2))
          ≤ (4 * 0.0285) * 1.65 := mul_le_mul h4 h2 h3 (by norm_num)
        _ = 0.0285 * 4 * 1.65 := by ring
    have hCr : r2 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))
        ≤ 0.125 * (1 / 4) := by
      have hD : (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ 0.125 := by
        rw [← one_div]; exact hC
      have h5 : r2 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))
          = r2 * (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h5]
      calc r2 * (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))⁻¹
          ≤ (1 / 4) * 0.125 := mul_le_mul hr.le hD (by positivity) (by norm_num)
        _ = 0.125 * (1 / 4) := by ring
    linarith [hstep, hB, hCr]
  · have hm : max r2 (1 / 4) = r2 := max_eq_left hr
    rw [hm]
    have hr0 : 0 < r2 := lt_of_lt_of_le (by norm_num) hr
    have hstep : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / r2)
        * (1.65 - Real.exp (-(5 / 2) * r2)) ≤ 0.0285 * (1 / r2) * 1.65 := by
      have h2 : 1.65 - Real.exp (-(5 / 2) * r2) ≤ 1.65 := by
        linarith [Real.exp_pos (-(5 / 2) * r2)]
      have h3 : (0 : ℝ) ≤ 1.65 - Real.exp (-(5 / 2) * r2) := by linarith [hexp1]
      have h4 : (0 : ℝ) ≤ 1 / r2 := by positivity
      have h5 : Real.sqrt (1 / 10) / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / r2)
          ≤ 0.0285 * (1 / r2) := mul_le_mul_of_nonneg_right hA h4
      exact mul_le_mul h5 h2 h3 (by positivity)
    have hCr : r2 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ)) ≤ r2 * 0.125 := by
      have hD : (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ 0.125 := by
        rw [← one_div]; exact hC
      have h5 : r2 / (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))
          = r2 * (48 * Real.pi ^ (3 / 2 : ℝ) * (1 / 10 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h5]
      exact mul_le_mul_of_nonneg_left hD h0
    have hquad : 0.0285 * (1 / r2) * 1.65 + 0.125 * r2 ≤ 0.14 + 1 / 10 - 1 / 250 := by
      have key : 0.0285 * (1 / r2) * 1.65 = 0.047025 / r2 := by
        field_simp
        ring
      rw [key, div_add' (0.047025) (0.125 * r2) r2 (ne_of_gt hr0), div_le_iff₀ hr0]
      have hprod : (r2 - 1 / 4) * (r2 - 3 / 4) ≤ 0 := by
        have h5 : 0 ≤ r2 - 1 / 4 := by linarith
        have h6 : r2 - 3 / 4 ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos h5 h6
      nlinarith [hprod]
    linarith [hstep, hB, hCr, hquad]

theorem madelung_smooth_nonpos {u : EuclideanSpace ℝ (Fin 3)} (hu : u ≠ 0)
    (hcell : ∀ i, |u i| ≤ 1 / 2) :
    Work.BoseFixR.LatGreen.latGreenSmooth u ≤ 0 := by
  set η : ℝ := 1 / 10 with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; norm_num
  have hρ : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hρ2le : ‖u‖ ^ 2 ≤ 3 / 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (u i) ^ 2 ≤ ∑ _i : Fin 3, (1 / 4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨hl, hr⟩ := abs_le.mp (hcell i)
          nlinarith [hl, hr, sq_abs (u i)]
      _ = 3 / 4 := by norm_num
  have hρ2nn : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
  -- ## Integrability bookkeeping
  have hInt : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi 0) := md_integrableOn_f u hu hcell
  have h1int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 η) :=
    integrableOn_const (by rw [Real.volume_Ioc]; simp)
  have hsmall_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioc 0 η) :=
    hInt.mono_set Ioc_subset_Ioi_self
  have htail_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi η) :=
    hInt.mono_set (Ioi_subset_Ioi hη.le)
  have hKint : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioc 0 η) :=
    (md_integrableOn_heatK3_Ioi u hu).mono_set Ioc_subset_Ioi_self
  have hKtail : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioi η) :=
    (md_integrableOn_heatK3_Ioi u hu).mono_set (Ioi_subset_Ioi hη.le)
  have hHPint : IntegrableOn (fun t : ℝ => heatPeriod t u) (Ioc 0 η) := by
    refine (hsmall_int.add h1int).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [Pi.add_apply]
    ring
  have hdiffint : IntegrableOn (fun t : ℝ => heatPeriod t u - heatK3 t u) (Ioc 0 η) :=
    hHPint.sub hKint
  -- ## The split of `latGreen` at `η`
  have hsplit : latGreen u
      = (∫ t in Ioc 0 η, (heatPeriod t u - 1)) + ∫ t in Ioi η, (heatPeriod t u - 1) := by
    rw [latGreen, ← Set.Ioc_union_Ioi_eq_Ioi hη.le]
    rw [setIntegral_union (disjoint_left.mpr fun x hx => by
      simp only [Set.mem_Ioi, not_lt]
      exact hx.2) measurableSet_Ioi hsmall_int htail_int]
  -- ## The short-time integral, split into `(heatPeriod - heatK3)`, `heatK3` and `-η`
  have hsmalleq : (∫ t in Ioc 0 η, (heatPeriod t u - 1))
      = (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u)) + (∫ t in Ioc 0 η, heatK3 t u) - η := by
    have hA : (∫ t in Ioc 0 η, (heatPeriod t u - 1))
        = ∫ t in Ioc 0 η, ((fun t : ℝ => heatPeriod t u - heatK3 t u) t
            + (fun t : ℝ => heatK3 t u - 1) t) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by ring
    have hgint : Integrable (fun t : ℝ => heatK3 t u - 1)
        (MeasureTheory.volume.restrict (Ioc 0 η)) := hKint.sub h1int
    rw [hA, MeasureTheory.integral_add (f := fun t : ℝ => heatPeriod t u - heatK3 t u)
      (g := fun t : ℝ => heatK3 t u - 1) hdiffint hgint]
    rw [MeasureTheory.integral_sub (f := fun t : ℝ => heatK3 t u) (g := fun _ : ℝ => (1 : ℝ))
      hKint h1int]
    have hone : (∫ t in Ioc 0 η, (1 : ℝ)) = η := by
      rw [← intervalIntegral.integral_of_le hη.le, intervalIntegral.integral_const]
      simp
    rw [hone]
    ring
  -- ## The heat-kernel head bound, keeping the negative tail term
  have hA2 : (∫ t in Ioc 0 η, heatK3 t u)
      ≤ 1 / (4 * Real.pi * ‖u‖)
        - (1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η)
            - ‖u‖ ^ 2 / (48 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ))) := by
    have hsplitK : (∫ t in Ioi (0 : ℝ), heatK3 t u)
        = (∫ t in Ioc 0 η, heatK3 t u) + ∫ t in Ioi η, heatK3 t u := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hη.le]
      rw [setIntegral_union (disjoint_left.mpr fun x hx => by
        simp only [Set.mem_Ioi, not_lt]
        exact hx.2) measurableSet_Ioi hKint hKtail]
    have htailge := (heatK3_tail_ge (a := ‖u‖ ^ 2 / 4) (by positivity) hη).2
    have hcongr : (∫ t in Ioi η,
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖u‖ ^ 2 / 4 / t)))
        = ∫ t in Ioi η, heatK3 t u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [heatK3]
      congr 1
      ring_nf
    rw [hcongr] at htailge
    rw [HeatIntegral hu] at hsplitK
    have ha : ‖u‖ ^ 2 / 4 / (12 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ))
        = ‖u‖ ^ 2 / (48 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ)) := by
      ring
    rw [ha] at htailge
    linarith [hsplitK, htailge]
  -- ## The `(heatPeriod - heatK3)` head bound
  have hhead : (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u))
      ≤ Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / max (‖u‖ ^ 2) (1 / 4))
          * (1.65 - Real.exp (-(5 / 2) * ‖u‖ ^ 2)) := by
    set M : ℝ := max (‖u‖ ^ 2) (1 / 4) with hMdef
    have hMpos : (0 : ℝ) < M := by
      rw [hMdef]
      exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hM0 : (0 : ℝ) < 2 * Real.pi ^ (3 / 2 : ℝ) * M := by positivity
    -- the summability of the periodised heat kernel along the lattice
    have hsumm : ∀ t : ℝ, (0 : ℝ) < t →
        Summable (fun n : Fin 3 → ℤ => heatK3 t (u - latVec n)) := by
      intro t ht
      have h1 : Summable (fun n : Fin 3 → ℤ => Real.exp (-(1 / (4 * t)) * ‖u - latVec n‖ ^ 2)) :=
        latticeGaussSummable u (by positivity)
      refine (Summable.mul_left ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) h1).congr fun n => ?_
      rw [heatK3]
      congr 1
      ring_nf
    -- the shifted family, zeroed off `Ioc 0 η`
    set F : (Fin 3 → ℤ) → ℝ → ℝ := fun n t =>
      if t ∈ Set.Ioc 0 η then (if n = 0 then 0 else heatK3 t (u - latVec n)) else 0 with hFdef
    have hFnn : ∀ n t, 0 ≤ F n t := by
      intro n t
      rw [hFdef]
      by_cases ht : t ∈ Set.Ioc 0 η
      · simp only [ht, if_true]
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, if_false]
          exact heatK3_nonneg ht.1 _
      · simp [ht]
    have hFint : ∀ n, IntegrableOn (F n) (Ioc 0 η) := by
      intro n
      by_cases hn : n = 0
      · have hz : F n = fun _ : ℝ => (0 : ℝ) := by
          funext t
          rw [hFdef]
          by_cases ht : t ∈ Set.Ioc 0 η <;> simp [ht, hn]
        rw [hz]
        exact integrableOn_const (by rw [Real.volume_Ioc]; simp)
      · have hpos : (0 : ℝ) < ‖u - latVec n‖ ^ 2 / 4 := by
          have hlt : (0 : ℝ) < ‖u - latVec n‖ ^ 2 :=
            lt_of_lt_of_le (by norm_num) (quarter_le_norm_sub_latVec_sq hcell hn)
          positivity
        refine ((heatK3_head_le hpos hη).1).congr_fun ?_ measurableSet_Ioc
        intro t ht
        rw [hFdef]
        simp only [ht, if_true, hn, if_false, heatK3]
        congr 1
        ring_nf
    -- the majorant
    set g : (Fin 3 → ℤ) → ℝ := fun n =>
      Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
        * (if n = 0 then 0 else Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)) with hgdef
    have hgsum : Summable (fun n : Fin 3 → ℤ => Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)) :=
      latticeGaussSummable u (by norm_num)
    have hGsum : Summable (fun n : Fin 3 → ℤ =>
        if n = 0 then 0 else Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgsum
      · by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, if_false]
          exact Real.exp_nonneg _
      · by_cases hn : n = 0
        · simp [hn]
          exact Real.exp_nonneg _
        · simp only [hn, if_false]
          exact le_refl _
    have hG : Summable g := by
      rw [hgdef]
      exact Summable.mul_left _ hGsum
    have hFbound : ∀ n, (∫ t in Ioc 0 η, F n t) ≤ g n := by
      intro n
      by_cases hn : n = 0
      · have hz : (∫ t in Ioc 0 η, F n t) = 0 := by
          rw [show F n = fun _ : ℝ => (0 : ℝ) from by
            funext t
            rw [hFdef]
            by_cases ht : t ∈ Set.Ioc 0 η <;> simp [ht, hn]]
          simp
        rw [hz, hgdef]
        simp [hn]
      · have hlt : (0 : ℝ) < ‖u - latVec n‖ ^ 2 :=
          lt_of_lt_of_le (by norm_num) (quarter_le_norm_sub_latVec_sq hcell hn)
        have hpos : (0 : ℝ) < ‖u - latVec n‖ ^ 2 / 4 := by positivity
        have hb := (heatK3_head_le hpos hη).2
        have hcongr : (∫ t in Ioc 0 η, F n t)
            = ∫ t in Ioc 0 η,
                (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖u - latVec n‖ ^ 2 / 4 / t)) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [hFdef]
          simp only [ht, if_true, hn, if_false, heatK3]
          congr 1
          ring_nf
        rw [hcongr, hgdef]
        simp only [hn, if_false]
        refine le_trans hb ?_
        have hexp : -(‖u - latVec n‖ ^ 2 / 4 / η) = -(5 / 2) * ‖u - latVec n‖ ^ 2 := by
          rw [hηdef]
          ring
        rw [hexp]
        -- `8 * (|x|²/4) = 2 * |x|²` and `M ≤ |x|²`
        have hMle : M ≤ ‖u - latVec n‖ ^ 2 := by
          rw [hMdef]
          exact max_le (norm_sub_latVec_sq_ge hcell n) (quarter_le_norm_sub_latVec_sq hcell hn)
        have hgoal : Real.sqrt η * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)
              / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖u - latVec n‖ ^ 2 / 4))
            ≤ Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
                * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2) := by
          have hL : Real.sqrt η * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)
                / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖u - latVec n‖ ^ 2 / 4))
              = (Real.sqrt η * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))
                * (1 / (2 * Real.pi ^ (3 / 2 : ℝ) * ‖u - latVec n‖ ^ 2)) := by
            field_simp
            ring
          have hR : Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
                * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)
              = (Real.sqrt η * Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))
                * (1 / (2 * Real.pi ^ (3 / 2 : ℝ) * M)) := by
            field_simp
          rw [hL, hR]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_left hMle (by positivity))
        exact hgoal
    -- the exchange of sum and integral
    have hsummInt : Summable (fun n : Fin 3 → ℤ => ∫ t in Ioc 0 η, F n t) :=
      Summable.of_nonneg_of_le
        (fun n => setIntegral_nonneg measurableSet_Ioc fun t ht => hFnn n t)
        hFbound hG
    have hkey : (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u))
        = ∑' n : Fin 3 → ℤ, ∫ t in Ioc 0 η, F n t := by
      have hpt : ∀ t ∈ Set.Ioc 0 η, heatPeriod t u - heatK3 t u = ∑' n, F n t := by
        intro t ht
        have ht0 : 0 < t := ht.1
        have hite : (∑' n : Fin 3 → ℤ, F n t)
            = ∑' n : Fin 3 → ℤ, (if n = 0 then (0 : ℝ) else heatK3 t (u - latVec n)) := by
          refine tsum_congr fun n => ?_
          rw [hFdef]
          simp only [ht, if_true]
        rw [hite, heatPeriod, (hsumm t ht0).tsum_eq_add_tsum_ite 0]
        have hzero : latVec (0 : Fin 3 → ℤ) = 0 := by
          ext i
          simp [latVec]
        rw [hzero, sub_zero]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioc hpt]
      exact integral_tsum_Ioc hη hFnn hFint hsummInt
    rw [hkey]
    -- the sum of the majorants
    have hsum0 : Summable (fun n : Fin 3 → ℤ => Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
        * (if n = 0 then 0 else Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))) :=
      Summable.mul_left _ hGsum
    have hsplit0 : (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
          Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2)))
        = (∑' n : Fin 3 → ℤ, Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))
          - Real.exp (-(5 / 2) * ‖u‖ ^ 2) := by
      have h := hgsum.tsum_eq_add_tsum_ite 0
      have hzero : latVec (0 : Fin 3 → ℤ) = 0 := by
        ext i
        simp [latVec]
      rw [hzero, sub_zero] at h
      linarith [h]
    calc ∑' n : Fin 3 → ℤ, ∫ t in Ioc 0 η, F n t
        ≤ ∑' n : Fin 3 → ℤ, g n := by
          rw [hgdef]
          exact hsummInt.tsum_le_tsum hFbound hsum0
      _ = Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
            * (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
                Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))) := by
          rw [hgdef]
          exact tsum_mul_left
      _ = Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
            * ((∑' n : Fin 3 → ℤ, Real.exp (-(5 / 2) * ‖u - latVec n‖ ^ 2))
              - Real.exp (-(5 / 2) * ‖u‖ ^ 2)) := by
          rw [hsplit0]
      _ ≤ Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ) * M)
            * (1.65 - Real.exp (-(5 / 2) * ‖u‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [latticeGaussSum_le u]
      _ = Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / max (‖u‖ ^ 2) (1 / 4))
            * (1.65 - Real.exp (-(5 / 2) * ‖u‖ ^ 2)) := by
          rw [hMdef]
          ring
  -- ## The tail
  have htail : (∫ t in Ioi η, (heatPeriod t u - 1)) ≤ 1 / 250 := by
    rw [hηdef]
    exact tailIntegral_le u
  -- ## Assembly
  have hfinal : latGreenSmooth u
      ≤ Real.sqrt η / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / max (‖u‖ ^ 2) (1 / 4))
          * (1.65 - Real.exp (-(5 / 2) * ‖u‖ ^ 2)) - η + 1 / 250
        - (1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η)
            - ‖u‖ ^ 2 / (48 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ))) := by
    have hlat : latGreenSmooth u = latGreen u - 1 / (4 * Real.pi * ‖u‖) := rfl
    rw [hlat, hsplit, hsmalleq]
    linarith [hA2, hhead, htail]
  have hledger := ledger_bound (r2 := ‖u‖ ^ 2) hρ2nn hρ2le
  rw [hηdef] at hfinal
  linarith [hfinal, hledger]

end Work.BoseFixR.LatGreen
