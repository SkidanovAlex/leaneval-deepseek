import Mathlib
import Submission.Work.NN.Core.czbL2Cut

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Pointwise

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-!
# The weighted energy of the radial cut-off vanishes

`cutC R` is the smooth radial cut-off equal to `1` on the Euclidean ball of radius `R/√2` and
equal to `0` off the Euclidean ball of radius `R`.  This file proves that its weighted
`L²`-energy against a continuous function `u` decaying like `‖z‖^{1-2n}` tends to `0`:

`∫ z, ‖u z‖² · Σ_j ‖∂_j (cutC R) z‖²  ⟶ 0`  and the same with `∂̄_j`.

The proof is a direct estimate.  Both sums of squared Wirtinger derivatives have the closed form
`(φ'(nrmSq z / R²))² / R⁴ · nrmSq z` (where `φ` is the cut-off profile), whose support is the
Euclidean shell `R/√2 ≤ eucNorm z ≤ R`.  On that shell `‖z‖ ≍ R`, so the decay hypothesis gives
`‖u‖² ≲ R^{2-4n}` while the derivative bound gives `Σ_j ‖∂_j cutC‖² ≤ K/R²`; multiplying by the
volume `≍ R^{2n}` of the ball of radius `R` produces `O(R^{-2n})` (indeed `O(R^{-1})`).
-/

/-- The squared modulus of the Wirtinger gradient of `cutC R`, in closed form. -/
def cutSq {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : ℝ :=
  (deriv Work.CR.Flat.Cauchy.cutProfile (nrmSq z / R ^ 2)) ^ 2 / R ^ 4 * nrmSq z

lemma cutSq_nonneg {n : ℕ} (R : ℝ) (z : Fin n → ℂ) : 0 ≤ cutSq R z := by
  rw [cutSq]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (nrmSq_nonneg z)

lemma cutSq_eq_sum_dCoord {n : ℕ} (R : ℝ) (z : Fin n → ℂ) :
    cutSq (n := n) R z = ∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2 :=
  (sum_normSq_dCoord_cutC z).symm

lemma cutSq_eq_sum_dbarCoord {n : ℕ} (R : ℝ) (z : Fin n → ℂ) :
    cutSq (n := n) R z = ∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2 :=
  (sum_normSq_dbarCoord_cutC z).symm

lemma cutSq_eq_zero_of_lt {n : ℕ} {R : ℝ} (hR : 0 < R) {z : Fin n → ℂ}
    (h : 2 * nrmSq z < R ^ 2) : cutSq (n := n) R z = 0 := by
  have h2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
  have ht : nrmSq z / R ^ 2 < 1 / 2 := by
    rw [div_lt_iff₀ h2]; linarith
  rw [cutSq, deriv_cutProfile_eq_zero_of_lt_half ht]
  simp

lemma cutSq_eq_zero_of_gt {n : ℕ} {R : ℝ} (hR : 0 < R) {z : Fin n → ℂ}
    (h : R ^ 2 < nrmSq z) : cutSq (n := n) R z = 0 := by
  have h2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
  have ht : 1 < nrmSq z / R ^ 2 := by rw [one_lt_div h2]; exact h
  rw [cutSq, deriv_cutProfile_eq_zero_of_one_lt ht]
  simp

/-- `(x ^ p) ^ 2 = (x ^ 2) ^ p`. -/
lemma sq_rpow_eq (x p : ℝ) (hx : 0 ≤ x) : (x ^ p) ^ 2 = (x ^ 2) ^ p := by
  rw [← Real.rpow_natCast (x ^ p) 2]
  rw [← Real.rpow_mul hx p ((2 : ℕ) : ℝ)]
  rw [show p * ((2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) * p by ring]
  rw [Real.rpow_mul hx ((2 : ℕ) : ℝ) p]
  rw [Real.rpow_natCast]

/-- The Lebesgue volume of the Euclidean ball of radius `R` in `ℂⁿ` is `O(R^{2n})`. -/
lemma volume_real_eucClosedBall_le {n : ℕ} :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ R : ℝ, 0 < R →
      volume.real (eucClosedBall (n := n) R) ≤ V * R ^ (2 * (n : ℝ)) := by
  refine ⟨volume.real (Metric.closedBall (0 : Fin n → ℂ) (1 : ℝ)), ?_, ?_⟩
  · rw [Measure.real_def]; exact ENNReal.toReal_nonneg
  · intro R hR
    have hsub : eucClosedBall (n := n) R ⊆ Metric.closedBall (0 : Fin n → ℂ) R := by
      intro z hz
      rw [mem_eucClosedBall] at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (pi_norm_le_eucNorm z) hz
    have h2 : volume (Metric.closedBall (0 : Fin n → ℂ) R) ≠ ∞ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
        (measure_ball_lt_top (x := (0 : Fin n → ℂ)) (r := R + 1)))
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith
    refine le_trans (measureReal_mono hsub h2) ?_
    have hscale : Metric.closedBall (0 : Fin n → ℂ) R
        = R • Metric.closedBall (0 : Fin n → ℂ) (1 : ℝ) := by
      ext x
      constructor
      · intro hx
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        refine ⟨R⁻¹ • x, ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hR), inv_mul_le_iff₀ hR]
          simpa using hx
        · simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      · rintro ⟨y, hy, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hR]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        nlinarith [hy, hR.le]
    rw [hscale, Measure.real_def,
      Measure.addHaar_smul_of_nonneg (volume : Measure (Fin n → ℂ)) hR.le
        (Metric.closedBall (0 : Fin n → ℂ) (1 : ℝ)),
      show Module.finrank ℝ (Fin n → ℂ) = 2 * n from by
        rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring,
      ENNReal.toReal_mul, ← Real.rpow_natCast R (2 * n),
      show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hR.le _), Measure.real_def, mul_comm]

/-- **The weighted energy of the cut-off vanishes.** -/
theorem tendsto_integral_cutSq_mul {n : ℕ} (hn : 0 < n) {u : (Fin n → ℂ) → ℂ} {R₀ C : ℝ}
    (hR₀ : 0 < R₀) (hC : 0 ≤ C) (hcont : Continuous u)
    (hdec : ∀ z, R₀ ≤ ‖z‖ → ‖u z‖ ≤ C * ‖z‖ ^ (1 - 2 * (n : ℝ))) :
    Filter.Tendsto (fun N : ℕ => ∫ z, ‖u z‖ ^ 2 * cutSq (n := n) (N + 1) z)
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨K, hK0, hKb⟩ := exists_bound_sum_normSq_dCoord_cutC
  obtain ⟨V, hV0, hV⟩ := volume_real_eucClosedBall_le (n := n)
  have hcutb : ∀ R z, 0 < R → cutSq (n := n) R z ≤ K / R ^ 2 := by
    intro R z hR; rw [cutSq_eq_sum_dCoord]; exact hKb R z hR
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (2 * (n : ℝ)) with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr (by positivity)
  have hs_sq : s ^ 2 = 2 * (n : ℝ) := by rw [hsdef]; exact Real.sq_sqrt (by positivity)
  have hp_neg : 1 - 2 * (n : ℝ) ≤ 0 := by linarith
  set Rthr : ℝ := max 1 (max (2 * (n : ℝ)) (R₀ * s)) with hRthr
  -- ## Pointwise bound
  have hpt : ∀ R : ℝ, Rthr ≤ R → ∀ z : Fin n → ℂ,
      ‖u z‖ ^ 2 * cutSq (n := n) R z ≤
        (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) *
          (eucClosedBall (n := n) R).indicator (fun _ => (1 : ℝ)) z := by
    intro R hRR z
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hRR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
    have hR2n : 2 * (n : ℝ) ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hRR)
    have hRs : R₀ * s ≤ R :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hRR)
    have hR2pos : (0 : ℝ) < R ^ 2 := pow_pos hRpos 2
    have hMnn : 0 ≤ C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ)) :=
      mul_nonneg (mul_nonneg (sq_nonneg C) (div_nonneg hK0 hR2pos.le))
        (Real.rpow_nonneg hRpos.le _)
    by_cases hz : z ∈ eucClosedBall (n := n) R
    · rw [Set.indicator_of_mem hz, mul_one]
      rw [mem_eucClosedBall] at hz
      by_cases hsh : 2 * nrmSq z < R ^ 2
      · rw [cutSq_eq_zero_of_lt hRpos hsh, mul_zero]; exact hMnn
      · push_neg at hsh
        have hnorm2 : R ^ 2 / (2 * (n : ℝ)) ≤ ‖z‖ ^ 2 := by
          have h1 := nrmSq_le_card_mul z
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
          nlinarith [h1, hsh]
        have hzlow : R / s ≤ ‖z‖ := by
          have hsqrt : Real.sqrt (R ^ 2 / (2 * (n : ℝ))) ≤ Real.sqrt (‖z‖ ^ 2) :=
            Real.sqrt_le_sqrt hnorm2
          rw [Real.sqrt_sq (norm_nonneg z)] at hsqrt
          have hsq : R ^ 2 / (2 * (n : ℝ)) = (R / s) ^ 2 := by
            rw [div_pow, hs_sq]
          rw [hsq, Real.sqrt_sq (div_nonneg hRpos.le hs_pos.le)] at hsqrt
          exact hsqrt
        have hzR0 : R₀ ≤ ‖z‖ := by
          refine le_trans ?_ hzlow
          rw [le_div_iff₀ hs_pos]; exact hRs
        have huz := hdec z hzR0
        have hu2 : ‖u z‖ ^ 2 ≤ C ^ 2 * R ^ (1 - 2 * (n : ℝ)) := by
          have h1 : ‖u z‖ ^ 2 ≤ (C * ‖z‖ ^ (1 - 2 * (n : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) huz 2
          have h2 : (C * ‖z‖ ^ (1 - 2 * (n : ℝ))) ^ 2
              = C ^ 2 * (‖z‖ ^ 2) ^ (1 - 2 * (n : ℝ)) := by
            rw [mul_pow, sq_rpow_eq ‖z‖ (1 - 2 * (n : ℝ)) (norm_nonneg z)]
          have h3 : (‖z‖ ^ 2) ^ (1 - 2 * (n : ℝ))
              ≤ (R ^ 2 / (2 * (n : ℝ))) ^ (1 - 2 * (n : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hnorm2 hp_neg
          have h4 : (R ^ 2 / (2 * (n : ℝ))) ^ (1 - 2 * (n : ℝ))
              ≤ R ^ (1 - 2 * (n : ℝ)) := by
            refine Real.rpow_le_rpow_of_nonpos hRpos ?_ hp_neg
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
            nlinarith [hR2n, hRpos]
          calc ‖u z‖ ^ 2 ≤ (C * ‖z‖ ^ (1 - 2 * (n : ℝ))) ^ 2 := h1
            _ = C ^ 2 * (‖z‖ ^ 2) ^ (1 - 2 * (n : ℝ)) := h2
            _ ≤ C ^ 2 * (R ^ 2 / (2 * (n : ℝ))) ^ (1 - 2 * (n : ℝ)) :=
                mul_le_mul_of_nonneg_left h3 (sq_nonneg C)
            _ ≤ C ^ 2 * R ^ (1 - 2 * (n : ℝ)) :=
                mul_le_mul_of_nonneg_left h4 (sq_nonneg C)
        calc ‖u z‖ ^ 2 * cutSq R z
            ≤ (C ^ 2 * R ^ (1 - 2 * (n : ℝ))) * (K / R ^ 2) :=
              mul_le_mul hu2 (hcutb R z hRpos) (cutSq_nonneg R z)
                (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hRpos.le _))
          _ = C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ)) := by ring
    · rw [Set.indicator_of_notMem hz, mul_zero]
      rw [mem_eucClosedBall, not_le] at hz
      have h1 : R ^ 2 < nrmSq z := by
        rw [nrmSq_eq_eucNorm_sq]; nlinarith [hz, eucNorm_nonneg z]
      rw [cutSq_eq_zero_of_gt hRpos h1, mul_zero]
  -- ## Integral bound
  have hint : ∀ R : ℝ, Rthr ≤ R →
      ∫ z, ‖u z‖ ^ 2 * cutSq (n := n) R z ≤ (C ^ 2 * K * V) * R ^ (-1 : ℝ) := by
    intro R hRR
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hRR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
    have hR2pos : (0 : ℝ) < R ^ 2 := pow_pos hRpos 2
    have hmes : MeasurableSet (eucClosedBall (n := n) R) :=
      (isClosed_le continuous_eucNorm continuous_const).measurableSet
    have hfin : volume (eucClosedBall (n := n) R) ≠ ∞ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
        (measure_ball_lt_top (x := (0 : Fin n → ℂ)) (r := R + 1)))
      intro z hz
      rw [mem_eucClosedBall] at hz
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (pi_norm_le_eucNorm z) (by linarith)
    have hInt_ind : Integrable
        ((eucClosedBall (n := n) R).indicator (fun _ => (1 : ℝ))) volume := by
      rw [integrable_indicator_iff hmes]
      exact integrableOn_const hfin (by simp)
    have hInt_g : Integrable (fun z : Fin n → ℂ =>
        (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) *
          (eucClosedBall (n := n) R).indicator (fun _ => (1 : ℝ)) z) volume :=
      hInt_ind.const_mul _
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (cutSq_nonneg R z)))
      hInt_g (Eventually.of_forall (hpt R hRR))
    refine le_trans hmono ?_
    have hval : ∫ z : Fin n → ℂ, (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) *
          (eucClosedBall (n := n) R).indicator (fun _ => (1 : ℝ)) z
        = (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) *
            volume.real (eucClosedBall (n := n) R) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_indicator_one hmes
    rw [hval]
    have hVb := hV R hRpos
    have hA : 0 ≤ C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ)) :=
      mul_nonneg (mul_nonneg (sq_nonneg C) (div_nonneg hK0 hR2pos.le))
        (Real.rpow_nonneg hRpos.le _)
    have he : R ^ (-2 : ℝ) * R ^ (1 - 2 * (n : ℝ)) * R ^ (2 * (n : ℝ))
        = R ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hRpos, ← Real.rpow_add hRpos]
      congr 1
      ring
    have hdiv : K / R ^ 2 = K * R ^ (-2 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_natCast R 2,
        ← Real.rpow_neg hRpos.le ((2 : ℕ) : ℝ)]
      norm_num
    calc (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) * volume.real (eucClosedBall (n := n) R)
        ≤ (C ^ 2 * (K / R ^ 2) * R ^ (1 - 2 * (n : ℝ))) * (V * R ^ (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hVb hA
      _ = (C ^ 2 * K * V) * R ^ (-1 : ℝ) := by
          rw [hdiv]
          calc C ^ 2 * (K * R ^ (-2 : ℝ)) * R ^ (1 - 2 * (n : ℝ)) * (V * R ^ (2 * (n : ℝ)))
              = C ^ 2 * K * V * (R ^ (-2 : ℝ) * R ^ (1 - 2 * (n : ℝ)) * R ^ (2 * (n : ℝ))) := by
                ring
            _ = C ^ 2 * K * V * R ^ (-1 : ℝ) := by rw [he]
  -- ## Squeeze
  have hev : ∀ᶠ N : ℕ in Filter.atTop, Rthr ≤ (N : ℝ) + 1 := by
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil Rthr)] with N hN
    have h1 : Rthr ≤ (Nat.ceil Rthr : ℝ) := Nat.le_ceil Rthr
    have h2 : (Nat.ceil Rthr : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlim : Filter.Tendsto
      (fun N : ℕ => (C ^ 2 * K * V) * (((N : ℝ) + 1) ^ (-1 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) ^ (-1 : ℝ)))
        Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp h1
    simpa using h2.const_mul (C ^ 2 * K * V)
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ hlim
  · exact integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (cutSq_nonneg _ z))
  · filter_upwards [hev] with N hN
    have h := hint ((N : ℝ) + 1) hN
    simpa [Nat.cast_add, Nat.cast_one] using h

theorem tendsto_integral_cutC_sq_mul {n : ℕ} {u : (Fin n → ℂ) → ℂ} {R₀ C : ℝ}
    (hR₀ : 0 < R₀) (hC : 0 ≤ C) (hcont : Continuous u)
    (hdec : ∀ z, R₀ ≤ ‖z‖ → ‖u z‖ ≤ C * ‖z‖ ^ (1 - 2 * (n : ℝ))) :
    (Filter.Tendsto (fun N : ℕ => ∫ z, ‖u z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dCoord j (Work.NN.Core.cutC (n := n) (N + 1)) z‖ ^ 2)) Filter.atTop (nhds 0))
    ∧ (Filter.Tendsto (fun N : ℕ => ∫ z, ‖u z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dbarCoord j (Work.NN.Core.cutC (n := n) (N + 1)) z‖ ^ 2)) Filter.atTop (nhds 0)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    constructor <;> simp
  · have hmain := tendsto_integral_cutSq_mul (n := n) hn hR₀ hC hcont hdec
    constructor
    · refine hmain.congr (fun N => ?_)
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Work.NN.Core.cutSq_eq_sum_dCoord]))
    · refine hmain.congr (fun N => ?_)
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Work.NN.Core.cutSq_eq_sum_dbarCoord]))

end Work.NN.Core
