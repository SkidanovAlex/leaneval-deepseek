import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs
import Submission.Commons.Analysis.Convolution.integrableOn_Ioi_rpow_max_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Convergence of the truncated Plancherel integral

For a `1`-bounded coefficient sequence `f : ℕ → ℂ` and `α > 0` we show that the truncated
Mellin–Plancherel integral

`N ↦ ∫_0^∞ ‖KfN f N t‖² / t^{3+2α} dt`

converges, as `N → ∞`, to

`∫_0^∞ ‖Kf f t‖² / t^{3+2α} dt`,

where `KfN f N t = Σ_{n ≤ min N ⌊t⌋} f n log n` and `Kf f t = Σ_{n ≤ ⌊t⌋} f n log n`.

The proof is a dominated-convergence argument.  Pointwise `KfN f N t = Kf f t` for `N ≥ ⌊t⌋`,
and the dominating function is `(4/α²) · (max 1 t)^{-(1+α)}`, which is integrable on `(0, ∞)` and
dominates the integrand:  `‖KfN f N t‖ ≤ ⌊t⌋ log ⌊t⌋` and `(m log m)² ≤ (4/α²) m^{2+α}`.
-/

open Finset MeasureTheory Filter
open scoped Topology

namespace Work.BMF

/-- Sub-polynomial growth of the logarithm in the shape needed below: for `α > 0` and every
`M : ℕ`, `(M log M)² ≤ (4/α²) M^{2+α}`.  The proof uses `log M ≤ M^{α/2}/(α/2)`. -/
private lemma log_nat_sq_le (α : ℝ) (hα : 0 < α) (M : ℕ) :
    ((M : ℝ) * Real.log (M : ℝ)) ^ 2 ≤ (4 / α ^ 2) * (M : ℝ) ^ (2 + α) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Nat.cast_zero, zero_mul, Real.log_zero]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Real.zero_rpow (by positivity : (2 : ℝ) + α ≠ 0),
      mul_zero]
  · have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := le_of_lt hMpos
    have hlog_le : Real.log (M : ℝ) ≤ (2 / α) * (M : ℝ) ^ (α / 2) := by
      have h := Real.log_le_rpow_div hMnn (show (0 : ℝ) < α / 2 by positivity)
      have hdiv : (M : ℝ) ^ (α / 2) / (α / 2) = (2 / α) * (M : ℝ) ^ (α / 2) := by
        have hα2 : α / 2 ≠ 0 := by positivity
        field_simp
      rwa [hdiv] at h
    have hlog_nn : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
    have h1 : (Real.log (M : ℝ)) ^ 2 ≤ ((2 / α) * (M : ℝ) ^ (α / 2)) ^ 2 :=
      pow_le_pow_left₀ hlog_nn hlog_le 2
    have h2 : ((2 / α) * (M : ℝ) ^ (α / 2)) ^ 2 = (4 / α ^ 2) * (M : ℝ) ^ α := by
      rw [mul_pow]
      congr 1
      · ring
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hMnn]
        congr 1
        ring
    have hlog_sq : (Real.log (M : ℝ)) ^ 2 ≤ (4 / α ^ 2) * (M : ℝ) ^ α := h1.trans (le_of_eq h2)
    have hsplit : (M : ℝ) ^ (2 + α) = (M : ℝ) ^ 2 * (M : ℝ) ^ α := by
      rw [Real.rpow_add hMpos]; simp
    calc ((M : ℝ) * Real.log (M : ℝ)) ^ 2
        = (M : ℝ) ^ 2 * (Real.log (M : ℝ)) ^ 2 := by rw [mul_pow]
      _ ≤ (M : ℝ) ^ 2 * ((4 / α ^ 2) * (M : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_left hlog_sq (sq_nonneg _)
      _ = (4 / α ^ 2) * (M : ℝ) ^ (2 + α) := by rw [hsplit]; ring

/-- The truncated summatory function is bounded by `M log M`, `M = min N ⌊t⌋`. -/
private lemma KfN_norm_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) (t : ℝ) :
    ‖KfN f N t‖ ≤ ((min N ⌊t⌋₊ : ℕ) : ℝ) * Real.log ((min N ⌊t⌋₊ : ℕ) : ℝ) := by
  rw [KfN]
  set M := min N ⌊t⌋₊ with hM
  calc ‖∑ n ∈ Icc 1 M, f n * (Real.log n : ℂ)‖
      ≤ ∑ n ∈ Icc 1 M, ‖f n * (Real.log n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 M, Real.log (n : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_natCast_nonneg n)]
        exact mul_le_of_le_one_left (Real.log_natCast_nonneg n) (hb n)
    _ ≤ (M : ℝ) * Real.log (M : ℝ) := by
        have h1 : ∀ n ∈ Icc 1 M, Real.log (n : ℝ) ≤ Real.log (M : ℝ) := by
          intro n hn
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          exact Real.log_le_log (by linarith) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
        calc ∑ n ∈ Icc 1 M, Real.log (n : ℝ)
            ≤ ∑ n ∈ Icc 1 M, Real.log (M : ℝ) := Finset.sum_le_sum h1
          _ = (M : ℝ) * Real.log (M : ℝ) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- The integrand `t ↦ ‖KfN f N t‖²/t^{3+2α}` is measurable (for `α > 0`). -/
private lemma measurable_integrand_KfN (f : ℕ → ℂ) (N : ℕ) {α : ℝ} (hα : 0 < α) :
    Measurable (fun t : ℝ => ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α)) := by
  have hKfN : Measurable (fun t : ℝ => KfN f N t) := by
    have hS : Measurable (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (Real.log n : ℂ)) :=
      measurable_of_countable _
    have hfloor : Measurable (fun t : ℝ => ⌊t⌋₊) := Nat.measurable_floor
    have hmin : Measurable (fun t : ℝ => min N ⌊t⌋₊) := measurable_const.min hfloor
    exact hS.comp hmin
  exact (hKfN.norm.pow_const 2).div
    ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 3 + 2 * α)).measurable)

/-- Pointwise convergence of the truncations. -/
private lemma tendsto_KfN (f : ℕ → ℂ) (t : ℝ) :
    Tendsto (fun N : ℕ => KfN f N t) atTop (nhds (Kf f t)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌊t⌋₊] with N hN
  simp only [KfN, Kf]
  rw [min_eq_right hN]

/-- Domination of the integrand by `(4/α²)(max 1 t)^{-(1+α)}` on `t > 0`. -/
private lemma KfN_integrand_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (hα : 0 < α)
    (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α) ≤ (4 / α ^ 2) * (max 1 t) ^ (-(1 + α)) := by
  set M := min N ⌊t⌋₊ with hM
  have hnorm : ‖KfN f N t‖ ≤ (M : ℝ) * Real.log (M : ℝ) := by
    rw [hM]; exact KfN_norm_le f hb N t
  rcases le_or_gt t 1 with ht1 | ht1
  · have hfloor : ⌊t⌋₊ ≤ 1 := by
      have h := (Nat.floor_lt (le_of_lt ht) (n := 2)).mpr (by linarith : t < 2)
      omega
    have hM1 : M ≤ 1 := by rw [hM]; exact le_trans (min_le_right _ _) hfloor
    have hMlog : (M : ℝ) * Real.log (M : ℝ) = 0 := by
      have h01 : M = 0 ∨ M = 1 := by omega
      rcases h01 with h | h <;> simp [h, Real.log_zero, Real.log_one]
    have hzero : ‖KfN f N t‖ = 0 := by
      rw [hMlog] at hnorm
      exact le_antisymm hnorm (norm_nonneg _)
    rw [hzero, max_eq_left ht1]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, Real.one_rpow, mul_one]
    exact div_nonneg (by norm_num) (sq_nonneg α)
  · have hmax : max 1 t = t := max_eq_right (le_of_lt ht1)
    have hMt : (M : ℝ) ≤ t := by
      rw [hM]
      calc ((min N ⌊t⌋₊ : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
            exact_mod_cast min_le_right N ⌊t⌋₊
        _ ≤ t := Nat.floor_le (le_of_lt ht)
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hrpow_le : (M : ℝ) ^ (2 + α) ≤ t ^ (2 + α) := Real.rpow_le_rpow hMnn hMt (by linarith)
    have hnorm_sq : ‖KfN f N t‖ ^ 2 ≤ ((M : ℝ) * Real.log (M : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hlogM_sq : ((M : ℝ) * Real.log (M : ℝ)) ^ 2 ≤ (4 / α ^ 2) * (M : ℝ) ^ (2 + α) :=
      log_nat_sq_le α hα M
    have htpos : (0 : ℝ) ≤ t ^ (3 + 2 * α) := Real.rpow_nonneg (le_of_lt ht) _
    calc ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α)
        ≤ ((M : ℝ) * Real.log (M : ℝ)) ^ 2 / t ^ (3 + 2 * α) :=
          div_le_div_of_nonneg_right hnorm_sq htpos
      _ ≤ ((4 / α ^ 2) * (M : ℝ) ^ (2 + α)) / t ^ (3 + 2 * α) :=
          div_le_div_of_nonneg_right hlogM_sq htpos
      _ ≤ ((4 / α ^ 2) * t ^ (2 + α)) / t ^ (3 + 2 * α) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow_le (by positivity)) htpos
      _ = (4 / α ^ 2) * t ^ (-(1 + α)) := by
          rw [div_eq_mul_inv, mul_assoc, ← Real.rpow_neg (le_of_lt ht) (3 + 2 * α),
            ← Real.rpow_add ht]
          congr 1
          congr 1
          ring
      _ = (4 / α ^ 2) * (max 1 t) ^ (-(1 + α)) := by rw [hmax]

/-- Convergence of the truncated Plancherel integral to the full one. -/
theorem tendsto_integral_KfN (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun N : ℕ => ∫ t in Set.Ioi (0 : ℝ), ‖KfN f N t‖ ^ 2 / t ^ (3 + 2 * α))
      Filter.atTop (nhds (∫ t in Set.Ioi (0 : ℝ), ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α))) := by
  have hbd : Integrable (fun t : ℝ => (4 / α ^ 2) * (max 1 t) ^ (-(1 + α)))
      (volume.restrict (Set.Ioi 0)) := by
    have h := (Commons.Analysis.Convolution.integrableOn_Ioi_rpow_max_one 1 le_rfl (1 + α)
      (by exact_mod_cast (by linarith : (1 : ℝ) < 1 + α))).integrable
    simpa using h.const_mul (4 / α ^ 2)
  refine tendsto_integral_of_dominated_convergence
    (fun t : ℝ => (4 / α ^ 2) * (max 1 t) ^ (-(1 + α)))
    (fun N => (measurable_integrand_KfN f N hα).aestronglyMeasurable)
    hbd ?_ ?_
  · intro N
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _))]
    exact KfN_integrand_le f hb α hα N ht
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have hq : t ^ (3 + 2 * α) ≠ 0 :=
      (Real.rpow_ne_zero (le_of_lt ht) (by linarith : (3 + 2 * α) ≠ 0)).mpr (ne_of_gt ht)
    exact ((tendsto_KfN f t).norm.pow 2).div tendsto_const_nhds hq

end Work.BMF
