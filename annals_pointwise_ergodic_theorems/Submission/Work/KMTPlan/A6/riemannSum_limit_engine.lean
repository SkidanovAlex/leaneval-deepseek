import Mathlib
import Submission.Work.KMTPlan.A6.riemannSum_uniform_compare
import Submission.Work.KMTPlan.A6.latticeSum_bound

set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory Filter Finset intervalIntegral
open scoped ENNReal BigOperators Topology

noncomputable section

/-- Summability over `ℤ` of the lattice weight `A / (1 + c |m|)^2`. -/
theorem summable_lattice_inv_sq (A : ℝ) (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ => A / (1 + c * |(m : ℝ)|) ^ 2) := by
  have h := (sum_inv_sq_linear_int_le 1 c one_pos hc).2.1
  exact (h.mul_left A).congr (fun m => by rw [mul_one_div])

/-- A function satisfying the `min |t| |s|` Lipschitz bound is continuous. -/
theorem continuous_of_min_lipschitz {F : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ t s : ℝ, |F t - F s| ≤ A / (1 + min |t| |s|) ^ 2 * |t - s|) :
    Continuous F := by
  have hle : ∀ t s : ℝ, |F t - F s| ≤ A * |t - s| := by
    intro t s
    have hm : (0 : ℝ) ≤ min |t| |s| := le_min (abs_nonneg t) (abs_nonneg s)
    have h1 : (1 : ℝ) ≤ 1 + min |t| |s| := by linarith
    have h2 : A / (1 + min |t| |s|) ^ 2 ≤ A := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (min |t| |s|), hm, hA]
    exact (hF t s).trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε / (A + 1), by positivity, fun y hy => ?_⟩
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  rw [Real.dist_eq] at hy ⊢
  have h3 : A * (ε / (A + 1)) < ε := by
    have h4 : A * (ε / (A + 1)) = (A * ε) / (A + 1) := by ring
    rw [h4, div_lt_iff₀ hA1]
    nlinarith [hε, hA]
  calc |F y - F x| ≤ A * |y - x| := hle y x
    _ ≤ A * (ε / (A + 1)) := mul_le_mul_of_nonneg_left hy.le hA
    _ < ε := h3

/-- A function decaying like `A/(1+|t|)^2` and a.e. strongly measurable is integrable. -/
theorem integrable_of_decay {F : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hmeas : AEStronglyMeasurable F volume) (hF : ∀ t : ℝ, |F t| ≤ A / (1 + |t|) ^ 2) :
    Integrable F := by
  have hbase : Integrable (fun t : ℝ => A * (1 + ‖t‖) ^ (-(2 : ℝ))) volume := by
    have h0 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) volume :=
      integrable_one_add_norm (μ := volume) (E := ℝ) (by rw [Module.finrank_self]; norm_num)
    exact h0.const_mul A
  refine hbase.mono' hmeas ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  calc |F t| ≤ A / (1 + |t|) ^ 2 := hF t
    _ = A * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
        rw [Real.norm_eq_abs t, Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]

/-- The absolute value of `(Q m)/R` for `R > 0`. -/
theorem abs_div_mul_cast (Q : ℕ) {R : ℕ} (hR : 0 < R) (m : ℤ) :
    |((Q : ℝ) * (m : ℝ)) / (R : ℝ)| = ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)| := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg Q), abs_of_nonneg hRpos.le]
  ring

/-- Finite-set lattice bound for the denominators `1 + min (|m h|) (|(m+1) h|)`. -/
theorem lattice_min_denom_finset_le (A : ℝ) (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h)
    (u : Finset ℤ) :
    ∑ m ∈ u, A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2
      ≤ 2 * A * h ^ 2 + 4 * A * h := by
  have hmin : ∀ m : ℤ, min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|
      = h * min |(m : ℝ)| |((m : ℝ) + 1)| := by
    intro m
    rw [abs_mul, abs_mul, abs_of_pos hh]
    rcases le_total |(m : ℝ)| |((m : ℝ) + 1)| with hle | hle
    · rw [min_eq_left (mul_le_mul_of_nonneg_right hle hh.le), min_eq_left hle, mul_comm]
    · rw [min_eq_right (mul_le_mul_of_nonneg_right hle hh.le), min_eq_right hle, mul_comm]
  have hd : ∀ m : ℤ, m ≠ -1 → |(m : ℝ)| / 2 ≤ min |(m : ℝ)| |((m : ℝ) + 1)| := by
    intro m hm
    rcases lt_or_ge m (-1) with hlt | hge
    · have hm2 : m ≤ -2 := by omega
      have hmr : (m : ℝ) ≤ -2 := by exact_mod_cast hm2
      have hn1 : ((m : ℝ) + 1) ≤ 0 := by linarith
      have hn2 : (m : ℝ) ≤ 0 := by linarith
      rw [min_eq_right, abs_of_nonpos hn2, abs_of_nonpos hn1]
      · linarith
      · rw [abs_of_nonpos hn2, abs_of_nonpos hn1]; linarith
    · have hm0 : (0 : ℤ) ≤ m := by omega
      have hmr : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      rw [min_eq_left, abs_of_nonneg hmr]
      · linarith
      · rw [abs_of_nonneg hmr, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)]
        linarith
  have hterm : ∀ m ∈ u, A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2
      ≤ (if m = -1 then A * h ^ 2 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2) := by
    intro m _
    rw [hmin m]
    by_cases hm : m = -1
    · rw [if_pos hm, hm]
      have hz : min |(((-1 : ℤ) : ℝ))| |(((-1 : ℤ) : ℝ) + 1)| = 0 := by norm_num
      rw [hz, mul_zero, add_zero, one_pow, div_one]
    · rw [if_neg hm]
      have hd' : |(m : ℝ)| / 2 ≤ min |(m : ℝ)| |((m : ℝ) + 1)| := hd m hm
      have hle : 1 + h * (|(m : ℝ)| / 2) ≤ 1 + h * min |(m : ℝ)| |((m : ℝ) + 1)| := by
        have := mul_le_mul_of_nonneg_left hd' hh.le
        linarith
      have hmn : (0 : ℝ) ≤ min |(m : ℝ)| |((m : ℝ) + 1)| :=
        le_min (abs_nonneg _) (abs_nonneg _)
      have hp1 : 0 < 1 + h * (|(m : ℝ)| / 2) := by positivity
      have hp2 : 0 < 1 + h * min |(m : ℝ)| |((m : ℝ) + 1)| := by nlinarith
      have hsq : (1 + h * (|(m : ℝ)| / 2)) ^ 2
          ≤ (1 + h * min |(m : ℝ)| |((m : ℝ) + 1)|) ^ 2 :=
        pow_le_pow_left₀ hp1.le hle 2
      have h1 : A * h ^ 2 / (1 + h * min |(m : ℝ)| |((m : ℝ) + 1)|) ^ 2
          ≤ A * h ^ 2 / (1 + h * (|(m : ℝ)| / 2)) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hp1 2) hsq
      have h2 : (1 + (h / 2) * |(m : ℝ)|) = (1 + h * (|(m : ℝ)| / 2)) := by ring
      rw [h2]
      exact h1
  have hsum1 : ∑ m ∈ u, (if m = -1 then A * h ^ 2 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2)
      ≤ A * h ^ 2 + ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 := by
    have hsplit : ∀ m : ℤ, (if m = -1 then A * h ^ 2 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2)
        = (if m = -1 then A * h ^ 2 else 0)
          + (if m = -1 then 0 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2) := by
      intro m; by_cases hm : m = -1 <;> simp [hm]
    have hnn : 0 ≤ A * h ^ 2 := mul_nonneg hA (sq_nonneg h)
    calc ∑ m ∈ u, (if m = -1 then A * h ^ 2 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2)
        = ∑ m ∈ u, ((if m = -1 then A * h ^ 2 else 0)
            + (if m = -1 then 0 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2)) :=
          Finset.sum_congr rfl (fun m _ => hsplit m)
      _ = (∑ m ∈ u, (if m = -1 then A * h ^ 2 else 0))
            + ∑ m ∈ u, (if m = -1 then 0 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2) :=
          Finset.sum_add_distrib
      _ ≤ A * h ^ 2 + ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 := by
          have h3 : (∑ m ∈ u, (if m = -1 then A * h ^ 2 else 0)) ≤ A * h ^ 2 := by
            rw [Finset.sum_ite_eq' u (-1) (fun _ => A * h ^ 2)]
            by_cases hmem : (-1 : ℤ) ∈ u <;> simp [hmem, hnn]
          have h4 : (∑ m ∈ u, (if m = -1 then 0 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2))
              ≤ ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            have hX : 0 ≤ A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 :=
              div_nonneg (mul_nonneg hA (sq_nonneg h)) (by positivity)
            by_cases hm : m = -1
            · rw [if_pos hm]; exact hX
            · rw [if_neg hm]
          linarith
  have hG : ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 ≤ A * h ^ 2 * (1 + 4 / h) := by
    have hb := (sum_inv_sq_linear_int_le 1 (h / 2) one_pos (half_pos hh)).1 u
    have hb' : ∑ m ∈ u, 1 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 ≤ 1 + 4 / h := by
      have hc : (1 : ℝ) / 1 ^ 2 + 2 / ((h / 2) * 1) = 1 + 4 / h := by ring
      linarith [hb]
    have hnn : 0 ≤ A * h ^ 2 := mul_nonneg hA (sq_nonneg h)
    have hEq : ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2
        = A * h ^ 2 * ∑ m ∈ u, 1 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [mul_one_div])
    rw [hEq]
    exact mul_le_mul_of_nonneg_left hb' hnn
  have hfin : A * h ^ 2 * (1 + 4 / h) = A * h ^ 2 + 4 * A * h := by field_simp
  calc ∑ m ∈ u, A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2
      ≤ ∑ m ∈ u, (if m = -1 then A * h ^ 2 else A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2) :=
        Finset.sum_le_sum hterm
    _ ≤ A * h ^ 2 + ∑ m ∈ u, A * h ^ 2 / (1 + (h / 2) * |(m : ℝ)|) ^ 2 := hsum1
    _ ≤ A * h ^ 2 + A * h ^ 2 * (1 + 4 / h) := by linarith [hG]
    _ = 2 * A * h ^ 2 + 4 * A * h := by rw [hfin]; ring

theorem lattice_min_denom_tsum_le (A : ℝ) (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) :
    ∑' m : ℤ, A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2
      ≤ 2 * A * h ^ 2 + 4 * A * h :=
  Real.tsum_le_of_sum_le (fun m => by positivity) (lattice_min_denom_finset_le A hA hh)

theorem lattice_min_denom_summable (A : ℝ) (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) :
    Summable (fun m : ℤ => A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2) :=
  summable_of_sum_le (fun m => by positivity) (lattice_min_denom_finset_le A hA hh)

/-- Cell oscillation bound: the difference between `h * F (m h)` and the integral of `F` over
the `m`-th cell is at most `A h² / (1 + min |m h| |(m+1) h|)²`. -/
theorem abs_intervalIntegral_cell_sub_const (F : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ t s : ℝ, |F t - F s| ≤ A / (1 + min |t| |s|) ^ 2 * |t - s|)
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    |∫ t in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), (F ((m : ℝ) * h) - F t)|
      ≤ A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 := by
  have hab : (m : ℝ) * h ≤ ((m : ℝ) + 1) * h := by nlinarith [hh]
  have hba : ((m : ℝ) + 1) * h - (m : ℝ) * h = h := by ring
  have hcell : ∀ t ∈ Set.uIoc ((m : ℝ) * h) (((m : ℝ) + 1) * h),
      |F ((m : ℝ) * h) - F t|
        ≤ A * h / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have hat : |(m : ℝ) * h - t| ≤ h := by
      rw [abs_of_nonpos (by linarith [ht.1] : (m : ℝ) * h - t ≤ 0)]
      linarith [ht.2, hba]
    have hkey : min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)| ≤ min |(m : ℝ) * h| |t| := by
      refine le_min (min_le_left _ _) ?_
      have ht' : t ≤ ((m : ℝ) + 1) * h := ht.2
      have ht'' : (m : ℝ) * h ≤ t := le_of_lt ht.1
      rcases lt_or_ge ((m : ℝ)) 0 with hm0 | hm0
      · have hmint : m < 0 := by exact_mod_cast hm0
        have hmle : m ≤ -1 := by omega
        have h1 : ((m : ℝ) + 1) ≤ 0 := by
          have : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
          linarith
        have hb0 : ((m : ℝ) + 1) * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hh.le
        have ht0 : t ≤ 0 := le_trans ht' hb0
        calc min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)| ≤ |(((m : ℝ) + 1) * h)| := min_le_right _ _
          _ = -(((m : ℝ) + 1) * h) := abs_of_nonpos hb0
          _ ≤ -t := by linarith [ht']
          _ = |t| := (abs_of_nonpos ht0).symm
      · have ha0 : 0 ≤ (m : ℝ) * h := mul_nonneg hm0 hh.le
        have ht0 : 0 ≤ t := le_trans ha0 ht''
        calc min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)| ≤ |(m : ℝ) * h| := min_le_left _ _
          _ = (m : ℝ) * h := abs_of_nonneg ha0
          _ ≤ t := ht''
          _ = |t| := (abs_of_nonneg ht0).symm
    have hden : 1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)| ≤ 1 + min |(m : ℝ) * h| |t| := by
      linarith
    have hp1 : 0 < 1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)| := by
      have := le_min (abs_nonneg ((m : ℝ) * h)) (abs_nonneg (((m : ℝ) + 1) * h))
      linarith
    have hp2 : 0 < 1 + min |(m : ℝ) * h| |t| := by
      have := le_min (abs_nonneg ((m : ℝ) * h)) (abs_nonneg t)
      linarith
    have hsq : (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2
        ≤ (1 + min |(m : ℝ) * h| |t|) ^ 2 := pow_le_pow_left₀ hp1.le hden 2
    have hdiv : A / (1 + min |(m : ℝ) * h| |t|) ^ 2
        ≤ A / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 :=
      div_le_div_of_nonneg_left hA (pow_pos hp1 2) hsq
    calc |F ((m : ℝ) * h) - F t| ≤ A / (1 + min |(m : ℝ) * h| |t|) ^ 2 * |(m : ℝ) * h - t| :=
          hF _ _
      _ ≤ A / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 * h := by
          refine mul_le_mul hdiv hat (abs_nonneg _) ?_
          positivity
      _ = A * h / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 := by ring
  calc |∫ t in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), (F ((m : ℝ) * h) - F t)|
      = ‖∫ t in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), (F ((m : ℝ) * h) - F t)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (A * h / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2)
          * |(((m : ℝ) + 1) * h) - (m : ℝ) * h| :=
        norm_integral_le_of_norm_le_const hcell
    _ = A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 := by
        rw [hba, abs_of_pos hh]; ring

/-- The lattice Riemann-sum bound: for `F` decaying like `A/(1+|t|)^2` and satisfying the
`min`-Lipschitz bound, the Riemann sum `h ∑_m F (m h)` approximates `∫ F` within `O(A h)`. -/
theorem riemannSum_lattice_bound (F : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hFbd : ∀ t : ℝ, |F t| ≤ A / (1 + |t|) ^ 2)
    (hFlip : ∀ t s : ℝ, |F t - F s| ≤ A / (1 + min |t| |s|) ^ 2 * |t - s|)
    {h : ℝ} (hh : 0 < h) :
    |h * ∑' m : ℤ, F ((m : ℝ) * h) - ∫ t, F t| ≤ 2 * A * h ^ 2 + 4 * A * h := by
  have hcont : Continuous F := continuous_of_min_lipschitz hA hFlip
  have hFint : Integrable F := integrable_of_decay hA hcont.aestronglyMeasurable hFbd
  have hsumm_lat : Summable (fun m : ℤ => F ((m : ℝ) * h)) := by
    refine Summable.of_norm_bounded (summable_lattice_inv_sq A hA hh) (fun m => ?_)
    rw [Real.norm_eq_abs]
    calc |F ((m : ℝ) * h)| ≤ A / (1 + |(m : ℝ) * h|) ^ 2 := hFbd _
      _ = A / (1 + h * |(m : ℝ)|) ^ 2 := by rw [abs_mul, abs_of_pos hh]; ring
  have htil : HasSum (fun m : ℤ => ∫ x in ((m : ℝ) * h + 0)..((m : ℝ) * h + 0 + h), F x)
      (∫ x, F x) := latticeSum_tiling F hFint (c := 0) (h := h) hh
  have hcellsum : HasSum (fun m : ℤ => ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x)
      (∫ x, F x) := by
    have hfun : (fun m : ℤ => ∫ x in ((m : ℝ) * h + 0)..((m : ℝ) * h + 0 + h), F x)
        = (fun m : ℤ => ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x) := by
      funext m
      rw [show (m : ℝ) * h + 0 = (m : ℝ) * h by ring,
        show (m : ℝ) * h + h = ((m : ℝ) + 1) * h by ring]
    simpa only [← hfun] using htil
  have h1 : HasSum (fun m : ℤ => h * F ((m : ℝ) * h)) (h * ∑' m : ℤ, F ((m : ℝ) * h)) :=
    hsumm_lat.hasSum.mul_left h
  have h2 : HasSum (fun m : ℤ =>
      h * F ((m : ℝ) * h) - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x)
      (h * (∑' m : ℤ, F ((m : ℝ) * h)) - ∫ x, F x) := h1.sub hcellsum
  have hpt : ∀ m : ℤ, ‖h * F ((m : ℝ) * h) - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x‖
      ≤ A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 := by
    intro m
    rw [Real.norm_eq_abs]
    have hcancel : ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), (F ((m : ℝ) * h) - F x)
        = h * F ((m : ℝ) * h) - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hFint.intervalIntegrable,
        intervalIntegral.integral_const, smul_eq_mul,
        show ((m : ℝ) + 1) * h - (m : ℝ) * h = h by ring]
    rw [← hcancel]
    exact abs_intervalIntegral_cell_sub_const F A hA hFlip hh m
  have hsumm_norm : Summable (fun m : ℤ =>
      ‖h * F ((m : ℝ) * h) - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hpt (lattice_min_denom_summable A hA hh)
  calc |h * ∑' m : ℤ, F ((m : ℝ) * h) - ∫ t, F t|
      = ‖h * ∑' m : ℤ, F ((m : ℝ) * h) - ∫ t, F t‖ := by rw [Real.norm_eq_abs]
    _ = ‖∑' m : ℤ, (h * F ((m : ℝ) * h)
          - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x)‖ := by
        rw [h2.tsum_eq]
    _ ≤ ∑' m : ℤ, ‖h * F ((m : ℝ) * h)
          - ∫ x in ((m : ℝ) * h)..(((m : ℝ) + 1) * h), F x‖ :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' m : ℤ, A * h ^ 2 / (1 + min |(m : ℝ) * h| |(((m : ℝ) + 1) * h)|) ^ 2 :=
        Summable.tsum_le_tsum hpt hsumm_norm (lattice_min_denom_summable A hA hh)
    _ ≤ 2 * A * h ^ 2 + 4 * A * h := lattice_min_denom_tsum_le A hA hh

theorem riemannSum_limit_engine
    (Q : ℕ) (hQ : 0 < Q) (Φ : ℕ → ℝ → ℂ) (Ψ : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hΦ : ∀ R t, ‖Φ R t‖ ≤ A / (1 + |t|) ^ 2)
    (hΨ : ∀ t, |Ψ t| ≤ A / (1 + |t|) ^ 2)
    (hΨlip : ∀ t s, |Ψ t - Ψ s| ≤ A / (1 + min |t| |s|) ^ 2 * |t - s|)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℝ, |‖Φ R t‖ - Ψ t| ≤ ε) :
    Filter.Tendsto (fun R : ℕ => ∑' m : ℤ,
        ENNReal.ofReal ((R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖))
      Filter.atTop (nhds (ENNReal.ofReal ((Q : ℝ)⁻¹ * ∫ t, Ψ t))) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hcmp : Tendsto (fun R : ℕ => ∑' m : ℤ,
      (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
        - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|) atTop (nhds 0) :=
    riemannSum_uniform_compare Q hQ Φ Ψ A hA hΦ hΨ hconv
  have hquad : Tendsto (fun R : ℕ => (Q : ℝ)⁻¹ *
      (2 * A * ((Q : ℝ) / (R : ℝ)) ^ 2 + 4 * A * ((Q : ℝ) / (R : ℝ)))) atTop (nhds 0) := by
    have h1 : Tendsto (fun R : ℕ => (Q : ℝ) / (R : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (Q : ℝ)
    have h2 : Tendsto (fun R : ℕ => 2 * A * ((Q : ℝ) / (R : ℝ)) ^ 2
        + 4 * A * ((Q : ℝ) / (R : ℝ))) atTop (nhds 0) := by
      have hh := ((h1.pow 2).const_mul (2 * A)).add (h1.const_mul (4 * A))
      simpa using hh
    simpa using h2.const_mul ((Q : ℝ)⁻¹)
  have hsumm_lat : ∀ {R : ℕ}, 1 ≤ R → ∀ {g : ℝ → ℝ},
      (∀ t : ℝ, |g t| ≤ A / (1 + |t|) ^ 2) →
      Summable (fun m : ℤ => (R : ℝ)⁻¹ * g (((Q : ℝ) * (m : ℝ)) / (R : ℝ))) := by
    intro R hR g hg
    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
    have hcpos : 0 < (Q : ℝ) / (R : ℝ) := div_pos hQpos hRpos
    refine Summable.of_norm_bounded
      (summable_lattice_inv_sq (A * (R : ℝ)⁻¹) (by positivity) hcpos) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hRpos.le)]
    calc (R : ℝ)⁻¹ * |g (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|
        ≤ (R : ℝ)⁻¹ * (A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hg _) (inv_nonneg.mpr hRpos.le)
      _ = A * (R : ℝ)⁻¹ / (1 + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2 := by
          rw [abs_div_mul_cast Q (lt_of_lt_of_le Nat.zero_lt_one hR) m]
          ring
  have hkey : ∀ R : ℕ, 1 ≤ R →
      |(∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
        - (Q : ℝ)⁻¹ * ∫ t, Ψ t|
      ≤ (∑' m : ℤ, (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
            - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|)
        + (Q : ℝ)⁻¹
            * (2 * A * ((Q : ℝ) / (R : ℝ)) ^ 2 + 4 * A * ((Q : ℝ) / (R : ℝ))) := by
    intro R hR
    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
    have hRinv : 0 ≤ (R : ℝ)⁻¹ := inv_nonneg.mpr hRpos.le
    have hsA : Summable (fun m : ℤ => (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖) :=
      hsumm_lat hR (g := fun t => ‖Φ R t‖) (fun t => by
        rw [abs_of_nonneg (norm_nonneg _)]; exact hΦ R t)
    have hsB : Summable (fun m : ℤ => (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))) :=
      hsumm_lat hR (g := Ψ) hΨ
    have hmaj : Summable (fun m : ℤ =>
        (R : ℝ)⁻¹ * (2 * A) / (1 + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2) := by
      refine (summable_lattice_inv_sq (2 * A * (R : ℝ)⁻¹) (by positivity)
        (div_pos hQpos hRpos)).congr (fun m => ?_)
      ring
    have h1 : |(∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
        - (∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))|
        ≤ (∑' m : ℤ, (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
            - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|) := by
      have hdec : (∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
          - (∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
          = ∑' m : ℤ, (R : ℝ)⁻¹
              * (‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))) :=
        (Summable.tsum_sub hsA hsB).symm.trans (tsum_congr (fun m => by ring))
      have hsn : Summable (fun m : ℤ => ‖(R : ℝ)⁻¹
          * (‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))‖) := by
        refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRinv]
        have htri : |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
            - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|
            ≤ 2 * A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2 := by
          calc |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
                - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|
              ≤ |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖|
                + |Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))| := abs_sub _ _
            _ = ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
                + |Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))| := by
                rw [abs_of_nonneg (norm_nonneg _)]
            _ ≤ A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2
                + A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2 :=
                add_le_add (hΦ R _) (hΨ _)
            _ = 2 * A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2 := by ring
        calc (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
              - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|
            ≤ (R : ℝ)⁻¹ * (2 * A / (1 + |((Q : ℝ) * (m : ℝ)) / (R : ℝ)|) ^ 2) :=
              mul_le_mul_of_nonneg_left htri hRinv
          _ = (R : ℝ)⁻¹ * (2 * A) / (1 + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2 := by
              rw [abs_div_mul_cast Q (lt_of_lt_of_le Nat.zero_lt_one hR) m]
              ring
      rw [hdec]
      calc |∑' m : ℤ, (R : ℝ)⁻¹
              * (‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))|
          = ‖∑' m : ℤ, (R : ℝ)⁻¹
              * (‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∑' m : ℤ, ‖(R : ℝ)⁻¹
              * (‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))‖ :=
            norm_tsum_le_tsum_norm hsn
        _ = ∑' m : ℤ, (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
              - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))| :=
            tsum_congr (fun m => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRinv])
    have hSB_eq : (∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
        - (Q : ℝ)⁻¹ * ∫ t, Ψ t
        = (Q : ℝ)⁻¹ * (((Q : ℝ) / (R : ℝ))
            * (∑' m : ℤ, Ψ ((m : ℝ) * ((Q : ℝ) / (R : ℝ)))) - ∫ t, Ψ t) := by
      have hpt : ∀ m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))
          = ((Q : ℝ)⁻¹ * ((Q : ℝ) / (R : ℝ))) * Ψ ((m : ℝ) * ((Q : ℝ) / (R : ℝ))) := by
        intro m
        have hx : ((Q : ℝ) * (m : ℝ)) / (R : ℝ) = (m : ℝ) * ((Q : ℝ) / (R : ℝ)) := by ring
        have hcoef : (R : ℝ)⁻¹ = (Q : ℝ)⁻¹ * ((Q : ℝ) / (R : ℝ)) := by
          field_simp
        rw [hx, hcoef]
      rw [tsum_congr hpt, tsum_mul_left]
      ring
    have h2 : |(∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
        - (Q : ℝ)⁻¹ * ∫ t, Ψ t|
        ≤ (Q : ℝ)⁻¹
            * (2 * A * ((Q : ℝ) / (R : ℝ)) ^ 2 + 4 * A * ((Q : ℝ) / (R : ℝ))) := by
      rw [hSB_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hQpos.le)]
      exact mul_le_mul_of_nonneg_left
        (riemannSum_lattice_bound Ψ A hA hΨ hΨlip (h := (Q : ℝ) / (R : ℝ))
          (div_pos hQpos hRpos))
        (inv_nonneg.mpr hQpos.le)
    calc |(∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
          - (Q : ℝ)⁻¹ * ∫ t, Ψ t|
        = |((∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
              - (∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))))
            + ((∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
              - (Q : ℝ)⁻¹ * ∫ t, Ψ t)| := by ring_nf
      _ ≤ |(∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
              - (∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))|
            + |(∑' m : ℤ, (R : ℝ)⁻¹ * Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
              - (Q : ℝ)⁻¹ * ∫ t, Ψ t| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  have hlim : Tendsto (fun R : ℕ => ∑' m : ℤ,
      (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖) atTop
      (nhds ((Q : ℝ)⁻¹ * ∫ t, Ψ t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hsq := squeeze_zero'
      (f := fun R : ℕ => |(∑' m : ℤ, (R : ℝ)⁻¹ * ‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)
        - (Q : ℝ)⁻¹ * ∫ t, Ψ t|)
      (g := fun R : ℕ => (∑' m : ℤ, (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖
            - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|)
        + (Q : ℝ)⁻¹
            * (2 * A * ((Q : ℝ) / (R : ℝ)) ^ 2 + 4 * A * ((Q : ℝ) / (R : ℝ))))
      (eventually_atTop.mpr ⟨1, fun R _ => abs_nonneg _⟩)
      (eventually_atTop.mpr ⟨1, fun R hR => hkey R hR⟩)
      (by simpa using hcmp.add hquad)
    simpa [Real.dist_eq] using hsq
  refine Tendsto.congr' ?_ ((ENNReal.continuous_ofReal.tendsto _).comp hlim)
  filter_upwards [eventually_atTop.mpr ⟨1, fun R hR => hR⟩] with R hR
  refine ENNReal.ofReal_tsum_of_nonneg (fun m => ?_) ?_
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg R)) (norm_nonneg _)
  · exact hsumm_lat hR (g := fun t => ‖Φ R t‖) (fun t => by
      rw [abs_of_nonneg (norm_nonneg _)]; exact hΦ R t)

end

end Work.KMTPlan.A6
