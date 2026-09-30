import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_lipschitz
import Submission.Work.BMF.halasz_mertens_aux
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp
import Submission.Work.BMF.HL.sum_log_div_prime_le
import Submission.Work.BMF.mrlas.halasz_crossover
import Submission.Work.BMF.mrlas.Wsup_measurable
import Submission.Work.BMF.mrlas.halasz_intM
import Submission.Work.BMF.mrlas.casdiv_majm
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "majm" bound of Ramaré's proof of Halász's theorem

`‖Σ_{n ≤ x} f n‖ ≤ C x ((1 + m) e^{-m} + 1/√T + 1/log x)`, `m = mHal f x (2T)`.

This assembles the estimate from its two halves:

* `Work.BMF.mrlas.casdiv_majm` (Ramaré's Proposition `casdiv` with `r ≡ 1`): the "long average"
  reduction `‖Mf f x‖ ≤ C (x/log x) (∫_{1/(2log x)}^1 exp (Wsup f x α (T+1)) dα/α + e^Z/√T + e^Z/log x)`;
* the two pointwise bounds for `Wsup` (`wsup_mHal_bound`, `wsup_log_bound`), which turn the
  α-integral — via the elementary `crossover_sharp` — into `e^Z (1+m) e^{-m}`;
* Mertens' theorem, which gives `e^Z ≤ C log x`.
-/

namespace Work.BMF.mrlas

open Finset Real MeasureTheory
open scoped BigOperators

/-! ## Mertens: `exp (Zrcp x) ≤ C log x` -/

/-- `exp (Zrcp x) ≤ C log x` for `x ≥ 3` (Mertens' theorem; the constant is absolute). -/
lemma exp_Zrcp_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → Real.exp (Work.BMF.Zrcp x) ≤ C * Real.log x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hC₀' : ∀ y : ℝ, 11 ≤ y → Work.BMF.Zrcp y ≤ Real.log (Real.log y) + C₀ := by
    intro y hy
    have h := hC₀ y hy
    rw [abs_le] at h
    have h2 : (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log y) ≤ C₀ := h.2
    simp only [Work.BMF.Zrcp]
    linarith
  refine ⟨max (Real.exp C₀) (Real.exp (Work.BMF.Zrcp 11) / Real.log 3), ?_, ?_⟩
  · refine lt_max_of_lt_left (Real.exp_pos C₀)
  intro x hx3
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  rcases le_or_gt 11 x with h11 | h11
  · have hZ : Work.BMF.Zrcp x ≤ Real.log (Real.log x) + C₀ := hC₀' x h11
    have hexp : Real.exp (Work.BMF.Zrcp x) ≤ Real.exp C₀ * Real.log x := by
      calc Real.exp (Work.BMF.Zrcp x) ≤ Real.exp (Real.log (Real.log x) + C₀) :=
            Real.exp_le_exp.mpr hZ
        _ = Real.exp C₀ * Real.log x := by rw [Real.exp_add, Real.exp_log hlogx, mul_comm]
    calc Real.exp (Work.BMF.Zrcp x) ≤ Real.exp C₀ * Real.log x := hexp
      _ ≤ max (Real.exp C₀) (Real.exp (Work.BMF.Zrcp 11) / Real.log 3) * Real.log x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogx.le
  · have hmono : Work.BMF.Zrcp x ≤ Work.BMF.Zrcp 11 :=
      Work.BMF.Zrcp_mono (le_of_lt h11)
    have hexp : Real.exp (Work.BMF.Zrcp x) ≤ Real.exp (Work.BMF.Zrcp 11) :=
      Real.exp_le_exp.mpr hmono
    have h2 : Real.exp (Work.BMF.Zrcp 11) ≤
        Real.exp (Work.BMF.Zrcp 11) / Real.log 3 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
      nlinarith [Real.exp_pos (Work.BMF.Zrcp 11), hlogx3]
    calc Real.exp (Work.BMF.Zrcp x) ≤ Real.exp (Work.BMF.Zrcp 11) := hexp
      _ ≤ Real.exp (Work.BMF.Zrcp 11) / Real.log 3 * Real.log x := h2
      _ ≤ max (Real.exp C₀) (Real.exp (Work.BMF.Zrcp 11) / Real.log 3) * Real.log x :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogx.le

/-! ## The sharp crossover integral -/

/-- **Sharp crossover.** If `g α ≤ Z - m + C₁` and `g α ≤ Z - log (α L) + C₁` for all
`α ∈ [1/(2L), 1]` (with `1 ≤ L`, `0 ≤ m`, `0 ≤ C₁`), then

`∫_{1/(2L)}^{1} exp (g α) / α dα ≤ (1 + log 2) · exp (Z + C₁) · (1 + m) e^{-m}`.

The first hypothesis is the sharp one for small `α` (where `α L ≤ e^m`), the second for large `α`;
the crossover point is `α₀ = e^m / L`. -/
theorem crossover_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ) (L Z m C₁ : ℝ), 1 ≤ L → 0 ≤ m → 0 ≤ C₁ →
      IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume (1 / (2 * L)) 1 →
      (∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 → g α ≤ Z - m + C₁) →
      (∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 → g α ≤ Z - Real.log (α * L) + C₁) →
      (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α) ≤
        C * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by
  refine ⟨1 + Real.log 2, by positivity, ?_⟩
  intro g L Z m C₁ hL hm hC₁ hInt h1 h2
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have ha_pos : 0 < 1 / (2 * L) := by positivity
  have ha_le_one : 1 / (2 * L) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * L)]; linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- the two pointwise bounds, in the normalised form used below
  have key1 : ∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 →
      Real.exp (g α) / α ≤ Real.exp (Z + C₁) * Real.exp (-m) * (1 / α) := by
    intro α hα1 hα2
    have hαpos : 0 < α := lt_of_lt_of_le ha_pos hα1
    have hg := h1 α hα1 hα2
    have hrew : Real.exp (Z - m + C₁) = Real.exp (Z + C₁) * Real.exp (-m) := by
      rw [show Z - m + C₁ = (Z + C₁) + (-m) by ring, Real.exp_add]
    calc Real.exp (g α) / α ≤ Real.exp (Z - m + C₁) / α :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hg) hαpos.le
      _ = Real.exp (Z + C₁) * Real.exp (-m) * (1 / α) := by rw [hrew]; ring
  have key2 : ∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 →
      Real.exp (g α) / α ≤ (Real.exp (Z + C₁) / L) / α ^ 2 := by
    intro α hα1 hα2
    have hαpos : 0 < α := lt_of_lt_of_le ha_pos hα1
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hg := h2 α hα1 hα2
    have harg : 0 < α * L := mul_pos hαpos hLpos
    have h4 : Real.exp (Z - Real.log (α * L) + C₁) = Real.exp (Z + C₁) * (α * L)⁻¹ := by
      rw [show Z - Real.log (α * L) + C₁ = Z + C₁ + -(Real.log (α * L)) by ring, Real.exp_add,
        Real.exp_neg, Real.exp_log harg]
    calc Real.exp (g α) / α ≤ Real.exp (Z - Real.log (α * L) + C₁) / α :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hg) hαpos.le
      _ = (Real.exp (Z + C₁) / L) / α ^ 2 := by
          rw [h4, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv, ← inv_pow]
          ring
  -- the two elementary integrals
  have int1 : ∀ u v : ℝ, 0 < u → u ≤ v →
      (∫ α in u..v, Real.exp (Z + C₁) * Real.exp (-m) * (1 / α))
        = Real.exp (Z + C₁) * Real.exp (-m) * Real.log (v / u) := by
    intro u v hu huv
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hu (lt_of_lt_of_le hu huv)]
  have int2 : ∀ u v : ℝ, 0 < u → u ≤ v →
      (∫ α in u..v, (Real.exp (Z + C₁) / L) / α ^ 2)
        = Real.exp (Z + C₁) / L * (1 / u - 1 / v) := by
    intro u v hu huv
    exact integral_div_sq (Real.exp (Z + C₁) / L) u v hu huv
  -- the final comparison, batch 1: `e^{-m} (m + log 2) ≤ (1 + log 2) (1+m) e^{-m}`
  have hkey1 : Real.exp (-m) * (m + Real.log 2) ≤ (1 + Real.log 2) * ((1 + m) * Real.exp (-m)) := by
    have h1' : m + Real.log 2 ≤ (1 + Real.log 2) * (1 + m) := by nlinarith
    calc Real.exp (-m) * (m + Real.log 2) ≤ Real.exp (-m) * ((1 + Real.log 2) * (1 + m)) :=
          mul_le_mul_of_nonneg_left h1' (Real.exp_pos _).le
      _ = (1 + Real.log 2) * ((1 + m) * Real.exp (-m)) := by ring
  -- batch 2: `e^{-m} (m + log 2 + 1) ≤ (1 + log 2) (1+m) e^{-m}`
  have hkey2 : Real.exp (-m) * (m + Real.log 2 + 1) ≤ (1 + Real.log 2) * ((1 + m) * Real.exp (-m)) := by
    have h1' : m + Real.log 2 + 1 ≤ (1 + Real.log 2) * (1 + m) := by nlinarith
    calc Real.exp (-m) * (m + Real.log 2 + 1) ≤ Real.exp (-m) * ((1 + Real.log 2) * (1 + m)) :=
          mul_le_mul_of_nonneg_left h1' (Real.exp_pos _).le
      _ = (1 + Real.log 2) * ((1 + m) * Real.exp (-m)) := by ring
  by_cases hcase : L ≤ Real.exp m
  · -- the sharp hypothesis suffices on the whole range
    have hlogL : Real.log L ≤ m := by
      have h := Real.log_le_log hLpos hcase
      rwa [Real.log_exp] at h
    have hcont : ContinuousOn (fun α : ℝ => Real.exp (Z + C₁) * Real.exp (-m) * (1 / α))
        (Set.uIcc (1 / (2 * L)) 1) := by
      rw [Set.uIcc_of_le ha_le_one]
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id ?_)
      intro α hα
      exact ne_of_gt (lt_of_lt_of_le ha_pos hα.1)
    have hstep : (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
        ≤ Real.exp (Z + C₁) * Real.exp (-m) * Real.log (1 / (1 / (2 * L))) := by
      calc (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
          ≤ ∫ α in (1 / (2 * L))..1, Real.exp (Z + C₁) * Real.exp (-m) * (1 / α) :=
            intervalIntegral.integral_mono_on ha_le_one hInt
              (ContinuousOn.intervalIntegrable hcont) (fun α hα => key1 α hα.1 hα.2)
        _ = _ := int1 _ _ ha_pos ha_le_one
    have harg : (1 : ℝ) / (1 / (2 * L)) = 2 * L := by rw [one_div_one_div]
    have hlog2L : Real.log (2 * L) ≤ m + Real.log 2 := by
      rw [Real.log_mul (by norm_num) hLne]
      linarith
    have hmain : (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
        ≤ Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) := by
      rw [harg] at hstep
      calc (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
          ≤ Real.exp (Z + C₁) * Real.exp (-m) * Real.log (2 * L) := hstep
        _ ≤ Real.exp (Z + C₁) * Real.exp (-m) * (m + Real.log 2) :=
            mul_le_mul_of_nonneg_left hlog2L (by positivity)
        _ = Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) := by ring
    calc (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
        ≤ Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) := hmain
      _ ≤ Real.exp (Z + C₁) * ((1 + Real.log 2) * ((1 + m) * Real.exp (-m))) :=
          mul_le_mul_of_nonneg_left hkey1 (Real.exp_pos _).le
      _ = (1 + Real.log 2) * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by ring
  · -- `exp m < L`: split at `α₀ = exp m / L`
    push_neg at hcase
    set α₀ : ℝ := Real.exp m / L with hα₀def
    have hα₀pos : 0 < α₀ := div_pos (Real.exp_pos m) hLpos
    have hα₀lt1 : α₀ < 1 := by
      rw [hα₀def, div_lt_one hLpos]; exact hcase
    have hα₀le1 : α₀ ≤ 1 := le_of_lt hα₀lt1
    have ha_le : 1 / (2 * L) ≤ α₀ := by
      have hhalf : ((1 : ℝ) / 2) ≤ Real.exp m := by
        have h := Real.one_le_exp hm
        linarith
      rw [show (1 : ℝ) / (2 * L) = ((1 : ℝ) / 2) / L by ring, hα₀def,
        div_le_div_iff_of_pos_right hLpos]
      exact hhalf
    have hI1 : IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume
        (1 / (2 * L)) α₀ :=
      hInt.mono_set (by
        rw [Set.uIcc_of_le ha_le, Set.uIcc_of_le ha_le_one]
        exact Set.Icc_subset_Icc_right hα₀le1)
    have hI2 : IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume α₀ 1 :=
      hInt.mono_set (by
        rw [Set.uIcc_of_le hα₀le1, Set.uIcc_of_le ha_le_one]
        exact Set.Icc_subset_Icc_left ha_le)
    have hsplit : (∫ α in (1 / (2 * L))..1, Real.exp (g α) / α)
        = (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α) + ∫ α in α₀..1, Real.exp (g α) / α :=
      (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
    -- first piece
    have hcont1' : ContinuousOn (fun α : ℝ => Real.exp (Z + C₁) * Real.exp (-m) * (1 / α))
        (Set.uIcc (1 / (2 * L)) α₀) := by
      rw [Set.uIcc_of_le ha_le]
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id ?_)
      intro α hα
      exact ne_of_gt (lt_of_lt_of_le ha_pos hα.1)
    have harg1 : α₀ / (1 / (2 * L)) = 2 * Real.exp m := by
      rw [hα₀def]
      field_simp
    have hp1 : (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α)
        ≤ Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) := by
      have hstep : (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α)
          ≤ Real.exp (Z + C₁) * Real.exp (-m) * Real.log (α₀ / (1 / (2 * L))) := by
        calc (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α)
            ≤ ∫ α in (1 / (2 * L))..α₀, Real.exp (Z + C₁) * Real.exp (-m) * (1 / α) :=
              intervalIntegral.integral_mono_on ha_le hI1 (ContinuousOn.intervalIntegrable hcont1')
                (fun α hα => key1 α hα.1 (le_trans hα.2 hα₀le1))
          _ = Real.exp (Z + C₁) * Real.exp (-m) * Real.log (α₀ / (1 / (2 * L))) :=
              int1 _ _ ha_pos ha_le
      rw [harg1, Real.log_mul (by norm_num) (Real.exp_ne_zero m), Real.log_exp] at hstep
      calc (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α)
          ≤ Real.exp (Z + C₁) * Real.exp (-m) * (Real.log 2 + m) := hstep
        _ = Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) := by ring
    -- second piece
    have hcont2 : ContinuousOn (fun α : ℝ => (Real.exp (Z + C₁) / L) / α ^ 2)
        (Set.uIcc α₀ 1) := by
      rw [Set.uIcc_of_le hα₀le1]
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro α hα
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hα₀pos hα.1))
    have hinv : 1 / α₀ = L * Real.exp (-m) := by
      rw [hα₀def, one_div, inv_div, div_eq_mul_inv, ← Real.exp_neg]
    have hp2 : (∫ α in α₀..1, Real.exp (g α) / α) ≤ Real.exp (Z + C₁) * Real.exp (-m) := by
      have hstep : (∫ α in α₀..1, Real.exp (g α) / α)
          ≤ Real.exp (Z + C₁) / L * (1 / α₀ - 1) := by
        calc (∫ α in α₀..1, Real.exp (g α) / α)
            ≤ ∫ α in α₀..1, (Real.exp (Z + C₁) / L) / α ^ 2 :=
              intervalIntegral.integral_mono_on hα₀le1 hI2
                (ContinuousOn.intervalIntegrable hcont2)
                (fun α hα => key2 α (le_trans ha_le hα.1) hα.2)
          _ = Real.exp (Z + C₁) / L * (1 / α₀ - 1) := by
              simpa using int2 α₀ 1 hα₀pos hα₀le1
      have hb : (1 : ℝ) / α₀ - 1 ≤ L * Real.exp (-m) := by
        rw [hinv]
        have : (0 : ℝ) ≤ L * Real.exp (-m) := by positivity
        linarith
      have hb' : Real.exp (Z + C₁) / L * (1 / α₀ - 1) ≤ Real.exp (Z + C₁) * Real.exp (-m) := by
        calc Real.exp (Z + C₁) / L * (1 / α₀ - 1)
            ≤ Real.exp (Z + C₁) / L * (L * Real.exp (-m)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = Real.exp (Z + C₁) * Real.exp (-m) := by
              field_simp <;> ring
      linarith [hstep, hb']
    have htot : (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α) + ∫ α in α₀..1, Real.exp (g α) / α
        ≤ Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2 + 1)) := by
      have h := add_le_add hp1 hp2
      have heq : Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2)) + Real.exp (Z + C₁) * Real.exp (-m)
          = Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2 + 1)) := by ring
      linarith [h, heq.le, heq.ge]
    rw [hsplit]
    calc (∫ α in (1 / (2 * L))..α₀, Real.exp (g α) / α) + ∫ α in α₀..1, Real.exp (g α) / α
        ≤ Real.exp (Z + C₁) * (Real.exp (-m) * (m + Real.log 2 + 1)) := htot
      _ ≤ Real.exp (Z + C₁) * ((1 + Real.log 2) * ((1 + m) * Real.exp (-m))) :=
          mul_le_mul_of_nonneg_left hkey2 (Real.exp_pos _).le
      _ = (1 + Real.log 2) * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by ring

/-! ## Comparing the scale `y` with the scale `x` (Mertens) -/

/-- Mertens' theorem in the form needed for the `Wsup` bounds:
`log (log x / log y) ≤ Zrcp x - Zrcp y + C` for `2 ≤ y ≤ x`. -/
lemma zrcp_ratio_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      Real.log (Real.log x / Real.log y) ≤ Work.BMF.Zrcp x - Work.BMF.Zrcp y + C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hZ11 : 0 ≤ Work.BMF.Zrcp 11 := Work.BMF.Zrcp_nonneg 11
  refine ⟨2 * C₀ + Work.BMF.Zrcp 11 + 1 + max 0 (Real.log (Real.log 11 / Real.log 2))
      + max 0 (-(Real.log (Real.log 2))), by positivity, ?_⟩
  intro x y hy2 hyx
  have hy1 : 1 < y := by linarith
  have hx1 : 1 < x := lt_of_lt_of_le hy1 hyx
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog11pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  -- (A) `log (log x / log y) ≤ log (log x) + max 0 (- log log 2)` for all `y ≥ 2`
  have hφ : Real.log (Real.log x / Real.log y)
      ≤ Real.log (Real.log x) + max 0 (-(Real.log (Real.log 2))) := by
    have h1 : Real.log x / Real.log y ≤ Real.log x / Real.log 2 :=
      div_le_div_of_nonneg_left hlx.le hlog2pos (Real.log_le_log (by norm_num) hy2)
    have h3 : 0 < Real.log x / Real.log y := div_pos hlx hly
    have h4 : Real.log (Real.log x / Real.log 2)
        = Real.log (Real.log x) - Real.log (Real.log 2) :=
      Real.log_div (ne_of_gt hlx) (ne_of_gt hlog2pos)
    have h5 : Real.log (Real.log x / Real.log y) ≤ Real.log (Real.log x / Real.log 2) :=
      Real.log_le_log h3 h1
    have h6 : -(Real.log (Real.log 2)) ≤ max 0 (-(Real.log (Real.log 2))) := le_max_right _ _
    linarith [h4 ▸ h5]
  rcases le_or_gt 11 y with hy11 | hy11
  · -- `11 ≤ y ≤ x`: two-sided Mertens at both scales
    have hx11 : 11 ≤ x := le_trans hy11 hyx
    have h1 := hC₀ x hx11
    have h2 := hC₀ y hy11
    rw [abs_le] at h1 h2
    have hx' : Real.log (Real.log x) - C₀ ≤ Work.BMF.Zrcp x := by
      have h := h1.1
      simp only [Work.BMF.Zrcp] at h ⊢
      linarith
    have hy' : Work.BMF.Zrcp y ≤ Real.log (Real.log y) + C₀ := by
      have h := h2.2
      simp only [Work.BMF.Zrcp] at h ⊢
      linarith
    have hlog : Real.log (Real.log x / Real.log y)
        = Real.log (Real.log x) - Real.log (Real.log y) :=
      Real.log_div (ne_of_gt hlx) (ne_of_gt hly)
    rw [hlog]
    linarith [hx', hy', hZ11, le_max_left (0:ℝ) (Real.log (Real.log 11 / Real.log 2)),
      le_max_left (0:ℝ) (-(Real.log (Real.log 2)))]
  · have hylog : Real.log y ≤ Real.log 11 := Real.log_le_log (by linarith) hy11.le
    have hzy : Work.BMF.Zrcp y ≤ Work.BMF.Zrcp 11 := Work.BMF.Zrcp_mono hy11.le
    rcases le_or_gt 11 x with hx11 | hx11
    · -- `y < 11 ≤ x`
      have h1 := hC₀ x hx11
      rw [abs_le] at h1
      have hx' : Real.log (Real.log x) - C₀ ≤ Work.BMF.Zrcp x := by
        have h := h1.1
        simp only [Work.BMF.Zrcp] at h ⊢
        linarith
      have hmax1 : (0:ℝ) ≤ max 0 (Real.log (Real.log 11 / Real.log 2)) := le_max_left _ _
      have hmax2 : (0:ℝ) ≤ max 0 (-(Real.log (Real.log 2))) := le_max_left _ _
      have hmax2' : -(Real.log (Real.log 2)) ≤ max 0 (-(Real.log (Real.log 2))) := le_max_right _ _
      linarith [hφ, hx', hzy, hZ11, hC₀pos.le, hmax1, hmax2, hmax2']
    · -- `x < 11` (and `y < 11`): crude bound
      have hquot : Real.log x / Real.log y ≤ Real.log 11 / Real.log 2 := by
        have h1 : Real.log x ≤ Real.log 11 := Real.log_le_log (by linarith) hx11.le
        have h2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
        exact le_trans (div_le_div_of_nonneg_left hlx.le hlog2pos h2)
          (div_le_div_of_nonneg_right h1 hlog2pos.le)
      have hφ' : Real.log (Real.log x / Real.log y) ≤ Real.log (Real.log 11 / Real.log 2) :=
        Real.log_le_log (div_pos hlx hly) hquot
      have hzx : 0 ≤ Work.BMF.Zrcp x := Work.BMF.Zrcp_nonneg x
      have hmax1 : Real.log (Real.log 11 / Real.log 2) ≤ max 0 (Real.log (Real.log 11 / Real.log 2)) :=
        le_max_right _ _
      have hmax2 : (0:ℝ) ≤ max 0 (-(Real.log (Real.log 2))) := le_max_left _ _
      linarith [hφ', hzy, hzx, hmax1, hmax2]

/-! ## The head/tail split at `y = exp (1/α)` -/

/-- **Pointwise bound for `Wsup` at the split scale `y = exp (1/α)`.** For `1`-bounded `f`,
`0 < α ≤ 1`, `T ≥ 0`, `11 ≤ x` and `y = exp (1/α) ≤ x`:

`Wsup f x α T ≤ Zrcp y - mHal f y T + C`.

This is the `y`-split of `Σ_{p ≤ x} f p p^{-1-α-it}`: on `p ≤ y` the weight `p^{-α}` is traded for
`(1 - p^{-α})/p` (costing `O(1)` since `α log y = 1`), and on `y < p ≤ x` one uses
`p^{-α} ≤ p^{-1/log y}` (costing `O(1)` by Mertens). -/
lemma wsup_le_zrcp_sub_mHal (C₂ C_L : ℝ)
    (hC_L : 0 ≤ C_L)
    (hsum : ∀ y : ℝ, 2 ≤ y →
      (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) ≤ C_L * Real.log y)
    (hC₂ : ∀ ε y x : ℝ, 0 < ε → ε ≤ 1 → 2 < y → 11 ≤ x → 1 ≤ ε * Real.log y →
      (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), (1 : ℝ) / (p : ℝ) ^ (1 + ε))
        ≤ C₂)
    (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {α T x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hT : 0 ≤ T)
    (hyx : Real.exp (1 / α) ≤ x) (hx11 : 11 ≤ x) :
    Work.BMF.Wsup f x α T
      ≤ Work.BMF.Zrcp (Real.exp (1 / α)) - Work.BMF.mHal f (Real.exp (1 / α)) T
        + (C_L + C₂) := by
  set y : ℝ := Real.exp (1 / α) with hydef
  have h1α : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
  have hy_e : Real.exp 1 ≤ y := by rw [hydef]; exact Real.exp_le_exp.mpr h1α
  have hy2 : 2 < y := by
    calc (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      _ ≤ y := hy_e
  have hy1 : 1 < y := by linarith
  have hlogypos : 0 < Real.log y := Real.log_pos hy1
  have hlogy1 : 1 ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos 1) hy_e
    rwa [Real.log_exp] at h
  have hlogy : Real.log y = 1 / α := by rw [hydef, Real.log_exp]
  have hαlogy : α * Real.log y = 1 := by rw [hlogy]; field_simp
  have hsub : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE :=
    Nat.primesLE_mono (Nat.floor_mono hyx)
  -- ## the pointwise bound for each admissible `t`
  have hpoint : ∀ t : ℝ, |t| ≤ T →
      (Work.BMF.vF f x ((1 + α : ℝ) + t * Complex.I)).re
        ≤ Work.BMF.Zrcp y - Work.BMF.mHalSum f y t + (C_L + C₂) := by
    intro t ht
    have hhead : (∑ p ∈ (⌊y⌋₊).primesLE,
          (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re)
        ≤ Work.BMF.Zrcp y - Work.BMF.mHalSum f y t + C_L := by
      have hterm : ∀ p ∈ (⌊y⌋₊).primesLE,
          (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
            ≤ (f p * (p : ℂ) ^ (-(Complex.I * t))).re / p + (1 - (p : ℝ) ^ (-α)) / p := by
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
        have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
        have hfac : (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))
            = (p : ℂ) ^ (-(Complex.I * t)) * ((((p : ℝ) ^ (-(1 + α)) : ℝ)) : ℂ) := by
          have hbase : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
          have hexp : -((1 + α : ℝ) + t * Complex.I)
              = -(Complex.I * t) + ((-((1 + α : ℝ))) : ℂ) := by push_cast; ring
          rw [hexp, Complex.cpow_add _ _ hpne, hbase, ← Complex.ofReal_neg,
            ← Complex.ofReal_cpow hp0.le]
        have hre : (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
            = (f p * (p : ℂ) ^ (-(Complex.I * t))).re * (p : ℝ) ^ (-(1 + α)) := by
          rw [hfac, ← mul_assoc, Complex.mul_re]
          simp
        have hwneg : -1 ≤ (f p * (p : ℂ) ^ (-(Complex.I * t))).re := by
          have h2 : ‖f p * (p : ℂ) ^ (-(Complex.I * t))‖ ≤ 1 := by
            have h3 : ‖(p : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
              rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
              have h4 : (-(Complex.I * t)).re = 0 := by simp
              rw [h4, Real.rpow_zero]
            rw [norm_mul, h3, mul_one]
            exact hb p
          have h4 := Complex.abs_re_le_norm (f p * (p : ℂ) ^ (-(Complex.I * t)))
          have h5 : |(f p * (p : ℂ) ^ (-(Complex.I * t))).re| ≤ 1 := by linarith
          exact (abs_le.mp h5).1
        have hkey : (p : ℝ) ^ (-(1 + α)) = (p : ℝ) ^ (-α) / p := by
          rw [show (-(1 + α) : ℝ) = -α + (-1 : ℝ) by ring, Real.rpow_add hp0]
          rw [Real.rpow_neg_one]; ring
        have hpa1 : (p : ℝ) ^ (-α) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -α ≤ 0)
          rwa [Real.rpow_zero] at h
        have hpa0 : 0 ≤ 1 - (p : ℝ) ^ (-α) := by linarith
        have hst : -((f p * (p : ℂ) ^ (-(Complex.I * t))).re) ≤ 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_right hst hpa0
        rw [hre, hkey, ← add_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hp0]
        nlinarith [hmul, hpa0]
      calc (∑ p ∈ (⌊y⌋₊).primesLE,
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re)
          ≤ ∑ p ∈ (⌊y⌋₊).primesLE,
              ((f p * (p : ℂ) ^ (-(Complex.I * t))).re / p + (1 - (p : ℝ) ^ (-α)) / p) :=
            Finset.sum_le_sum hterm
        _ = (∑ p ∈ (⌊y⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * t))).re / p)
              + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p :=
            Finset.sum_add_distrib
        _ = (Work.BMF.Zrcp y - Work.BMF.mHalSum f y t)
              + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by
            congr 1
            have hcongr : (∑ p ∈ (⌊y⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * t))).re / p)
                = ∑ p ∈ (⌊y⌋₊).primesLE,
                    ((1 : ℝ) / p - (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p) :=
              Finset.sum_congr rfl (fun p _ => by ring)
            rw [hcongr, Finset.sum_sub_distrib, ← Work.BMF.Zrcp, ← Work.BMF.mHalSum]
        _ ≤ (Work.BMF.Zrcp y - Work.BMF.mHalSum f y t) + C_L := by
            refine add_le_add le_rfl ?_
            calc (∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p)
                ≤ ∑ p ∈ (⌊y⌋₊).primesLE, α * (Real.log p / (p : ℝ)) := by
                  refine Finset.sum_le_sum (fun p hp => ?_)
                  have hpp := Nat.prime_of_mem_primesLE hp
                  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
                  have h1 : 1 - (p : ℝ) ^ (-α) ≤ α * Real.log p := by
                    have h2 : (p : ℝ) ^ (-α) = Real.exp (-(α * Real.log p)) := by
                      rw [Real.rpow_def_of_pos hp0]
                      congr 1
                      ring
                    have h3 := Real.add_one_le_exp (-(α * Real.log p))
                    linarith [h2, h3]
                  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hp0]
                  exact h1
              _ = α * (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) := by
                  rw [Finset.mul_sum]
              _ ≤ α * (C_L * Real.log y) :=
                  mul_le_mul_of_nonneg_left (hsum y (le_of_lt hy2)) hα.le
              _ = C_L := by
                  rw [mul_comm C_L (Real.log y), ← mul_assoc, hαlogy, one_mul]
    have htail : (∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
          (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re) ≤ C₂ := by
      have hstep1 : (∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re)
          ≤ ∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE), (p : ℝ) ^ (-(1 + α)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        calc (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
            ≤ ‖f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖ := Complex.re_le_norm _
          _ = ‖f p‖ * ‖(p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖ := norm_mul _ _
          _ ≤ 1 * (p : ℝ) ^ (-(1 + α)) := by
              have hnorm : ‖(p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖
                  = (p : ℝ) ^ (-(1 + α)) := by
                rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
                congr 1
                simp [Complex.neg_re, Complex.add_re, Complex.mul_re]
              rw [hnorm]
              exact mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg hp0.le _)
          _ = (p : ℝ) ^ (-(1 + α)) := one_mul _
      have hsubset : (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE
          ⊆ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))) := by
        intro p hp
        obtain ⟨hpx, hpy⟩ := Finset.mem_sdiff.mp hp
        refine Finset.mem_filter.mpr ⟨hpx, ?_⟩
        have hpp := Nat.prime_of_mem_primesLE hpx
        by_contra hcon
        push_neg at hcon
        exact hpy (Nat.mem_primesLE.mpr ⟨Nat.le_floor hcon, hpp⟩)
      have hterm2 : ∀ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
          (p : ℝ) ^ (-(1 + α)) ≤ (1 : ℝ) / (p : ℝ) ^ (1 + 1 / Real.log y) := by
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
        have hεα : 1 / Real.log y ≤ α := by
          rw [div_le_iff₀ hlogypos, hαlogy]
        have hexp : -(1 + α) ≤ -(1 + 1 / Real.log y) := by linarith
        calc (p : ℝ) ^ (-(1 + α)) ≤ (p : ℝ) ^ (-(1 + 1 / Real.log y)) :=
              Real.rpow_le_rpow_of_exponent_le hp1 hexp
          _ = (1 : ℝ) / (p : ℝ) ^ (1 + 1 / Real.log y) := by
              rw [Real.rpow_neg (by positivity)]; ring
      calc (∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re)
          ≤ ∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE), (p : ℝ) ^ (-(1 + α)) := hstep1
        _ ≤ ∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
              (1 : ℝ) / (p : ℝ) ^ (1 + 1 / Real.log y) := Finset.sum_le_sum hterm2
        _ ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
              (1 : ℝ) / (p : ℝ) ^ (1 + 1 / Real.log y) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun p _ _ => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        _ ≤ C₂ := by
            refine hC₂ (1 / Real.log y) y x (div_pos one_pos hlogypos) ?_ hy2 hx11 ?_
            · rw [div_le_one hlogypos]; exact hlogy1
            · rw [one_div, inv_mul_cancel₀ (ne_of_gt hlogypos)]
    have hsplit : (Work.BMF.vF f x ((1 + α : ℝ) + t * Complex.I)).re
        = (∑ p ∈ (⌊y⌋₊).primesLE,
              (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re)
          + ∑ p ∈ ((⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE),
              (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re := by
      rw [Work.BMF.vF]
      rw [show (∑ p ∈ (⌊x⌋₊).primesLE,
            f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
          = ∑ p ∈ (⌊x⌋₊).primesLE,
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
          from map_sum Complex.reAddGroupHom _ _]
      rw [← Finset.sum_sdiff hsub, add_comm]
    rw [hsplit]
    linarith [hhead, htail]
  -- ## the supremum
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT⟩⟩
  unfold Work.BMF.Wsup
  rw [show (⨆ (t : {t : ℝ // |t| ≤ T}),
      (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)
    = sSup (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) from rfl]
  refine ciSup_le (fun t => ?_)
  have h1' := hpoint t.1 t.2
  have h2' : Work.BMF.mHal f y T ≤ Work.BMF.mHalSum f y t.1 := HLip.mHal_le_psum hb t.2
  linarith

/-! ## The two pointwise bounds for `Wsup` -/

/-- **Trivial (Mertens) bound for `Wsup`.** For `1`-bounded `f`, `3 ≤ x`, `1 ≤ T` and
`1/log x ≤ α ≤ 1`:
`Wsup f x α T ≤ Zrcp x - log (α log x) + C` (Ramaré, *Wirsing–Halász*, "trivial bound"). -/
theorem wsup_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ x α T : ℝ, 3 ≤ x → 1 ≤ T → 1 / Real.log x ≤ α → α ≤ 1 →
        Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x - Real.log (α * Real.log x) + C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.BMF.halasz_mertens_aux.2.2
  obtain ⟨C_L, hC_Lpos, hsum⟩ := Work.BMF.HL.sum_log_div_prime_le
  obtain ⟨C_m, hC_mpos, hC_m⟩ := zrcp_ratio_log_le
  refine ⟨max (max (Real.log (Real.log 11)) (C_L + C₂ + C_m)) 1, by positivity, ?_⟩
  intro f hb x α T hx3 hT hαlog hα1
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hαlog
  have hCbig : Real.log (Real.log 11) ≤ max (max (Real.log (Real.log 11)) (C_L + C₂ + C_m)) 1 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCall : C_L + C₂ + C_m ≤ max (max (Real.log (Real.log 11)) (C_L + C₂ + C_m)) 1 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  rcases lt_or_ge x 11 with hx11 | hx11
  · -- small `x`: `Wsup ≤ Zrcp x`, and `log (α log x) ≤ log (log 11)`
    have hW : Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x :=
      Wsup_le_Zrcp f hb x T α hαpos.le
    have hlog : Real.log (α * Real.log x) ≤ Real.log (Real.log 11) := by
      have h1 : 1 ≤ α * Real.log x := by
        calc (1 : ℝ) = (1 / Real.log x) * Real.log x := by
              rw [one_div, inv_mul_cancel₀ (ne_of_gt hlogxpos)]
          _ ≤ α * Real.log x := mul_le_mul_of_nonneg_right hαlog hlogxpos.le
      have h2 : α * Real.log x ≤ Real.log 11 := by
        have h3 : α * Real.log x ≤ 1 * Real.log x := mul_le_mul_of_nonneg_right hα1 hlogxpos.le
        have h4 : Real.log x ≤ Real.log 11 := Real.log_le_log (by linarith) hx11.le
        linarith
      exact Real.log_le_log (lt_of_lt_of_le zero_lt_one h1) h2
    linarith
  · -- `11 ≤ x`: split at `y = exp (1/α)`
    set y : ℝ := Real.exp (1 / α) with hydef
    have hyx : y ≤ x := by
      have h1 : 1 / α ≤ Real.log x := by
        rw [div_le_iff₀ hαpos]
        calc (1 : ℝ) = Real.log x * (1 / Real.log x) := by
              rw [one_div, mul_inv_cancel₀ (ne_of_gt hlogxpos)]
          _ ≤ Real.log x * α := mul_le_mul_of_nonneg_left hαlog hlogxpos.le
      calc y = Real.exp (1 / α) := hydef
        _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h1
        _ = x := Real.exp_log (by linarith)
    have hy2 : 2 ≤ y := by
      rw [hydef]
      have h1α : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hαpos]; linarith
      exact le_of_lt (calc (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        _ ≤ Real.exp (1 / α) := Real.exp_le_exp.mpr h1α)
    have hlogy : Real.log y = 1 / α := by rw [hydef, Real.log_exp]
    have hratio : Real.log x / Real.log y = α * Real.log x := by
      rw [hlogy]
      field_simp
    have hW : Work.BMF.Wsup f x α T
        ≤ Work.BMF.Zrcp y - Work.BMF.mHal f y T + (C_L + C₂) :=
      wsup_le_zrcp_sub_mHal C₂ C_L hC_Lpos.le hsum hC₂ f hb hαpos hα1 (by linarith) hyx hx11
    have hm := hC_m x y hy2 hyx
    rw [hratio] at hm
    have hmHal : Work.BMF.mHal f y T ≥ 0 := Work.BMF.mHal_nonneg f hb y T (by linarith)
    have hZy : Work.BMF.Zrcp y ≤ Work.BMF.Zrcp x - Real.log (α * Real.log x) + C_m := by
      linarith [hm]
    linarith [hW, hZy, hmHal, hCall]

/-- **Sharp pointwise bound for `Wsup`** (two-window form). For `1`-bounded `f`, `3 ≤ x`, `0 < α ≤ 1`,
`1 ≤ T'` (the window of the supremum), `1 ≤ T` and `T' + 1 ≤ 2T` (so that the `Lipschitz` estimate
`halasz_lipschitz` may be applied with window `T'`):
`Wsup f x α T' ≤ Zrcp x - mHal f x (2T) + C` (Ramaré, *Wirsing–Halász*: the "sharp bound"). -/
theorem wsup_mHal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ x α T T' : ℝ, 3 ≤ x → 1 ≤ T → 1 ≤ T' → T' + 1 ≤ 2 * T → 0 < α → α ≤ 1 →
        Work.BMF.Wsup f x α T' ≤ Work.BMF.Zrcp x - Work.BMF.mHal f x (2 * T) + C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.BMF.halasz_mertens_aux.2.2
  obtain ⟨C_L, hC_Lpos, hsum⟩ := Work.BMF.HL.sum_log_div_prime_le
  obtain ⟨C_m, hC_mpos, hC_m⟩ := zrcp_ratio_log_le
  obtain ⟨C_lip, hC_lip_pos, hC_lip⟩ := Work.BMF.halasz_lipschitz
  refine ⟨max (max (2 * Work.BMF.Zrcp 11) (C_L + C_L + C₂ + C_m + C_lip)) 1, by positivity, ?_⟩
  intro f hb x α T T' hx3 hT hT' hwin hαpos hα1
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hCsmall : 2 * Work.BMF.Zrcp 11 ≤
      max (max (2 * Work.BMF.Zrcp 11) (C_L + C_L + C₂ + C_m + C_lip)) 1 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCbig : C_L + C_L + C₂ + C_m + C_lip ≤
      max (max (2 * Work.BMF.Zrcp 11) (C_L + C_L + C₂ + C_m + C_lip)) 1 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  rcases lt_or_ge x 11 with hx11 | hx11
  · -- small `x`
    have hW : Work.BMF.Wsup f x α T' ≤ Work.BMF.Zrcp x := Wsup_le_Zrcp f hb x T' α hαpos.le
    have hm : Work.BMF.mHal f x (2 * T) ≤ 2 * Work.BMF.Zrcp x :=
      Work.BMF.mHal_le_two_Zrcp f hb x (2 * T) (by linarith)
    have hzx : Work.BMF.Zrcp x ≤ Work.BMF.Zrcp 11 :=
      Work.BMF.Zrcp_mono (le_of_lt hx11)
    linarith
  · -- `11 ≤ x`
    rcases le_or_gt α (1 / Real.log x) with hsmall | hbig
    · -- `α ≤ 1/log x`: no split needed, the loss `Σ (1 - p^{-α})/p` is `≤ C_L`
      have hCLle : C_L ≤ max (max (2 * Work.BMF.Zrcp 11)
          (C_L + C_L + C₂ + C_m + C_lip)) 1 :=
        le_trans (by linarith [hC_Lpos.le, hC₂pos.le, hC_mpos.le, hC_lip_pos.le]) hCbig
      have hpoint : ∀ t : ℝ, |t| ≤ T' →
          (Work.BMF.vF f x ((1 + α : ℝ) + t * Complex.I)).re
            ≤ Work.BMF.Zrcp x - Work.BMF.mHal f x (2 * T)
              + max (max (2 * Work.BMF.Zrcp 11) (C_L + C_L + C₂ + C_m + C_lip)) 1 := by
        intro t ht
        have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
              ≤ (f p * (p : ℂ) ^ (-(Complex.I * t))).re / p + (1 - (p : ℝ) ^ (-α)) / p := by
          intro p hp
          have hpp := Nat.prime_of_mem_primesLE hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
          have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
          have hfac : (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))
              = (p : ℂ) ^ (-(Complex.I * t)) * ((((p : ℝ) ^ (-(1 + α)) : ℝ)) : ℂ) := by
            have hbase : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
            have hexp : -((1 + α : ℝ) + t * Complex.I)
                = -(Complex.I * t) + ((-((1 + α : ℝ))) : ℂ) := by push_cast; ring
            rw [hexp, Complex.cpow_add _ _ hpne, hbase, ← Complex.ofReal_neg,
              ← Complex.ofReal_cpow hp0.le]
          have hre : (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
              = (f p * (p : ℂ) ^ (-(Complex.I * t))).re * (p : ℝ) ^ (-(1 + α)) := by
            rw [hfac, ← mul_assoc, Complex.mul_re]
            simp
          have hwneg : -1 ≤ (f p * (p : ℂ) ^ (-(Complex.I * t))).re := by
            have h2 : ‖f p * (p : ℂ) ^ (-(Complex.I * t))‖ ≤ 1 := by
              have h3 : ‖(p : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
                rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
                have h4 : (-(Complex.I * t)).re = 0 := by simp
                rw [h4, Real.rpow_zero]
              rw [norm_mul, h3, mul_one]
              exact hb p
            have h4 := Complex.abs_re_le_norm (f p * (p : ℂ) ^ (-(Complex.I * t)))
            have h5 : |(f p * (p : ℂ) ^ (-(Complex.I * t))).re| ≤ 1 := by linarith
            exact (abs_le.mp h5).1
          have hkey : (p : ℝ) ^ (-(1 + α)) = (p : ℝ) ^ (-α) / p := by
            rw [show (-(1 + α) : ℝ) = -α + (-1 : ℝ) by ring, Real.rpow_add hp0]
            rw [Real.rpow_neg_one]; ring
          have hpa1 : (p : ℝ) ^ (-α) ≤ 1 := by
            have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -α ≤ 0)
            rwa [Real.rpow_zero] at h
          have hpa0 : 0 ≤ 1 - (p : ℝ) ^ (-α) := by linarith
          have hst : -((f p * (p : ℂ) ^ (-(Complex.I * t))).re) ≤ 1 := by linarith
          have hmul := mul_le_mul_of_nonneg_right hst hpa0
          rw [hre, hkey, ← add_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hp0]
          nlinarith [hmul, hpa0]
        calc (Work.BMF.vF f x ((1 + α : ℝ) + t * Complex.I)).re
            = ∑ p ∈ (⌊x⌋₊).primesLE,
                (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re := by
              rw [Work.BMF.vF]
              exact map_sum Complex.reAddGroupHom _ _
          _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE,
              ((f p * (p : ℂ) ^ (-(Complex.I * t))).re / p + (1 - (p : ℝ) ^ (-α)) / p) :=
              Finset.sum_le_sum hterm
          _ = (Work.BMF.Zrcp x - Work.BMF.mHalSum f x t)
              + ∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by
              rw [Finset.sum_add_distrib]
              congr 1
              have hcongr : (∑ p ∈ (⌊x⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * t))).re / p)
                  = ∑ p ∈ (⌊x⌋₊).primesLE,
                      ((1 : ℝ) / p - (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p) :=
                Finset.sum_congr rfl (fun p _ => by ring)
              rw [hcongr, Finset.sum_sub_distrib, ← Work.BMF.Zrcp, ← Work.BMF.mHalSum]
          _ ≤ (Work.BMF.Zrcp x - Work.BMF.mHalSum f x t) + C_L := by
              refine add_le_add le_rfl ?_
              calc (∑ p ∈ (⌊x⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p)
                  ≤ ∑ p ∈ (⌊x⌋₊).primesLE, α * (Real.log p / (p : ℝ)) := by
                    refine Finset.sum_le_sum (fun p hp => ?_)
                    have hpp := Nat.prime_of_mem_primesLE hp
                    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
                    have h1 : 1 - (p : ℝ) ^ (-α) ≤ α * Real.log p := by
                      have h2 : (p : ℝ) ^ (-α) = Real.exp (-(α * Real.log p)) := by
                        rw [Real.rpow_def_of_pos hp0]
                        congr 1
                        ring
                      have h3 := Real.add_one_le_exp (-(α * Real.log p))
                      linarith [h2, h3]
                    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hp0]
                    exact h1
                _ = α * (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / (p : ℝ)) := by
                    rw [Finset.mul_sum]
                _ ≤ α * (C_L * Real.log x) :=
                    mul_le_mul_of_nonneg_left (hsum x (by linarith)) hαpos.le
                _ ≤ C_L := by
                    have hαL : α * Real.log x ≤ 1 := by
                      rw [le_div_iff₀ hlogxpos] at hsmall
                      linarith
                    nlinarith [hC_Lpos, hαL, hlogxpos]
          _ ≤ Work.BMF.Zrcp x - Work.BMF.mHal f x (2 * T) + C_L := by
              have h1 : Work.BMF.mHal f x (2 * T) ≤ Work.BMF.mHalSum f x t := by
                have h2 : Work.BMF.mHal f x (T' + 1) ≤ Work.BMF.mHalSum f x t :=
                  HLip.mHal_le_psum (z := x) (T := T' + 1) (t := t) hb
                    (by calc |t| ≤ T' := ht
                          _ ≤ T' + 1 := by linarith)
                have h3 : Work.BMF.mHal f x (2 * T) ≤ Work.BMF.mHal f x (T' + 1) :=
                  Work.BMF.mHal_anti f hb x (T' + 1) (2 * T) hwin (by linarith)
                exact le_trans h3 h2
              linarith
          _ ≤ Work.BMF.Zrcp x - Work.BMF.mHal f x (2 * T)
              + max (max (2 * Work.BMF.Zrcp 11) (C_L + C_L + C₂ + C_m + C_lip)) 1 := by
              linarith [hCLle]
      haveI : Nonempty {t : ℝ // |t| ≤ T'} := ⟨⟨0, by rw [abs_zero]; linarith⟩⟩
      unfold Work.BMF.Wsup
      rw [show (⨆ (t : {t : ℝ // |t| ≤ T'}),
          (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)
        = sSup (Set.range (fun t : {t : ℝ // |t| ≤ T'} =>
          (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) from rfl]
      exact ciSup_le (fun t => hpoint t.1 t.2)
    · -- `1/log x < α`: split at `y = exp (1/α)`
      set y : ℝ := Real.exp (1 / α) with hydef
      have hyx : y ≤ x := by
        have hb' : 1 < α * Real.log x := by
          have h := (div_lt_iff₀ hlogxpos).mp hbig
          linarith
        have h1 : 1 / α ≤ Real.log x := by
          rw [div_le_iff₀ hαpos]
          linarith
        calc y = Real.exp (1 / α) := hydef
          _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h1
          _ = x := Real.exp_log (by linarith)
      have hy2 : 2 ≤ y := by
        rw [hydef]
        have h1α : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hαpos]; linarith
        exact le_of_lt (calc (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          _ ≤ Real.exp (1 / α) := Real.exp_le_exp.mpr h1α)
      have hlogy : Real.log y = 1 / α := by rw [hydef, Real.log_exp]
      have hratio : Real.log x / Real.log y = α * Real.log x := by
        rw [hlogy]
        field_simp
      have hW : Work.BMF.Wsup f x α T'
          ≤ Work.BMF.Zrcp y - Work.BMF.mHal f y T' + (C_L + C₂) :=
        wsup_le_zrcp_sub_mHal C₂ C_L hC_Lpos.le hsum hC₂ f hb hαpos hα1 (by linarith) hyx hx11
      have hm := hC_m x y hy2 hyx
      rw [hratio] at hm
      have hZy : Work.BMF.Zrcp y ≤ Work.BMF.Zrcp x - Real.log (α * Real.log x) + C_m := by
        linarith [hm]
      have hlip := hC_lip f hb x y T' hy2 hyx (by linarith)
      rw [hratio] at hlip
      have hanti : Work.BMF.mHal f x (2 * T) ≤ Work.BMF.mHal f x (T' + 1) :=
        Work.BMF.mHal_anti f hb x (T' + 1) (2 * T) hwin (by linarith)
      linarith [hW, hZy, hlip, hanti, hCbig, hC_Lpos.le, hC₂pos.le, hC_mpos.le, hC_lip_pos.le]

/-! ## Monotonicity of `t ↦ (1 + t) e^{-t}` -/

lemma one_add_mul_exp_neg_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 + b) * Real.exp (-b) ≤ (1 + a) * Real.exp (-a) := by
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have h1 : 1 + b ≤ (1 + a) * Real.exp (b - a) := by
    have hexp := Real.add_one_le_exp (b - a)
    have h2 : (1 + a) * (1 + (b - a)) ≤ (1 + a) * Real.exp (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 : (1 + a) * (1 + (b - a)) = 1 + b + a * (b - a) := by ring
    nlinarith [h2, mul_nonneg ha hd]
  have h2 : (1 + b) * Real.exp (-(b - a)) ≤ (1 + a) := by
    have h := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(b - a))).le
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h
    exact h
  calc (1 + b) * Real.exp (-b)
      = (1 + b) * Real.exp (-(b - a)) * Real.exp (-a) := by
        rw [show -b = -(b - a) + -a by ring, Real.exp_add]; ring
    _ ≤ (1 + a) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-a)).le

/-! ## Assembly: Ramaré's `casdiv` + the `Wsup` bounds ⟹ the `majm` bound -/

/-- **The `majm` bound from Ramaré's `casdiv`.** If the `casdiv` estimate holds in the form
`‖Mf f x‖ ≤ C (x/log x)(∫_{1/(2log x)}^1 e^{Wsup f x α (T+1)} dα/α + e^Z/√T + e^Z/log x)`, then the
sharp Halász bound `‖Mf f x‖ ≤ C x ((1+m)e^{-m} + 1/√T + 1/log x)`, `m = mHal f x (2T)`, follows:
the α-integral is evaluated by `crossover_sharp` from `wsup_mHal_bound` and `wsup_log_bound`, and
Mertens (`exp_Zrcp_le_log`) removes `e^Z`. -/
theorem halasz_majm_of_casdiv
    (hcasdiv : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / (2 * Real.log x))..1,
              Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C₁ * x *
          ((1 + Work.BMF.mHal f x (2 * T)) * Real.exp (-(Work.BMF.mHal f x (2 * T))) +
            1 / Real.sqrt T + 1 / Real.log x) := by
  obtain ⟨Cc, hCcpos, hcasdiv'⟩ := hcasdiv
  obtain ⟨Cw1, hCw1pos, hw1⟩ := wsup_mHal_bound
  obtain ⟨Cw2, hCw2pos, hw2⟩ := wsup_log_bound
  obtain ⟨Ccross, hCcrosspos, hcross⟩ := crossover_sharp
  obtain ⟨CL, hCLpos, hCL⟩ := exp_Zrcp_le_log
  set K : ℝ := Ccross * Real.exp (max Cw1 Cw2) * CL with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨Cc * (K + CL + 1) + Cc, by positivity, ?_⟩
  intro f hf1 hmul hb x T hx hT
  set L : ℝ := Real.log x with hLdef
  set Z : ℝ := Work.BMF.Zrcp x with hZdef
  set m : ℝ := Work.BMF.mHal f x (2 * T) with hmdef
  have hx0 : 0 ≤ x := by linarith
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hmn : 0 ≤ m := by rw [hmdef]; exact Work.BMF.mHal_nonneg f hb x (2 * T) (by linarith)
  have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hP : 0 ≤ (1 + m) * Real.exp (-m) := mul_nonneg (by linarith) (Real.exp_pos _).le
  -- ## integrability of the α-integrand
  have hInt : IntervalIntegrable
      (fun α : ℝ => Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) MeasureTheory.volume
      (1 / (2 * L)) 1 := by
    have h2L : 0 < 2 * L := by linarith
    have hle : 1 / (2 * L) ≤ 1 := by
      rw [div_le_one h2L]; linarith
    refine intM_intervalIntegrable_of_bound_real hle ?_
      (C := Real.exp Z * (2 * L)) ?_
    · exact ((Wsup_measurable f x (T + 1)).exp.div measurable_id).aestronglyMeasurable.restrict
    · intro α hα
      have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα.1.le
      have hαinv : α⁻¹ ≤ 2 * L := by
        rw [inv_le_iff_one_le_mul₀ hαpos]
        have h1 : 1 / (2 * L) < α := hα.1
        rw [div_lt_iff₀ h2L] at h1
        linarith [h1]
      have hW : Work.BMF.Wsup f x α (T + 1) ≤ Work.BMF.Zrcp x :=
        Wsup_le_Zrcp f hb x (T + 1) α hαpos.le
      rw [← hZdef] at hW
      rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hαpos.le)]
      calc Real.exp (Work.BMF.Wsup f x α (T + 1)) / α
          ≤ Real.exp Z / α := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hW) hαpos.le
        _ ≤ Real.exp Z * (2 * L) := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hαinv (Real.exp_pos _).le
  -- ## the two hypotheses of the crossover
  have hcov1 : ∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 →
      Work.BMF.Wsup f x α (T + 1) ≤ Z - m + max Cw1 Cw2 := by
    intro α hα hα1
    have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα
    have h := hw1 f hb x α T (T + 1) hx (by linarith) (by linarith) (by linarith) hαpos
      (le_trans hα1 (by norm_num))
    rw [← hmdef] at h
    linarith [h, le_max_left Cw1 Cw2]
  have hcov2 : ∀ α : ℝ, 1 / (2 * L) ≤ α → α ≤ 1 →
      Work.BMF.Wsup f x α (T + 1) ≤ Z - Real.log (α * L) + max Cw1 Cw2 := by
    intro α hα hα1
    have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα
    rcases le_or_gt (1 / L) α with hαbig | hαsmall
    · have h := hw2 f hb x α (T + 1) hx (by linarith) hαbig (le_trans hα1 (by norm_num))
      rw [← hLdef] at h
      linarith [h, le_max_right Cw1 Cw2]
    · have hW : Work.BMF.Wsup f x α (T + 1) ≤ Z := by
        rw [hZdef]
        exact Wsup_le_Zrcp f hb x (T + 1) α hαpos.le
      have hlog : Real.log (α * L) ≤ 0 := by
        have hlt : α * L < 1 := (lt_div_iff₀ hLpos).mp hαsmall
        exact Real.log_nonpos (mul_pos hαpos hLpos).le hlt.le
      have hmax : 0 ≤ max Cw1 Cw2 := le_max_of_le_left hCw1pos.le
      linarith
  have hcross' := hcross (fun α => Work.BMF.Wsup f x α (T + 1)) L Z m (max Cw1 Cw2) hL1 hmn
    (le_max_of_le_left hCw1pos.le) hInt hcov1 hcov2
  -- ## the three terms
  have hEZ : Real.exp Z ≤ CL * L := by
    rw [hZdef, hLdef]
    exact hCL x hx
  have hT1 : (x / L) * (∫ α in (1 / (2 * L))..1,
        Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) ≤ K * x * ((1 + m) * Real.exp (-m)) := by
    have hstep : (x / L) * Real.exp Z ≤ x * CL := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
      nlinarith [hEZ, hLpos, hx0]
    calc (x / L) * (∫ α in (1 / (2 * L))..1,
          Real.exp (Work.BMF.Wsup f x α (T + 1)) / α)
        ≤ (x / L) * (Ccross * Real.exp (Z + max Cw1 Cw2) * ((1 + m) * Real.exp (-m))) :=
          mul_le_mul_of_nonneg_left hcross' (by positivity)
      _ = (Ccross * Real.exp (max Cw1 Cw2) * ((1 + m) * Real.exp (-m))) * ((x / L) * Real.exp Z) := by
          rw [Real.exp_add]; ring
      _ ≤ (Ccross * Real.exp (max Cw1 Cw2) * ((1 + m) * Real.exp (-m))) * (x * CL) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = K * x * ((1 + m) * Real.exp (-m)) := by rw [hKdef]; ring
  have hT2 : (x / L) * (Real.exp Z / Real.sqrt T) ≤ CL * x * (1 / Real.sqrt T) := by
    have h1 : Real.exp Z / Real.sqrt T ≤ CL * L / Real.sqrt T :=
      div_le_div_of_nonneg_right hEZ hsqrtpos.le
    calc (x / L) * (Real.exp Z / Real.sqrt T) ≤ (x / L) * (CL * L / Real.sqrt T) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CL * x * (1 / Real.sqrt T) := by
          field_simp
  have hT3 : (x / L) * (Real.exp Z / L) ≤ CL * x * (1 / L) := by
    have h1 : Real.exp Z / L ≤ CL := by
      rw [div_le_iff₀ hLpos]
      exact hEZ
    calc (x / L) * (Real.exp Z / L) ≤ (x / L) * CL :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CL * x * (1 / L) := by rw [div_mul_eq_mul_div, div_eq_mul_inv]; ring
  -- ## assemble
  have hmain := hcasdiv' f hf1 hmul hb x T hx hT
  rw [← hLdef, ← hZdef] at hmain
  rw [mul_add, mul_add] at hmain
  have hb' : 0 ≤ 1 / Real.sqrt T := by positivity
  have hc : 0 ≤ 1 / L := by positivity
  have hfin : Cc * ((x / L) * (∫ α in (1 / (2 * L))..1,
          Real.exp (Work.BMF.Wsup f x α (T + 1)) / α))
        + Cc * ((x / L) * (Real.exp Z / Real.sqrt T))
        + Cc * ((x / L) * (Real.exp Z / L))
      ≤ (Cc * (K + CL + 1) + Cc) * x * ((1 + m) * Real.exp (-m) + 1 / Real.sqrt T + 1 / L) := by
    have hA := mul_le_mul_of_nonneg_left hT1 hCcpos.le
    have hB := mul_le_mul_of_nonneg_left hT2 hCcpos.le
    have hD := mul_le_mul_of_nonneg_left hT3 hCcpos.le
    have hCtK : Cc * K ≤ Cc * (K + CL + 1) + Cc := by nlinarith [hCcpos.le, hCLpos.le]
    have hCtL : Cc * CL ≤ Cc * (K + CL + 1) + Cc := by nlinarith [hCcpos.le, hKpos.le]
    have hxP : 0 ≤ x * ((1 + m) * Real.exp (-m)) := mul_nonneg hx0 hP
    have hxb : 0 ≤ x * (1 / Real.sqrt T) := mul_nonneg hx0 hb'
    have hxc : 0 ≤ x * (1 / L) := mul_nonneg hx0 hc
    have e1 : Cc * (K * x * ((1 + m) * Real.exp (-m)))
        ≤ (Cc * (K + CL + 1) + Cc) * (x * ((1 + m) * Real.exp (-m))) := by
      calc Cc * (K * x * ((1 + m) * Real.exp (-m)))
          = (Cc * K) * (x * ((1 + m) * Real.exp (-m))) := by ring
        _ ≤ (Cc * (K + CL + 1) + Cc) * (x * ((1 + m) * Real.exp (-m))) :=
            mul_le_mul_of_nonneg_right hCtK hxP
    have e2 : Cc * (CL * x * (1 / Real.sqrt T))
        ≤ (Cc * (K + CL + 1) + Cc) * (x * (1 / Real.sqrt T)) := by
      calc Cc * (CL * x * (1 / Real.sqrt T))
          = (Cc * CL) * (x * (1 / Real.sqrt T)) := by ring
        _ ≤ (Cc * (K + CL + 1) + Cc) * (x * (1 / Real.sqrt T)) :=
            mul_le_mul_of_nonneg_right hCtL hxb
    have e3 : Cc * (CL * x * (1 / L))
        ≤ (Cc * (K + CL + 1) + Cc) * (x * (1 / L)) := by
      calc Cc * (CL * x * (1 / L))
          = (Cc * CL) * (x * (1 / L)) := by ring
        _ ≤ (Cc * (K + CL + 1) + Cc) * (x * (1 / L)) :=
            mul_le_mul_of_nonneg_right hCtL hxc
    have hsum : Cc * (K * x * ((1 + m) * Real.exp (-m))) + Cc * (CL * x * (1 / Real.sqrt T))
        + Cc * (CL * x * (1 / L))
        ≤ (Cc * (K + CL + 1) + Cc) * (x * ((1 + m) * Real.exp (-m)))
          + (Cc * (K + CL + 1) + Cc) * (x * (1 / Real.sqrt T))
          + (Cc * (K + CL + 1) + Cc) * (x * (1 / L)) := by linarith [e1, e2, e3]
    have hfactor : (Cc * (K + CL + 1) + Cc) * (x * ((1 + m) * Real.exp (-m)))
          + (Cc * (K + CL + 1) + Cc) * (x * (1 / Real.sqrt T))
          + (Cc * (K + CL + 1) + Cc) * (x * (1 / L))
        = (Cc * (K + CL + 1) + Cc) * x
            * ((1 + m) * Real.exp (-m) + 1 / Real.sqrt T + 1 / L) := by ring
    linarith [hA, hB, hD, hsum, hfactor]
  linarith [hmain, hfin]

/-! ## Ramaré's `casdiv` (the remaining input) -/

/-- **The `1/log x` version of `casdiv` implies the `1/(2 log x)` version.** The integrand
`exp (Wsup f x α (T+1))/α` is nonnegative, so enlarging the integration range only enlarges the
integral. -/
lemma casdiv_majm_of_log_version
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / Real.log x)..1,
              Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / (2 * Real.log x))..1,
              Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x) := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, ?_⟩
  intro f hf1 hmul hb x T hx hT
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hapos : 0 < 1 / (2 * Real.log x) := by positivity
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hAB : 1 / (2 * Real.log x) ≤ 1 / Real.log x := by
    have h1 : (1:ℝ) / (2 * Real.log x) = ((1:ℝ) / 2) / Real.log x := by ring
    rw [h1]
    exact div_le_div_of_nonneg_right (by norm_num) hlogxpos.le
  have hB1 : 1 / Real.log x ≤ 1 := by
    rw [one_div, inv_le_one₀ hlogxpos]
    linarith
  have hI : IntervalIntegrable
      (fun α : ℝ => Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) MeasureTheory.volume
      (1 / (2 * Real.log x)) 1 := by
    have hle : 1 / (2 * Real.log x) ≤ 1 := le_trans hAB hB1
    refine intM_intervalIntegrable_of_bound_real hle
      (((Wsup_measurable f x (T + 1)).exp.div measurable_id).aestronglyMeasurable.restrict)
      (C := Real.exp (Work.BMF.Zrcp x) * (2 * Real.log x)) (fun t ht => by
        have htpos : 0 < t := lt_trans hapos ht.1
        have htinv : t⁻¹ ≤ 2 * Real.log x := by
          have h1 : 1 / (2 * Real.log x) < t := ht.1
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.log x)] at h1
          rw [inv_le_iff_one_le_mul₀ htpos]
          linarith [h1]
        have hW : Work.BMF.Wsup f x t (T + 1) ≤ Work.BMF.Zrcp x :=
          Wsup_le_Zrcp f hb x (T + 1) t (le_of_lt htpos)
        rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le htpos.le)]
        calc Real.exp (Work.BMF.Wsup f x t (T + 1)) / t
            ≤ Real.exp (Work.BMF.Zrcp x) / t :=
              div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hW) htpos.le
          _ ≤ Real.exp (Work.BMF.Zrcp x) * (2 * Real.log x) := by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left htinv (Real.exp_pos _).le)
  have hI1 : IntervalIntegrable
      (fun α : ℝ => Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) MeasureTheory.volume
      (1 / (2 * Real.log x)) (1 / Real.log x) :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hAB, Set.uIcc_of_le (le_trans hAB hB1)]
      exact Set.Icc_subset_Icc_right hB1)
  have hI2 : IntervalIntegrable
      (fun α : ℝ => Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) MeasureTheory.volume
      (1 / Real.log x) 1 :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hB1, Set.uIcc_of_le (le_trans hAB hB1)]
      exact Set.Icc_subset_Icc_left hAB)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hnn : 0 ≤ ∫ α in (1 / (2 * Real.log x))..(1 / Real.log x),
      Real.exp (Work.BMF.Wsup f x α (T + 1)) / α :=
    intervalIntegral.integral_nonneg hAB
      (fun t ht => div_nonneg (Real.exp_pos _).le (le_trans (le_of_lt hapos) ht.1))
  have hmono : (∫ α in (1 / Real.log x)..1,
        Real.exp (Work.BMF.Wsup f x α (T + 1)) / α)
      ≤ ∫ α in (1 / (2 * Real.log x))..1,
        Real.exp (Work.BMF.Wsup f x α (T + 1)) / α := by
    linarith [hsplit, hnn]
  have hmain := hC f hf1 hmul hb x T hx hT
  calc ‖Work.BMF.Mf f x‖
      ≤ C * (x / Real.log x) *
          ((∫ α in (1 / Real.log x)..1, Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x) := hmain
    _ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / (2 * Real.log x))..1, Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hmono]

/-- The target theorem: the `majm` bound, obtained from `casdiv_majm` by `halasz_majm_of_casdiv`. -/
theorem halasz_majm :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C₁ * x *
          ((1 + Work.BMF.mHal f x (2 * T)) * Real.exp (-(Work.BMF.mHal f x (2 * T))) +
            1 / Real.sqrt T + 1 / Real.log x) :=
  halasz_majm_of_casdiv casdiv_majm

end Work.BMF.mrlas
