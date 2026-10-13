/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-summand bound for the pure `D_z`-slots of `D_z^j D_θ (A · D_θ f)`

This file proves `summandZ_bound`, one of the two per-summand estimates consumed by
`Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDth`.  A Leibniz expansion of the level-six slot
`D_z^j D_θ (A · D_θ f)` splits into two families of summands:

* the *`M`-slots* `D_z^b D_θ^a A · D_z^{j-b} D_θ^{i-a+1} f`, in which at least one angular
  derivative falls on `A` (handled by `summandM_bound`);
* the *`Z`-slots* `D_z^b A · D_z^{j-b} D_θ f` — this file — in which all the angular
  derivatives fall on `f`; they carry the *light* weight `w/sin(2θ)^{η/2}` (the weight of the
  pure `D_z`-slots of `HkIntegrand`) rather than the full weight `W`.

## The estimate

```
(D_z^b A · D_z^{j-b}D_θ f · w/sin(2θ)^{η/2})² ≤ ptdK2 · ptdBud α A f MA z θ     (j ≤ 6, b ≤ j).
```

## The route

Write `L = w/sin(2θ)^{η/2}` for the light weight and `W` for the full weight `Wt α`.
Since `L ≤ W` on the open quadrant (`sq_light_le_sq_Wt`, i.e. `η < γ`), a slot carrying `L` is
dominated by the same slot carrying `W`, hence by `HkIntegrand α 6 ·` as soon as the slot is one
of the slots of the level-six integrand (`sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`).

The two factors of the summand have orders `b` and `(j-b)+1 = j-b+1` with `b + (j-b) ≤ j ≤ 6`
and `b ≥ 0`, so **at least one of them has order `≤ 4`**: if `b ≥ 5` then `j - b ≤ 1 ≤ 3`.  The
factor of order `≤ 4` is priced *pointwise by the norm* with `CP_price` (`(·)² ≤ CP/(γ-1)·HkSq`),
and the other factor is bounded *pointwise by the integrand* with the single-slot lemmas.  The
product of the resulting two bounds is a single summand of `ptdBud`, and `CP ≤ ptdK2`, so the
summand is dominated by `ptdK2 · ptdBud`.

The case split in the proof is therefore:

* `j - b ≤ 3`: the `f`-factor has order `≤ 4` and is priced; the `A`-factor is a pure `D_z`-slot
  of `HkIntegrand α 6 A`, which exists because `b ≤ j ≤ 6`;
* otherwise `b ≤ 4` (as `b ≥ 5` would force `j ≥ 9`), and:
  * `j - b ≤ 5`: the `A`-factor (order `≤ 4`) is priced by the norm and the `f`-factor is a mixed
    slot of `HkIntegrand α 6 f` (it exists because `1 + (j-b) ≤ 6`);
  * `j - b = 6`: then `j = 6` and `b = 0`, so the `A`-factor is `A` itself, bounded by `MA`,
    while `D_z^6 D_θ f · W` is a slot of `HkIntegrand α 7 f` — the `MA²·HkIntegrand α 7 f`
    summand of the budget.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux

open Work.Spaces

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The two `(γ-1)⁻¹`-blocks of the budget -/

/-- The `(γ-1)⁻¹ · HkSq α 6 A · HkIntegrand α 6 f`-block is a summand of the budget. -/
private theorem inv_HkSqA_mul_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ) ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr (by rw [gam_sub_one]; linarith)
  have h1 : 0 ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
    mul_nonneg (sq_nonneg MA) (HkIntegrand_nonneg α 7 f z θ)
  have h2 : 0 ≤ (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ) :=
    mul_nonneg hγ (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 A z θ))
  have heq : ptdBud α A f MA z θ
      = ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)
         + (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
        + (MA ^ 2 * HkIntegrand α 7 f z θ
           + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2) := by
    rw [ptdBud]; ring
  rw [heq]; linarith

/-- The `(γ-1)⁻¹ · HkSq α 6 f · HkIntegrand α 6 A`-block is a summand of the budget. -/
private theorem inv_HkSqf_mul_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ) ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr (by rw [gam_sub_one]; linarith)
  have h1 : 0 ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
    mul_nonneg (sq_nonneg MA) (HkIntegrand_nonneg α 7 f z θ)
  have h2 : 0 ≤ (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ) :=
    mul_nonneg hγ (mul_nonneg (HkSq_nonneg α 6 A) (HkIntegrand_nonneg α 6 f z θ))
  have heq : ptdBud α A f MA z θ
      = ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)
         + (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
        + (MA ^ 2 * HkIntegrand α 7 f z θ
           + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2) := by
    rw [ptdBud]; ring
  rw [heq]; linarith

/-- The `A`-priced block, scaled by the universal constant `CP`, is dominated by the target
`ptdK2 · ptdBud`. -/
private theorem blockA_le {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    CP * ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ))
      ≤ ptdK2 * ptdBud α A f MA z θ := by
  have h1 := mul_le_mul_of_nonneg_left (inv_HkSqA_mul_le_ptdBud hα A f MA z θ) (le_of_lt CP_pos)
  have h2 := mul_le_mul_of_nonneg_right CP_le_ptdK2 (ptdBud_nonneg hα A f MA z θ)
  linarith

/-- The `f`-priced block, scaled by the universal constant `CP`, is dominated by the target
`ptdK2 · ptdBud`. -/
private theorem blockf_le {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    CP * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
      ≤ ptdK2 * ptdBud α A f MA z θ := by
  have h1 := mul_le_mul_of_nonneg_left (inv_HkSqf_mul_le_ptdBud hα A f MA z θ) (le_of_lt CP_pos)
  have h2 := mul_le_mul_of_nonneg_right CP_le_ptdK2 (ptdBud_nonneg hα A f MA z θ)
  linarith

/-! The main estimate -/

theorem summandZ_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {j b : ℕ} (hj : j ≤ 6) (hb : b ≤ j) :
    (Work.Spaces.DzIter b A z θ * Work.Spaces.mixed (j - b) 1 f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdK2
          * Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdBud α A f MA z θ := by
  have hγnn : 0 ≤ CP / (gam α - 1) :=
    div_nonneg (le_of_lt CP_pos) (by rw [gam_sub_one]; linarith)
  -- the first factor is a `HkIntegrand α 6 A`-slot whenever `b ≤ 6`
  have hzslot : (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      ≤ HkIntegrand α 6 A z θ := sq_le_HkIntegrand_z α 6 A z θ b (by omega)
  by_cases hB : j - b ≤ 3
  · -- ### Case B: the `f`-factor has order `≤ 4` and is priced by the norm
    have hprice : (mixed (j - b) 1 f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
      CP_price α f (j - b) 1 hα hα1 hf hmf (by omega) hz ⟨hθ0, hθ1⟩
    have hsplit : (DzIter b A z θ * mixed (j - b) 1 f z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        = (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          * (mixed (j - b) 1 f z θ) ^ 2 := by ring
    rw [hsplit]
    calc (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          * (mixed (j - b) 1 f z θ) ^ 2
        ≤ HkIntegrand α 6 A z θ * (CP / (gam α - 1) * HkSq α 6 f) :=
          mul_le_mul hzslot hprice (sq_nonneg _) (HkIntegrand_nonneg α 6 A z θ)
      _ = CP * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ptdK2 * ptdBud α A f MA z θ := blockf_le hα A f MA z θ
  · -- ### `j - b ≥ 4`, so `b ≤ 4`: the `A`-factor (order `≤ 4`) is the priced one
    have hb4 : b ≤ 4 := by omega
    by_cases h5 : j - b ≤ 5
    · -- the `f`-factor is a mixed slot of `HkIntegrand α 6 f` (order `1 + (j-b) ≤ 6`)
      have hprice : (DzIter b A z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 A := by
        have h := CP_price α A b 0 hα hα1 hA hmA (by omega) hz ⟨hθ0, hθ1⟩
        simpa only [mixed_zero_right] using h
      have hfslot : (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ HkIntegrand α 6 f z θ :=
        le_trans (sq_light_le_sq_Wt hα hα1 hz hθ0 hθ1 (mixed (j - b) 1 f z θ))
          (sq_le_HkIntegrand_mixed α 6 f z θ 1 (j - b) (by norm_num) (by omega))
      have hsplit : (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          = (DzIter b A z θ) ^ 2
            * (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by ring
      rw [hsplit]
      calc (DzIter b A z θ) ^ 2
            * (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ (CP / (gam α - 1) * HkSq α 6 A) * HkIntegrand α 6 f z θ :=
            mul_le_mul hprice hfslot (sq_nonneg _)
              (mul_nonneg hγnn (HkSq_nonneg α 6 A))
        _ = CP * ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ ptdK2 * ptdBud α A f MA z θ := blockA_le hα A f MA z θ
    · -- ### `j - b = 6`, hence `j = 6` and `b = 0`: the `MA²`-slot of the budget
      have hj6 : j = 6 := by omega
      have hb0 : b = 0 := by omega
      have hMA0 : 0 ≤ MA :=
        le_trans (abs_nonneg _)
          (hMA 1 (Real.pi / 4) (by norm_num) (by linarith [Real.pi_pos])
            (by linarith [Real.pi_pos]))
      have hAsq : (A z θ) ^ 2 ≤ MA ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hMA0]
        exact hMA z θ hz hθ0 hθ1
      have hfslot : (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ HkIntegrand α 7 f z θ :=
        le_trans (sq_light_le_sq_Wt hα hα1 hz hθ0 hθ1 (mixed 6 1 f z θ))
          (sq_le_HkIntegrand_mixed α 7 f z θ 1 6 (by norm_num) (by norm_num))
      subst hb0
      subst hj6
      have hsplit : (DzIter 0 A z θ * mixed (6 - 0) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          = (A z θ) ^ 2
            * (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by
        simp only [DzIter_zero]
        ring
      rw [hsplit]
      calc (A z θ) ^ 2 * (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
            mul_le_mul hAsq hfslot (sq_nonneg _) (sq_nonneg MA)
        _ ≤ ptdBud α A f MA z θ := MAsq_mul_Hk7_le_ptdBud hα A f MA z θ
        _ ≤ ptdK2 * ptdBud α A f MA z θ :=
            le_mul_of_one_le_left (ptdBud_nonneg hα A f MA z θ) one_le_ptdK2

end Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux
