import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.StrongEps.E4R3.Nblock6.Tools

/-- **The mixed-slot summand of the level-`6` product bound.**  Every first-order slot
`D_z^bD_θ^a A · D_z^{j-b}D_θ^{i-a+1}f · W` of the Leibniz expansion of `D_z^jD_θ^i(A · D_θ f)`
(with `i ≥ 1`, `i + j ≤ 6`) is priced against the budget `ptdBud`.

The proof is a case analysis on the `θ`-order `a` of the `A`-slot and the total order
`a + b` of the `A`-slot.  Exactly one of the two factors carries the weight `W`:

* `a + b = 0`: the `A`-slot is `A` itself, so `|A| ≤ MA` and the `f`-slot
  `D_θ^{i+1}f` (order `≤ 7`) is absorbed by `MA²·HkIntegrand 7 f`;
* `1 ≤ a + b ≤ 4`: the `A`-slot is priced by the pointwise price `CP_price`
  (order `≤ 4`) and the `f`-slot (order `≤ 6`) carries `W`, giving `HkIntegrand 6 f`;
* `a + b ≥ 5`, `a = 0`: forced to be the exceptional slot `D_z⁵A · D_θ²f · W`
  (`i = 1`, `j = b = 5`), which is a summand of the budget;
* `a + b ≥ 5`, `a ≥ 1`: the `A`-slot (θ-order `≥ 1`, order `≤ 6`) carries `W` and
  the `f`-slot has order `≤ 7 - 5 = 2`, so it is priced by `CP_price`. -/
theorem summandM_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) (ha : a ≤ i) (hb : b ≤ j) :
    (Work.Spaces.mixed b a A z θ * Work.Spaces.mixed (j - b) (i - a + 1) f z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdK2
          * Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdBud α A f MA z θ := by
  have hγpos : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγnn : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγpos.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hbud : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hKpos : 0 < ptdK2 := ptdK2_pos
  have hK1 : 1 ≤ ptdK2 := one_le_ptdK2
  have hshape1 : (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
      = (mixed b a A z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 := by
    ring
  have hshape2 : (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
      = (mixed b a A z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ) ^ 2 := by
    ring
  rcases Nat.eq_zero_or_pos (a + b) with hp0 | hppos
  · -- the `A`-slot is `A` itself
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0
    subst hb0
    have hY : (mixed j (i + 1) f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 7 f z θ :=
      sq_le_HkIntegrand_mixed α 7 f z θ (i + 1) j (by omega) (by omega)
    have hA2 : (A z θ) ^ 2 ≤ MA ^ 2 := by
      have hh := abs_le.mp (hMA z θ hz hθ0 hθ1)
      nlinarith [hh.1, hh.2]
    rw [hshape1]
    calc (A z θ) ^ 2 * (mixed j (i + 1) f z θ * Wt α z θ) ^ 2
        ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
          mul_le_mul hA2 hY (sq_nonneg _) (sq_nonneg MA)
      _ ≤ ptdBud α A f MA z θ := MAsq_mul_Hk7_le_ptdBud hα A f MA z θ
      _ ≤ ptdK2 * ptdBud α A f MA z θ := le_mul_of_one_le_left hbud hK1
  · by_cases hp4 : a + b ≤ 4
    · -- the `A`-slot is priced pointwise, the `f`-slot carries the weight
      have hYq : (i - a + 1) + (j - b) ≤ 6 := by omega
      have hY : (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
          ≤ HkIntegrand α 6 f z θ :=
        sq_le_HkIntegrand_mixed α 6 f z θ (i - a + 1) (j - b) (by omega) hYq
      have hX : (mixed b a A z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 A :=
        CP_price α A b a hα hα1 hA hmA (by omega) hz hθmem
      rw [hshape1]
      calc (mixed b a A z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
          ≤ (CP / (gam α - 1) * HkSq α 6 A) * HkIntegrand α 6 f z θ :=
            mul_le_mul hX hY (sq_nonneg _)
              (mul_nonneg (div_nonneg CP_pos.le hγpos.le) (HkSq_nonneg α 6 A))
        _ = CP * ((gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ ptdK2 * ((gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_right CP_le_ptdK2
              (mul_nonneg (mul_nonneg hγnn (HkSq_nonneg α 6 A))
                (HkIntegrand_nonneg α 6 f z θ))
        _ ≤ ptdK2 * ptdBud α A f MA z θ :=
            mul_le_mul_of_nonneg_left (inv_hA_mul_Hk6f_le_ptdBud hα A f MA z θ) hKpos.le
    · by_cases ha0 : a = 0
      · -- the exceptional slot `D_z⁵A · D_θ²f · W`
        have hb5 : b = 5 := by omega
        have hi1 : i = 1 := by omega
        have hj5 : j = 5 := by omega
        subst ha0
        subst hb5
        subst hi1
        subst hj5
        have he : (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2
            ≤ ptdK2 * ptdBud α A f MA z θ :=
          le_trans (exc_le_ptdBud hα A f MA z θ) (le_mul_of_one_le_left hbud hK1)
        simpa using he
      · -- the `A`-slot carries the weight (θ-order `≥ 1`), the `f`-slot is priced
        have hX : (mixed b a A z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 A z θ :=
          sq_le_HkIntegrand_mixed α 6 A z θ a b (by omega) (by omega)
        have hYq : (i - a + 1) + (j - b) ≤ 4 := by omega
        have hY : (mixed (j - b) (i - a + 1) f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
          CP_price α f (j - b) (i - a + 1) hα hα1 hf hmf hYq hz hθmem
        rw [hshape2]
        calc (mixed b a A z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ) ^ 2
            ≤ HkIntegrand α 6 A z θ * (CP / (gam α - 1) * HkSq α 6 f) :=
              mul_le_mul hX hY (sq_nonneg _) (HkIntegrand_nonneg α 6 A z θ)
          _ = CP * ((gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ) := by
              rw [div_eq_mul_inv]; ring
          _ ≤ ptdK2 * ((gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ) :=
              mul_le_mul_of_nonneg_right CP_le_ptdK2
                (mul_nonneg (mul_nonneg hγnn (HkSq_nonneg α 6 f))
                  (HkIntegrand_nonneg α 6 A z θ))
          _ ≤ ptdK2 * ptdBud α A f MA z θ :=
              mul_le_mul_of_nonneg_left (inv_hf_mul_Hk6A_le_ptdBud hα A f MA z θ) hKpos.le

end Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux
