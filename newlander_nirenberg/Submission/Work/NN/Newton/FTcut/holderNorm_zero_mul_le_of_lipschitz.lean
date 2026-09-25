import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.holderNorm_zero_mul_le

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.FTcut

/-! ## Multiplying by a bounded Lipschitz factor

If `χ` is bounded by `1` and globally `L`-Lipschitz, then the `C^{0,α}`-norm of the product
`x ↦ χ x * u x` is bounded by `(L + 3)` times the `C^{0,α}`-norm of `u`, for `0 < α ≤ 1`.

The pointwise content is that the `C^{0,α}`-norm of `χ` itself is at most `L + 3`:
the sup part is at most `1` by the bound `‖χ‖ ≤ 1`, and the Hölder part is at most `max L 2`
because on scales `‖x - y‖ ≤ 1` the Lipschitz bound gives `‖χ x - χ y‖ ≤ L ‖x - y‖^{1-α} ≤ L`,
while on scales `‖x - y‖ ≥ 1` the bound `‖χ‖ ≤ 1` gives `‖χ x - χ y‖ ≤ 2 ≤ 2 ‖x - y‖^α`.
The statement then follows from submultiplicativity of the `C^{0,α}`-norm. -/

/-- At order `0` the "derivative" is the function itself, so the norm of the difference of the
two `0`-th iterated derivatives is the norm of the difference of the values. -/
private lemma norm_iteratedFDerivWithin_zero_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f x - f y‖) (norm_nonneg _) fun m => ?_
    rw [sub_apply, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]
    rw [show (∏ i : Fin 0, ‖m i‖) = 1 from by simp, mul_one]
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y)
      (fun _ : Fin 0 => (0 : X))
    simpa only [sub_apply, iteratedFDerivWithin_zero_apply,
      Finset.univ_eq_empty, Finset.prod_empty, mul_one] using h

/-- The Hölder seminorm of order `α` of a function that is bounded by `1` and globally
`L`-Lipschitz is at most `max L 2`. -/
private lemma holderSeminorm_zero_le_of_lipschitz {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {α L : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    {χ : X → ℂ} {Ω : Set X}
    (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hχlip : ∀ x y, ‖χ x - χ y‖ ≤ L * ‖x - y‖) :
    Work.CR.Flat.holderSeminorm 0 α χ Ω ≤ ENNReal.ofReal (max L 2) := by
  rw [Work.CR.Flat.holderSeminorm]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [norm_iteratedFDerivWithin_zero_sub χ Ω x y]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hden_pos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hnorm_pos α
  rcases lt_or_ge ‖x - y‖ 1 with hlt | hge
  · have hd : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
      rw [Real.rpow_sub hnorm_pos, Real.rpow_one]
    calc ‖χ x - χ y‖ / ‖x - y‖ ^ α
        ≤ (L * ‖x - y‖) / ‖x - y‖ ^ α := div_le_div_of_nonneg_right (hχlip x y) hden_pos.le
      _ = L * (‖x - y‖ / ‖x - y‖ ^ α) := by rw [mul_div_assoc]
      _ = L * ‖x - y‖ ^ (1 - α) := by rw [hd]
      _ ≤ L * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one (norm_nonneg _) hlt.le (by linarith)) hL
      _ = L := mul_one L
      _ ≤ max L 2 := le_max_left _ _
  · have h2 : ‖χ x - χ y‖ ≤ 2 := by
      have := norm_sub_le (χ x) (χ y); linarith [hχ1 x, hχ1 y]
    have hden1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hge hα0.le
    calc ‖χ x - χ y‖ / ‖x - y‖ ^ α
        ≤ 2 / ‖x - y‖ ^ α := div_le_div_of_nonneg_right h2 hden_pos.le
      _ ≤ 2 / 1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden1
      _ = 2 := by norm_num
      _ ≤ max L 2 := le_max_right _ _

/-- The `C^{0,α}`-norm of a function that is bounded by `1` and globally `L`-Lipschitz
is at most `L + 3`. -/
private lemma holderNorm_zero_le_of_lipschitz {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {α L : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    {χ : X → ℂ} {Ω : Set X}
    (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hχlip : ∀ x y, ‖χ x - χ y‖ ≤ L * ‖x - y‖) :
    Work.CR.Flat.holderNorm 0 α χ Ω ≤ ENNReal.ofReal (L + 3) := by
  have h_iter : Work.CR.Flat.iterDerivNorm 0 χ Ω ≤ (1 : ℝ≥0∞) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun x hx => ?_
    exact le_trans (ENNReal.ofReal_le_ofReal (hχ1 x)) (le_of_eq ENNReal.ofReal_one)
  have h_sem : Work.CR.Flat.holderSeminorm 0 α χ Ω ≤ ENNReal.ofReal (max L 2) :=
    holderSeminorm_zero_le_of_lipschitz hα0 hα1 hL hχ1 hχlip
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  refine le_trans (add_le_add h_iter h_sem) ?_
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (le_trans hL (le_max_left L 2))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmax : max L 2 ≤ L + 2 := max_le (by linarith) (by linarith)
  linarith

/-- Multiplying a function by a factor `χ` that is bounded by `1` and globally `L`-Lipschitz
increases its `C^{0,α}`-norm (on any subset, for `0 < α ≤ 1`) by at most the factor `L + 3`. -/
theorem holderNorm_zero_mul_le_of_lipschitz {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {α L : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    {χ u : X → ℂ} {Ω : Set X}
    (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hχlip : ∀ x y, ‖χ x - χ y‖ ≤ L * ‖x - y‖) :
    Work.CR.Flat.holderNorm 0 α (fun x => χ x * u x) Ω
      ≤ ENNReal.ofReal (L + 3) * Work.CR.Flat.holderNorm 0 α u Ω := by
  have hchi := holderNorm_zero_le_of_lipschitz (Ω := Ω) (χ := χ) hα0 hα1 hL hχ1 hχlip
  exact le_trans (Work.NN.Final.holderNorm_zero_mul_le χ u Ω) (mul_le_mul' hchi le_rfl)

end Work.NN.Newton.FTcut
