import Mathlib

namespace Work.GM.Affine

/-- If `g` is integrable, bounded above by `A` everywhere and by `B / x ^ 2` for `x ≠ 0`,
then `∫ g ≤ 2 * r * A + 2 * B / r` for every `r > 0`.

The proof splits `ℝ` at `[-r, r]`: on the middle interval we use the bound `g ≤ A`, and on
the two tails we use `g ≤ B / x ^ 2` together with `∫_{|x| > r} B / x ^ 2 = 2 * B / r`. -/
theorem integral_le_two_r {g : ℝ → ℝ} {A B r : ℝ} (hr : 0 < r) (hg : MeasureTheory.Integrable g) (h1 : ∀ x, g x ≤ A) (h2 : ∀ x, x ≠ 0 → g x ≤ B / x ^ 2) : ∫ x, g x ≤ 2 * r * A + 2 * B / r := by
  set s : Set ℝ := Set.Icc (-r) r with hs_def
  have hs : MeasurableSet s := measurableSet_Icc
  -- `∫_{Ioi r} B / x^2 = B / r`, together with its integrability.
  have hIoi_int : MeasureTheory.IntegrableOn (fun x : ℝ => B / x ^ 2) (Set.Ioi r) := by
    have h1' : MeasureTheory.IntegrableOn (fun x : ℝ => B * x ^ (-2 : ℝ)) (Set.Ioi r) := by
      exact MeasureTheory.Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr) B
    exact h1'.congr_fun (fun x hx => by
      change B * x ^ (-2 : ℝ) = B / x ^ 2
      have hx0 : 0 < x := hr.trans hx
      rw [div_eq_mul_inv, ← Real.rpow_two x, ← Real.rpow_neg hx0.le (2 : ℝ)]) measurableSet_Ioi
  have hIoi_val : ∫ x in Set.Ioi r, (fun x : ℝ => B / x ^ 2) x = B / r := by
    have hcongr : Set.EqOn (fun x : ℝ => B / x ^ 2) (fun x : ℝ => B * x ^ (-2 : ℝ)) (Set.Ioi r) := by
      intro x hx
      change B / x ^ 2 = B * x ^ (-2 : ℝ)
      have hx0 : 0 < x := hr.trans hx
      rw [div_eq_mul_inv, ← Real.rpow_two x, ← Real.rpow_neg hx0.le (2 : ℝ)]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr]
    rw [show ((-2 : ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  -- The same on the negative half-line, by the substitution `x ↦ -x`.
  have hIio_int : MeasureTheory.IntegrableOn (fun x : ℝ => B / x ^ 2) (Set.Iio (-r)) := by
    have hkey := (measurableEmbedding_neg (α := ℝ)).integrableOn_map_iff
      (f := fun x : ℝ => B / x ^ 2) (s := Set.Iio (-r))
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    rw [MeasureTheory.Measure.map_neg_eq_self (MeasureTheory.volume : MeasureTheory.Measure ℝ)] at hkey
    rw [hkey]
    rw [show Neg.neg ⁻¹' Set.Iio (-r) = Set.Ioi r by
          ext x; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi, neg_lt_neg_iff]]
    simpa [Function.comp_def, Even.neg_pow (by norm_num : Even 2)] using hIoi_int
  have hIio_val : ∫ x in Set.Iio (-r), (fun x : ℝ => B / x ^ 2) x = B / r := by
    have hsym : ∫ x in Set.Iic (-r), (fun x : ℝ => B / x ^ 2) x
        = ∫ x in Set.Ioi r, (fun x : ℝ => B / x ^ 2) x := by
      rw [← integral_comp_neg_Ioi r (fun x : ℝ => B / x ^ 2)]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change B / (-x) ^ 2 = B / x ^ 2
      rw [Even.neg_pow (by norm_num : Even 2)]
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio (f := fun x : ℝ => B / x ^ 2) (x := -r)]
    rw [hsym, hIoi_val]
  have hs_compl : sᶜ = Set.Iio (-r) ∪ Set.Ioi r := by
    rw [hs_def]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ) s ≠ ⊤ := by
    rw [hs_def, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- The middle piece: `g ≤ A` on `[-r, r]`.
  have hmiddle : ∫ x in s, g x ≤ ∫ x in s, (fun _ : ℝ => A) x := by
    apply MeasureTheory.setIntegral_mono_on
    · exact hg.integrableOn
    · exact MeasureTheory.integrableOn_const hfin
    · exact hs
    · intro x _; exact h1 x
  have hmiddle_val : ∫ x in s, (fun _ : ℝ => A) x = 2 * r * A := by
    rw [MeasureTheory.setIntegral_const]
    rw [show (MeasureTheory.volume : MeasureTheory.Measure ℝ).real s = 2 * r by
          rw [hs_def, Real.volume_real_Icc_of_le (by linarith : -r ≤ r)]
          ring]
    simp only [smul_eq_mul]
  -- The tail piece: `g ≤ B / x^2` off `[-r, r]`.
  have hcompl_int : MeasureTheory.IntegrableOn (fun x : ℝ => B / x ^ 2) sᶜ := by
    rw [hs_compl]
    exact hIio_int.union hIoi_int
  have htail : ∫ x in sᶜ, g x ≤ ∫ x in sᶜ, (fun x : ℝ => B / x ^ 2) x := by
    apply MeasureTheory.setIntegral_mono_on
    · exact hg.integrableOn
    · exact hcompl_int
    · exact hs.compl
    · intro x hx
      have hx' : x < -r ∨ r < x := by
        rw [hs_compl] at hx; exact hx
      have hx0 : x ≠ 0 := by rcases hx' with h | h <;> linarith
      exact h2 x hx0
  have htail_val : ∫ x in sᶜ, (fun x : ℝ => B / x ^ 2) x = 2 * B / r := by
    rw [hs_compl]
    rw [MeasureTheory.setIntegral_union (by
          rw [Set.disjoint_left]; intro x hx hx'
          simp only [Set.mem_Iio] at hx; simp only [Set.mem_Ioi] at hx'; linarith)
        measurableSet_Ioi hIio_int hIoi_int]
    rw [hIio_val, hIoi_val]; ring
  calc ∫ x, g x = (∫ x in s, g x) + (∫ x in sᶜ, g x) :=
        (MeasureTheory.integral_add_compl hs hg).symm
    _ ≤ (∫ x in s, (fun _ : ℝ => A) x) + (∫ x in sᶜ, (fun x : ℝ => B / x ^ 2) x) :=
        add_le_add hmiddle htail
    _ = 2 * r * A + 2 * B / r := by rw [hmiddle_val, htail_val]

end Work.GM.Affine
