import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory

/-- If the average of `‖f - c‖` on `a i` tends to `0`, and `w i` is supported in `a i` with
integral tending to `1` and pointwise norm bounded by `K / μ.real (a i)`, then the integrals
`∫ y, w i y * f y` tend to `c`. -/
theorem tendsto_integral_mul_of_tendsto_average_norm_sub
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {ι : Type*} {a : ι → Set α} {l : Filter ι} {f : α → ℂ} {c : ℂ} {w : ι → α → ℂ} (K : ℝ)
    (hf : Filter.Tendsto (fun i => ⨍ y in a i, ‖f y - c‖ ∂μ) l (nhds 0))
    (f_int : ∀ᶠ i in l, MeasureTheory.IntegrableOn f (a i) μ)
    (hw : Filter.Tendsto (fun i => ∫ y, w i y ∂μ) l (nhds 1))
    (w_supp : ∀ᶠ i in l, Function.support (w i) ⊆ a i)
    (w_bound : ∀ᶠ i in l, ∀ x, ‖w i x‖ ≤ K / μ.real (a i)) :
    Filter.Tendsto (fun i => ∫ y, w i y * f y ∂μ) l (nhds c) := by
  have w_ne : ∀ᶠ i in l, ∫ y, w i y ∂μ ≠ 0 :=
    hw.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  have w_int : ∀ᶠ i in l, MeasureTheory.Integrable (w i) μ := by
    filter_upwards [w_ne] with i hi
    by_contra h
    exact hi (MeasureTheory.integral_undef h)
  have I : ∀ᶠ i in l,
      ∫ y, w i y * (f y - c) ∂μ + (∫ y, w i y ∂μ) * c = ∫ y, w i y * f y ∂μ := by
    filter_upwards [f_int, w_int, w_supp, w_bound] with i hif hiw hisupp hibound
    rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_add]
    · simp only [mul_sub, sub_add_cancel]
    · simp_rw [mul_sub]
      refine MeasureTheory.Integrable.sub ?_ (hiw.mul_const c)
      have A : Function.support (fun y => w i y * f y) ⊆ a i :=
        fun x hx => hisupp (Function.support_mul_subset_left (w i) f hx)
      rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset A]
      exact MeasureTheory.Integrable.mul_of_top_right hif
        (MeasureTheory.memLp_top_of_bound hiw.aestronglyMeasurable.restrict (K / μ.real (a i))
          (Filter.Eventually.of_forall hibound))
    · exact hiw.mul_const c
  have L0 : Filter.Tendsto (fun i => ∫ y, w i y * (f y - c) ∂μ) l (nhds 0) := by
    have hK : Filter.Tendsto (fun i => K * ⨍ y in a i, ‖f y - c‖ ∂μ) l (nhds 0) := by
      have h := hf.const_mul K
      simpa only [mul_zero] using h
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [w_supp, w_bound, f_int, w_ne] with i hisupp hibound hif hi0
    have mu_ai : μ (a i) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      rw [MeasureTheory.measureReal_def, h, ENNReal.toReal_top, div_zero] at hibound
      have h0 : w i = 0 :=
        funext fun x => norm_eq_zero.mp (le_antisymm (hibound x) (norm_nonneg _))
      exact hi0 (by rw [h0]; simp)
    have hzero : ∀ x, x ∉ a i → ‖w i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have hx0 : w i x = 0 := by
        rw [← Function.notMem_support]
        exact fun h => hx (hisupp h)
      simp [hx0]
    calc ‖∫ y, w i y * (f y - c) ∂μ‖
        ≤ ∫ y, ‖w i y‖ * ‖f y - c‖ ∂μ := by
          simpa only [norm_mul] using
            MeasureTheory.norm_integral_le_integral_norm (fun y => w i y * (f y - c))
      _ = ∫ y in a i, ‖w i y‖ * ‖f y - c‖ ∂μ :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
            (f := fun y => ‖w i y‖ * ‖(f y - c)‖) hzero).symm
      _ ≤ ∫ y in a i, (K / μ.real (a i)) * ‖f y - c‖ ∂μ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => by positivity)) ?_
            (Filter.Eventually.of_forall (fun x => ?_))
          · apply (MeasureTheory.Integrable.sub hif _).norm.const_mul
            change MeasureTheory.IntegrableOn (fun _ => c) (a i) μ
            simp [mu_ai]
          · dsimp only
            gcongr
            simpa using hibound x
      _ = K * ⨍ y in a i, ‖f y - c‖ ∂μ := by
          rw [MeasureTheory.setAverage_eq μ (fun y => ‖f y - c‖) (a i), smul_eq_mul]
          conv_lhs => rw [MeasureTheory.integral_const_mul]
          rw [div_eq_mul_inv, mul_assoc]
  have := L0.add (hw.mul_const c)
  simp only [one_mul, zero_add] at this
  exact Filter.Tendsto.congr' I this

end Work.MRMT.Found
