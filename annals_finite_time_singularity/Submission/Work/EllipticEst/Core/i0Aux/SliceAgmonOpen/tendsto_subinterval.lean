import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

open MeasureTheory Filter

/-- If `g` is integrable on `(0, π/2)`, `a n → 0⁺` and `b n → (π/2)⁻`, then the
integrals of `g` over the shrinking intervals `(a n, b n)` converge to the integral
over `(0, π/2)`.  This is the Lebesgue dominated convergence theorem applied to the
indicator functions of `(a n, b n)` on the measure space `(0, π/2)`. -/
theorem tendsto_subinterval {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℕ → ℝ}
    (ha : Filter.Tendsto a Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hb : Filter.Tendsto b Filter.atTop (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
    (hab : ∀ᶠ n in Filter.atTop, a n < b n) :
    Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioo (a n) (b n), g x) Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2), g x)) := by
  set S : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  have hgon : MeasureTheory.Integrable g (volume.restrict S) := by
    rw [hS]; exact hg
  -- eventually the intervals `(a n, b n)` are contained in `(0, π/2)`
  have hgood : ∀ᶠ n in Filter.atTop, 0 ≤ a n ∧ b n ≤ Real.pi / 2 := by
    filter_upwards [ha self_mem_nhdsWithin, hb self_mem_nhdsWithin] with n han hbn
    exact ⟨le_of_lt han, le_of_lt hbn⟩
  -- the restricted integrals coincide with the integrals over `(a n, b n)`
  have hInt : ∀ᶠ n in Filter.atTop,
      (∫ x in S, (Set.Ioo (a n) (b n)).indicator g x) = ∫ x in Set.Ioo (a n) (b n), g x := by
    filter_upwards [hgood] with n hn
    have hsub : Set.Ioo (a n) (b n) ⊆ S := by
      intro x hx
      exact ⟨hn.1.trans_lt hx.1, hx.2.trans_le hn.2⟩
    have h1 : (∫ x in Set.Ioo (a n) (b n), (Set.Ioo (a n) (b n)).indicator g x)
        = ∫ x in Set.Ioo (a n) (b n), g x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => Set.indicator_of_mem hx g)
    rw [← h1]
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSmeas hsub
      (fun x hx => Set.indicator_of_notMem hx.2 g)
  -- dominated convergence on the restricted measure space
  have hmain : Filter.Tendsto
      (fun n => ∫ x, (Set.Ioo (a n) (b n)).indicator g x ∂(volume.restrict S))
      Filter.atTop (nhds (∫ x, g x ∂(volume.restrict S))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => hgon.aestronglyMeasurable.indicator measurableSet_Ioo) hgon.norm
      (fun n => Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self g x)) ?_
    rw [MeasureTheory.ae_restrict_iff' hSmeas]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hax : ∀ᶠ n in Filter.atTop, a n < x :=
      ha (nhdsWithin_le_nhds (Iio_mem_nhds hx.1))
    have hbx : ∀ᶠ n in Filter.atTop, x < b n :=
      hb (nhdsWithin_le_nhds (Ioi_mem_nhds hx.2))
    have heq : (fun _ : ℕ => g x) =ᶠ[Filter.atTop]
        (fun n => (Set.Ioo (a n) (b n)).indicator g x) := by
      filter_upwards [hax, hbx] with n hn1 hn2
      have hmem : x ∈ Set.Ioo (a n) (b n) := ⟨hn1, hn2⟩
      exact (Set.indicator_of_mem hmem g).symm
    exact Filter.Tendsto.congr' heq tendsto_const_nhds
  have hmain' : Filter.Tendsto (fun n => ∫ x in S, (Set.Ioo (a n) (b n)).indicator g x)
      Filter.atTop (nhds (∫ x in Set.Ioo 0 (Real.pi / 2), g x)) := by
    simpa [hS] using hmain
  exact Filter.Tendsto.congr' hInt hmain'

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
