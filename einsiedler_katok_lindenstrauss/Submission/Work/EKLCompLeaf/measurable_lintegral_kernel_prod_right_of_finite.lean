import Mathlib

namespace Work.EKLCompLeaf

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped MeasureTheory ENNReal Topology

/-- Auxiliary lemma: the lintegral against a kernel (each `κ a` a finite measure) of the indicator
of a constant on a measurable set is measurable. This is the finite version of
`Kernel.measurable_lintegral_indicator_const` which is stated for s-finite kernels. -/
theorem measurable_lintegral_indicator_const_of_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {κ : Kernel α β} {t : Set (α × β)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) (hκ : ∀ a, IsFiniteMeasure (κ a)) :
    Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a := by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ) c

theorem measurable_lintegral_kernel_prod_right_of_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {κ : ProbabilityTheory.Kernel α β}
    (hκ : ∀ a, MeasureTheory.IsFiniteMeasure (κ a)) {f : α → β → ENNReal}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun a => MeasureTheory.lintegral (κ a) (fun b => f a b) := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox (uncurry f)
  have h : ∀ a, ⨆ n, F n a = uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox (uncurry f) hij _
  simp_rw [this]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun f => Measurable (fun (a : α) => ∫⁻ (b : β), f (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const_of_finite ht c hκ
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext1 a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂

end Work.EKLCompLeaf
