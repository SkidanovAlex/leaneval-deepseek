import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set

/-- **Swapping the order of integration for a compactly supported datum.**

If `g` vanishes off the box `[a,b] × [c,d]` with `0 < a ≤ b` and `0 < c ≤ d < π/2`,
and is continuous on that box, then the iterated integrals of `g` over
`(0,∞) × (0,π/2)` may be interchanged.

The proof reduces both iterated set integrals to interval integrals over `[a,b]` and
`[c,d]` (using the support hypothesis: the outer and inner integrands vanish outside
`[a,b]` resp. `[c,d]`, and `[c,d] ⊆ (0,π/2)`, `[a,b] ⊆ (0,∞)`), and then applies
Fubini's theorem for interval integrals
(`MeasureTheory.intervalIntegral_intervalIntegral_swap`), the integrability input being
that `g` is continuous on the compact box. -/
theorem iter_swap_compact {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2)
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d))
    (hzero : ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → g z θ = 0) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, g z θ := by
  have hθsub : Set.Icc c d ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hzsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  -- the inner integral over `(0,π/2)` is the interval integral over `[c,d]`
  have key_inner : ∀ z, (∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ) = ∫ θ in c..d, g z θ := by
    intro z
    rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hθsub
      (fun θ hθ => hzero z θ (Or.inr hθ.2)),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  -- the inner integral over `(0,∞)` is the interval integral over `[a,b]`
  have key_outer : ∀ θ, (∫ z in Set.Ioi 0, g z θ) = ∫ z in a..b, g z θ := by
    intro θ
    rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hzsub
      (fun z hz => hzero z θ (Or.inl hz.2)),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hL : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ)
      = ∫ z in a..b, ∫ θ in c..d, g z θ := by
    have h1 : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ)
        = ∫ z in Set.Icc a b, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hzsub
        (fun z hz => by
          have hz' : ∀ θ, g z θ = 0 := fun θ => hzero z θ (Or.inl hz.2)
          simp [hz'])
    have h2 : (∫ z in Set.Icc a b, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ)
        = ∫ z in a..b, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have h3 : (∫ z in a..b, ∫ θ in Set.Ioo 0 (Real.pi / 2), g z θ)
        = ∫ z in a..b, ∫ θ in c..d, g z θ := by
      congr 1 with z
      exact key_inner z
    exact h1.trans (h2.trans h3)
  have hR : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, g z θ)
      = ∫ θ in c..d, ∫ z in a..b, g z θ := by
    have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, g z θ)
        = ∫ θ in Set.Icc c d, ∫ z in Set.Ioi 0, g z θ :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hθsub
        (fun θ hθ => by
          have hθ' : ∀ z, g z θ = 0 := fun z => hzero z θ (Or.inr hθ.2)
          simp [hθ'])
    have h2 : (∫ θ in Set.Icc c d, ∫ z in Set.Ioi 0, g z θ)
        = ∫ θ in c..d, ∫ z in Set.Ioi 0, g z θ := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
    have h3 : (∫ θ in c..d, ∫ z in Set.Ioi 0, g z θ)
        = ∫ θ in c..d, ∫ z in a..b, g z θ := by
      congr 1 with θ
      exact key_outer θ
    exact h1.trans (h2.trans h3)
  have hInt : IntegrableOn (Function.uncurry g) (Set.uIoc a b ×ˢ Set.uIoc c d) volume := by
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  exact hL.trans ((MeasureTheory.intervalIntegral_intervalIntegral_swap hInt).trans hR.symm)

end Work.FTS.EllipticEst.AeI1Fts
