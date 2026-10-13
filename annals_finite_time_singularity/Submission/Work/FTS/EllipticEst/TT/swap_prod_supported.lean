import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Blocks.interp_swap_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

theorem swap_prod_supported {A B c d : ℝ} (hA : 0 < A) (hAB : A < B) (hc : 0 < c)
    (hcd : c < d) (hd : d < Real.pi / 2) {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (Set.Icc A B ×ˢ Set.Icc c d))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → f z θ = 0) :
    MeasureTheory.Integrable (Function.uncurry f)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, f z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz)
      ∧ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, f z θ := by
  -- `f` vanishes off the compact rectangle `K`, where it is continuous.
  have hK : IsCompact (Set.Icc A B ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hIntK : IntegrableOn (Function.uncurry f) (Set.Icc A B ×ˢ Set.Icc c d)
      (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hK hcont
  have hind : Integrable (Set.indicator (Set.Icc A B ×ˢ Set.Icc c d) (Function.uncurry f))
      (volume.prod volume) :=
    (integrable_indicator_iff hK.measurableSet).2 hIntK
  have hzero : ∀ p : ℝ × ℝ, p ∉ Set.Icc A B ×ˢ Set.Icc c d → Function.uncurry f p = 0 := by
    rintro ⟨z, θ⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    exact hsupp z θ hp
  have hfull : Integrable (Function.uncurry f) (volume.prod volume) :=
    hind.congr (Filter.Eventually.of_forall fun p => by
      by_cases hp : p ∈ Set.Icc A B ×ˢ Set.Icc c d
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, hzero p hp])
  -- Restrict the product measure to the domain `Iz ×ˢ Iθ`.
  have hInt : Integrable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hfull.restrict
  refine ⟨hInt, ?_, ?_⟩
  · -- Integrability of the `θ`-slices follows from Fubini for integrable functions.
    exact hInt.integral_prod_left
  · -- Fubini: swap the two iterated integrals.
    exact integral_integral_swap hInt

end Work.FTS.EllipticEst.TT
