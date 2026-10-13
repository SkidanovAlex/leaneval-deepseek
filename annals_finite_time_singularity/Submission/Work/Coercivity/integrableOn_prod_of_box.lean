import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

set_option autoImplicit false
-- `hc` is kept as a hypothesis for compatibility with the caller's statement; the
-- argument below does not need it (the box `[c,d] × [0,π/2]` is compact for any `c ≤ d`).
set_option linter.unusedVariables false

/-- If `G` is continuous on the box `[c,d] × [0,π/2]` and vanishes on the domain
`[0,∞) × [0,π/2]` outside that box, then `G` is integrable on the domain.

Indeed, `uncurry G` agrees on the domain with `(Icc c d ×ˢ Iθ).piecewise (uncurry G) 0`,
which is integrable because the box is compact (so `G` is bounded on it) and has
finite Lebesgue measure. -/
theorem integrableOn_prod_of_box {G : ℝ → ℝ → ℝ} {c d : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn (Function.uncurry G) (Set.Icc c d ×ˢ Spaces.Iθ))
    (hzero : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, z ∉ Set.Icc c d → G z θ = 0) :
    MeasureTheory.IntegrableOn (Function.uncurry G) (Spaces.Iz ×ˢ Spaces.Iθ) := by
  classical
  have hBmeas : MeasurableSet (Set.Icc c d ×ˢ Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hAmeas : MeasurableSet (Spaces.Iz ×ˢ Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  -- `G` is bounded on the compact box
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  -- the box has finite Lebesgue measure
  have hBfin : volume (Set.Icc c d ×ˢ Spaces.Iθ) < ⊤ := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp only [Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- hence `uncurry G` is integrable on the box
  have hIntB : MeasureTheory.IntegrableOn (Function.uncurry G) (Set.Icc c d ×ˢ Spaces.Iθ) := by
    refine IntegrableOn.of_bound hBfin (hcont.aestronglyMeasurable hBmeas) C ?_
    rw [MeasureTheory.ae_restrict_iff' hBmeas]
    exact Filter.Eventually.of_forall fun x hx => hC x hx
  -- and therefore so is the function which is `uncurry G` on the box and `0` off it
  have hpw : Integrable ((Set.Icc c d ×ˢ Spaces.Iθ).piecewise (Function.uncurry G) 0) volume :=
    Integrable.piecewise hBmeas hIntB integrableOn_zero
  -- which agrees with `uncurry G` on the whole domain, by the support hypothesis
  refine (hpw.integrableOn).congr_fun ?_ hAmeas
  rintro ⟨z, θ⟩ hx
  obtain ⟨hzIz, hθIθ⟩ := hx
  by_cases hb : (z, θ) ∈ Set.Icc c d ×ˢ Spaces.Iθ
  · rw [Set.piecewise_eq_of_mem _ _ _ hb]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hb]
    exact (hzero z hzIz θ hθIθ (fun hz => hb ⟨hz, hθIθ⟩)).symm

end Work.Coercivity
