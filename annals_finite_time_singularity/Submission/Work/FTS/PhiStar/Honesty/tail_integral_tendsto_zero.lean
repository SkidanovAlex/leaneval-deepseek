import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- `hg` is consumed by `MeasureTheory.tendsto_integral_Ioi_zero`, which only needs *some* half-line
-- on which `g` is integrable; the hypothesis is not otherwise named in the proof term.
set_option linter.unusedVariables false in
theorem tail_integral_tendsto_zero {g : ℝ → ℝ} (hg : MeasureTheory.IntegrableOn g (Set.Ioi 1)) :
    Filter.Tendsto (fun n : ℕ => ∫ t in Set.Ioi (n : ℝ), g t) Filter.atTop (nhds 0) := by
  -- The tail integrals `∫_{Ioi n} g` are the integrals of `g` over the decreasing family of
  -- half-lines `Ioi n`, whose intersection is empty; this is the "absolute continuity of the
  -- integral" theorem in its monotone-set form (Mathlib has it as
  -- `MeasureTheory.tendsto_integral_Ioi_zero`).
  exact MeasureTheory.tendsto_integral_Ioi_zero (f := g) (b := fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop

end Work.FTS.PhiStar.Honesty
