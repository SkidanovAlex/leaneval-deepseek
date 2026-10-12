import Mathlib.MeasureTheory.Integral.DominatedConvergence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

theorem continuous_parametric_intervalIntegral_general {Y : Type*} [TopologicalSpace Y]
    {a b : ℝ} {g : ℝ × Y → ℝ} (hg : Continuous g) :
    Continuous (fun y : Y => ∫ x in a..b, g (x, y)) := by
  have hf : Continuous (Function.uncurry fun y x => g (x, y)) := by
    show Continuous fun p : Y × ℝ => g (p.2, p.1)
    exact hg.comp (continuous_snd.prodMk continuous_fst)
  simpa using intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y x => g (x, y)) hf a b

end Commons.Analysis.Fourier