import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

open MeasureTheory in
/-- **Hölder's inequality for a translated product**: the norm of the Bochner integral of
`y ↦ f (x - y) * g y` is bounded by the product of the `L^p` norm of `f` and the `L^q` norm of `g`
whenever `p` and `q` are Hölder conjugates.  The point is that the translated copy
`y ↦ f (x - y)` has the same `L^p` norm as `f` (Haar invariance of Lebesgue measure). -/
theorem integral_norm_mul_sub_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {p q : ℝ} (hpq : Real.HolderConjugate p q) {f g : V → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) (volume : Measure V))
    (hg : MemLp g (ENNReal.ofReal q) (volume : Measure V)) (x : V) :
    ‖∫ y, f (x - y) * g y‖
      ≤ (∫ y, ‖f y‖ ^ p) ^ (1 / p) * (∫ y, ‖g y‖ ^ q) ^ (1 / q) := by
  have hmp : MeasurePreserving (fun y : V => x - y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hmem : MemLp (fun y : V => f (x - y)) (ENNReal.ofReal p) (volume : Measure V) :=
    hf.comp_measurePreserving hmp
  calc
    ‖∫ y, f (x - y) * g y‖ ≤ ∫ y, ‖f (x - y) * g y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖f (x - y)‖ * ‖g y‖ := by simp_rw [norm_mul]
    _ ≤ (∫ y, ‖f (x - y)‖ ^ p) ^ (1 / p) * (∫ y, ‖g y‖ ^ q) ^ (1 / q) :=
        integral_mul_norm_le_Lp_mul_Lq hpq hmem hg
    _ = (∫ y, ‖f y‖ ^ p) ^ (1 / p) * (∫ y, ‖g y‖ ^ q) ^ (1 / q) := by
        rw [integral_sub_left_eq_self (fun z : V => ‖f z‖ ^ p) volume x]

end Commons.Analysis.Integral