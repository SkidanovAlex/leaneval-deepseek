import Mathlib.MeasureTheory.Integral.Pi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem prod_integral_unitCube (h : Fin 3 → ℝ → ℂ) :
    ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
        (∏ i, h i (y i))
      = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2), h i t := by
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi,
      MeasureTheory.integral_fintype_prod_eq_prod]

end Work.BoseB4
