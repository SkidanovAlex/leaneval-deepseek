import Mathlib.RingTheory.PowerSeries.Substitution

namespace Commons.RingTheory.PowerSeries

theorem subst_injective_of_constantCoeff_eq_zero {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : IsUnit (PowerSeries.coeff 1 g)) :
    Function.Injective (fun f : PowerSeries R => PowerSeries.subst g f) := by
  intro f f' hff'
  have hff'' : PowerSeries.subst g f = PowerSeries.subst g f' := hff'
  have hg : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  have hQ : PowerSeries.HasSubst (g.substInvOfIsUnit hg1) :=
    PowerSeries.HasSubst.substInvOfIsUnit g hg1
  have key := congrArg (PowerSeries.subst (g.substInvOfIsUnit hg1)) hff''
  rw [PowerSeries.subst_comp_subst_apply hg hQ, PowerSeries.subst_comp_subst_apply hg hQ,
    PowerSeries.subst_substInvOfIsUnit_right g hg0 hg1,
    PowerSeries.X_subst, PowerSeries.X_subst] at key
  exact key

end Commons.RingTheory.PowerSeries
