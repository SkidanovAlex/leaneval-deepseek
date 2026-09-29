import Mathlib
import Submission.Work.Holonomy3.cleared_setup

/-!
# Substitution commutes with the vertical lift `liftV`

The `s`-th variable lift `liftV s h = h.toMvPowerSeries s` of a univariate series `h`
is `rename (fun _ : Unit ↦ s) h`.  Substituting the family `substFam Φ` (whose `t`-th
member is `liftV t (Φ t)`) into `liftV s h` therefore only sees the variable `s` and
produces `liftV s (PowerSeries.subst (Φ s) h)`.

The technical core is `PowerSeries.subst_toMvPowerSeries` (the `toMvPowerSeries i`
embedding commutes with substitution, in either direction) together with
`MvPowerSeries.subst_comp_subst_apply`.
-/

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- Substitution of the lifted series `q.toMvPowerSeries i` into `h` only involves the variable
`i`, and coincides with the lift of the univariate substitution of `q` into `h`. -/
lemma subst_toMvPowerSeries_toMvPowerSeries {σ : Type*} (i : σ) {q h : PowerSeries ℂ}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst (PowerSeries.toMvPowerSeries i q) h =
      PowerSeries.toMvPowerSeries i (PowerSeries.subst q h) := by
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => q) := hq.const
  have hb : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have key := MvPowerSeries.subst_comp_subst_apply (R := ℂ) (S := ℂ) (T := ℂ)
    (a := fun _ : Unit => q)
    (b := fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ)) ha hb (h : MvPowerSeries Unit ℂ)
  simp only [PowerSeries.subst_def, PowerSeries.toMvPowerSeries_eq_subst] at key ⊢
  exact key.symm

theorem subst_liftV {d : ℕ} (Φ : Fin d → PowerSeries ℂ)
    (hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0) (h : PowerSeries ℂ) (s : Fin d) :
    MvPowerSeries.subst (substFam Φ) (PowerSeries.toMvPowerSeries s h) =
      PowerSeries.toMvPowerSeries s (PowerSeries.subst (Φ s) h) := by
  have ha : MvPowerSeries.HasSubst (substFam Φ) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ?_)
    simp only [substFam, liftV]
    rw [PowerSeries.toMvPowerSeries_apply, MvPowerSeries.constantCoeff_rename,
      ← PowerSeries.constantCoeff_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0 t]
  have hq : PowerSeries.HasSubst (Φ s) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [← PowerSeries.constantCoeff_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0 s])
  rw [PowerSeries.subst_toMvPowerSeries ha]
  have hsf : substFam Φ s = PowerSeries.toMvPowerSeries s (Φ s) := by
    simp [substFam, liftV]
  rw [hsf]
  exact subst_toMvPowerSeries_toMvPowerSeries s hq

end

end Work.Holonomy3
