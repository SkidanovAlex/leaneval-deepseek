import Mathlib
import Submission.Work.SSGRoute.ELFDefs
import Submission.Work.SSGRoute.localField_units_pQuotient_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of `K_wˣ ⧸ p·K_wˣ` for a number field place `w`

For a number field `K`, a place `w` of `K` and a prime `p`, the quotient of the additive group
`Additive K_wˣ` attached to the unit group of the local field `K_w` by the subgroup of `p`-th
multiples (`= p`-th powers, transported through `Additive`) is finite.

This is the additive restatement of
`Work.SSGRoute.localField_units_pQuotient_finite`, which proves the finiteness of
`K_wˣ ⧸ (K_wˣ)^p` where `(K_wˣ)^p = Work.Kummer.nthPowerSubgroup p K_wˣ`.  The two subgroups
`(Work.Kummer.nthPowerSubgroup p K_wˣ).toAddSubgroup` and
`(Work.SSGRoute.nsmulAddHom p (Additive K_wˣ)).range` of `Additive K_wˣ` coincide, and finiteness
of a quotient is transported along `Subgroup.toAddSubgroup` by the index computations
`Subgroup.finiteIndex_toAddSubgroup_iff` together with
`Subgroup.finiteIndex_of_finite_quotient` / `AddSubgroup.finite_quotient_of_finiteIndex`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

noncomputable section

/-- The range of "multiplication by `p`" on `Additive G` is the additive subgroup attached to the
subgroup of `p`-th powers `Work.Kummer.nthPowerSubgroup p G` of `G`. -/
theorem range_nsmulAddHom_eq_toAddSubgroup (p : ℕ) (G : Type*) [CommGroup G] :
    (nsmulAddHom p (Additive G)).range = (Work.Kummer.nthPowerSubgroup p G).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, Work.Kummer.mem_nthPowerSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Additive.toMul b, (toMul_nsmul p b).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨Additive.ofMul g, by rw [nsmulAddHom_apply, ← ofMul_pow, hg]; rfl⟩

/-- Finiteness of the quotient `G ⧸ H` transfers to the quotient of `Additive G` by the
corresponding `AddSubgroup`. -/
theorem finite_additive_quotient_toAddSubgroup {G : Type*} [CommGroup G] (H : Subgroup G)
    (h : Finite (G ⧸ H)) : Finite (Additive G ⧸ H.toAddSubgroup) := by
  have hfi : H.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient G _ H h
  exact @AddSubgroup.finite_quotient_of_finiteIndex (Additive G) _
    H.toAddSubgroup (Subgroup.finiteIndex_toAddSubgroup_iff.mpr hfi)

/-- **Finiteness of `K_wˣ ⧸ p·K_wˣ` for a number field place `w`.**

Combines `Work.SSGRoute.localField_units_pQuotient_finite` with the identification of the range
of `nsmulAddHom p` on `Additive K_wˣ` with the additive subgroup attached to the `p`-th power
subgroup. -/
theorem localUnits_additive_pQuotient_finite (K : Type) [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) [Fact p.Prime] :
    Finite (Additive ((NK.GlobalCFT.Place.localField K w)ˣ) ⧸
      (Work.SSGRoute.nsmulAddHom p (Additive ((NK.GlobalCFT.Place.localField K w)ˣ))).range) := by
  rw [range_nsmulAddHom_eq_toAddSubgroup p ((NK.GlobalCFT.Place.localField K w)ˣ)]
  exact finite_additive_quotient_toAddSubgroup _
    (localField_units_pQuotient_finite K w p)

end

end Work.SSGRoute
