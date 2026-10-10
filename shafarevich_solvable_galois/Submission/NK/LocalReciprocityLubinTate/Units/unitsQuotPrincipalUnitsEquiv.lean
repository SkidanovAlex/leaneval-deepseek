import Mathlib.NumberTheory.LocalField.Basic
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Units

open scoped ValuativeRel

/-- **The quotient of the units of the ring of integers by the higher principal units.**

For a nonarchimedean local field `F` with ring of integers `𝒪[F]` and maximal ideal `𝔪[F]`, the
reduction map `𝒪[F]ˣ →* (𝒪[F] ⧸ 𝔪[F]^n)ˣ` is surjective with kernel precisely the group
`U^n = 1 + 𝔪[F]^n` of higher principal units.  Hence
`𝒪[F]ˣ ⧸ U^n ≃* (𝒪[F] ⧸ 𝔪[F]^n)ˣ`.

This is the standard identification underlying the description of the reciprocity map on units,
cf. Serre, *Local Fields*, Ch. IV §1: the filtration `U^n` is exactly the kernel filtration of the
reduction maps onto the unit groups of the truncated integer rings. -/
theorem unitsQuotPrincipalUnitsEquiv (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    Nonempty (((ValuativeRel.valuation F).integer)ˣ ⧸
      NK.LocalReciprocityLubinTate.principalUnits F n ≃*
      (((ValuativeRel.valuation F).integer ⧸
        NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n))ˣ) := by
  let R := ↥(ValuativeRel.valuation F).integer
  let I : Ideal R := NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F
  -- the reduction map on units
  let f : Rˣ →* (R ⧸ I ^ n)ˣ := Units.map (Ideal.Quotient.mk (I ^ n))
  -- its kernel is the group of higher principal units
  have hker : NK.LocalReciprocityLubinTate.principalUnits F n = f.ker := by
    ext u
    rw [MonoidHom.mem_ker]
    rw [Units.ext_iff, Units.coe_map]
    show (u ∈ NK.LocalReciprocityLubinTate.principalUnits F n) ↔
      (Ideal.Quotient.mk (I ^ n) (u : R) : R ⧸ I ^ n) = ↑(1 : (R ⧸ I ^ n)ˣ)
    rw [Units.val_one, ← map_one (Ideal.Quotient.mk (I ^ n)), Ideal.Quotient.eq]
    rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff]
  -- it is surjective: `𝒪[F]` is local, so a unit of the truncation lifts to a unit of `𝒪[F]`
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hn : n = 0
    · -- `𝔪^0 = ⊤`, both sides of the reduction are trivial
      subst hn
      have hsub : Subsingleton (R ⧸ I ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        exact Ideal.Quotient.subsingleton_iff.mpr rfl
      exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I ^ n) (y : R ⧸ I ^ n)
      have hua : IsUnit a := by
        have h1 : IsUnit ((Ideal.Quotient.mk (I ^ n)) a) := by rw [ha]; exact y.isUnit
        have h2 : a ∉ I := (Ideal.Quotient.isUnit_mk_pow_iff_notMem I hn).mp h1
        dsimp only [I, R] at h2 ⊢
        exact IsLocalRing.notMem_maximalIdeal.mp h2
      obtain ⟨u, hu⟩ := hua
      refine ⟨u, ?_⟩
      apply Units.ext
      rw [Units.coe_map, hu]
      exact ha
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

end NK.LocalReciprocityLubinTate.Units
