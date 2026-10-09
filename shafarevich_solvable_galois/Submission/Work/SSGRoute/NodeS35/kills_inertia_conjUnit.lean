import Mathlib
import Submission.Work.SSGRoute.H9.swChainConjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS35

open scoped Pointwise

/-- **The "kills the inertia" confinement is invariant under simultaneous conjugation of the place
`A` and the class `b` by `galLift K σ`.**

If the Kummer cochain `χ_b` of `b ∈ Kˣ` kills the inertia of every finite place `B` that is not
`K`-conjugate to `A` (its inertial elements fixing `K`), then the Kummer cochain of the conjugate
class `b^{σ̃}` (`σ̃ := galLift K σ`) kills the inertia of every finite place that is not
`K`-conjugate to `σ̃ • A`.

The transfer mirrors the transport `swGesKConj_galLift_smul_iff` of the conjugacy confinement: a
place `B` outside the `K`-class of `σ̃ • A` pulls back to the place `σ̃⁻¹ • B` outside the
`K`-class of `A`, an inertial element `u` fixing `K` pulls back to the inertial element
`σ̃⁻¹ u σ̃` fixing `K` (`isInertia_conj`, `galLift_conj_mem_fixingSubgroup`, `isFinPlace_smul_iff`),
and the Kummer cochain of the conjugate class at `u` is the Kummer cochain of `b` at `σ̃⁻¹ u σ̃`
(`swConjElemZero`). -/
theorem kills_inertia_conjUnit {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (σ : K ≃ₐ[k] K) (A : ValuationSubring Ω)
    (h : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ¬ Work.SSGRoute.gesKConj K A B →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      ¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.galLift K σ • A) B →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) b) u = 0 := by
  intro B hB hnotB u huK huI
  -- Reduce to the cochain of `b` at the conjugate inertial element `σ̃⁻¹ u σ̃`, `σ̃ := galLift K σ`.
  refine (Work.SSGRoute.H9.swConjElemZero (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
    (b := b) (σ := Work.SSGRoute.ZDataMup.galLift K σ) (τ := u)).mpr ?_
  -- The pulled-back place and inertial element.
  have hB0 : SSGRoute.IsFinPlace k ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • B) :=
    (Work.SSGRoute.isFinPlace_smul_iff B ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹)).mpr hB
  have hnotB0 : ¬ Work.SSGRoute.gesKConj K A
      ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • B) :=
    fun hc => hnotB
      ((Work.SSGRoute.H9.swGesKConj_galLift_smul_iff (K := K) σ A B).mpr hc)
  have hmem0 : (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * u * Work.SSGRoute.ZDataMup.galLift K σ
      ∈ K.fixingSubgroup :=
    Work.SSGRoute.H9.galLift_conj_mem_fixingSubgroup (K := K) σ huK
  have hI0 : SSGRoute.IsInertia k ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • B)
      ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * u * Work.SSGRoute.ZDataMup.galLift K σ) :=
    (Work.SSGRoute.isInertia_conj B ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹) u).mpr huI
  exact h _ hB0 hnotB0 _ hmem0 hI0

end Work.SSGRoute.NodeS35
