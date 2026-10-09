import Mathlib
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer pairing vanishes at an even count

`Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count` computes the local Kummer pairing at a finite
place `A` when the `A`-adic count of the **second** class is odd:

  `oPairAt_A (χ_α) (χ_β) = χ_α ψ` for a Frobenius `ψ` pinned at `A`,

the count factor being `1` in `ZMod 2`.  This file records the complementary half, which is what the
*split* half of Schmidt--Wingberg's p. 16 dichotomy consumes (`(x,a)_P · (x,a)_{σP} = (-1,a)_P`, and
`(-1,a)_P = 1` because the count of `a` at `P` is even):

  if the count of `β` at `A` is **even**, then `oPairAt_A (χ_α) (χ_β) = 0`.

Both are immediate from the unramified pairing-value dictionary `swPairingValueFrob`, whose
right-hand side is `count_A(β) • χ_α ψ`.

This is the local-arithmetic companion of the corrected `ρ`-fixed squareness
(`Work.SSGRoute.NodeS37.inertSquareOfRhoFixed`, the *inert* half of the same dichotomy, which
genuinely needs Hensel and the finite-field involution squareness).
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The local Kummer pairing vanishes when the count of the second class at `A` is even.** -/
theorem oPairAt_eq_zero_of_even_count {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
    (hpinning : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
    (hcount : Even (FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (β : ↥K)))) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (ζ := (⟨ζ, hζK⟩ : ↥K))
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = 0 := by
  rw [Work.SSGRoute.H9.swPairingValueFrob (K := K) (p := 2) (k := k) (Ω := Ω) A hA ζ hζ hζK
    α β ψ hψ hunr hpinning]
  rw [zsmul_eq_mul]
  have hc : ((FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (β : ↥K)) : ℤ) : ZMod 2) = 0 := by
    obtain ⟨m, hm⟩ := hcount
    rw [hm]
    push_cast
    rw [← two_mul, show ((2 : ZMod 2)) = 0 by decide, zero_mul]
  rw [hc, zero_mul]

end Work.SSGRoute.NodeS37
