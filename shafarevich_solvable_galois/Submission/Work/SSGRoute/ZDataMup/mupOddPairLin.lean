import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddPairBilin4
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd-`p` pairing as a bilinear form

The pairing `oPair` of `mupOddForm.lean` is additive in each variable
(`oPair_add_left`, `oPair_add_right`); since the coefficient ring is the prime field `ZMod p`, an
additive map on `ZMod p`-modules is automatically `ZMod p`-linear, and `oPair` therefore packages
into a bilinear form

  `oPairForm A hA : hV A →ₗ[ZMod p] hV A →ₗ[ZMod p] ZMod p`.

This is the form consumed by the assembly of the target `localTateSystem_productFormula_odd` (which
needs a family `∀ H, V H →ₗ[ZMod p] V H →ₗ[ZMod p] ZMod p`).
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

variable (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (hA : SSGRoute.IsFinPlace k A)

/-- The pairing vanishes when its first argument is zero. -/
theorem oPair_zero_right (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x 0 = 0 := by
  have h := oPair_add_right (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x 0 0
  rw [add_zero] at h
  have h2 : oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x 0 + 0 =
      oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x 0 +
        oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x 0 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The pairing vanishes when its second argument is zero. -/
theorem oPair_zero_left (y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA 0 y = 0 := by
  have h := oPair_add_left (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA 0 0 y
  rw [zero_add] at h
  have h2 : oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA 0 y + 0 =
      oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA 0 y +
        oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA 0 y := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The pairing, as a linear form in the *second* variable. -/
noncomputable def oPairLinearRight (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    hV (K := K) (p := p) (k := k) (Ω := Ω) A →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun y => oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y
      map_zero' := oPair_zero_right (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      map_add' := fun y y' => oPair_add_right (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y y' }

/-- **The odd-`p` pairing as a bilinear form** on the level-`K` local `H¹` at the place `A`. -/
noncomputable def oPairForm :
    hV (K := K) (p := p) (k := k) (Ω := Ω) A →ₗ[ZMod p]
      (hV (K := K) (p := p) (k := k) (Ω := Ω) A →ₗ[ZMod p] ZMod p) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x => oPairLinearRight (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      map_zero' := by
        refine LinearMap.ext fun y => ?_
        exact oPair_zero_left (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA y
      map_add' := fun x x' => by
        refine LinearMap.ext fun y => ?_
        exact oPair_add_left (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x x' y }

/-- The defining equation of `oPairForm`. -/
theorem oPairForm_apply (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y =
      oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y :=
  rfl

/-- **First-variable non-degeneracy, in the form consumed by the assembly.** -/
theorem oPairForm_nondegenerate (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A)
    (h : ∀ y, oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y = 0) : x = 0 :=
  oPair_left_nondegenerate (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x fun y => h y

end

end Work.SSGRoute.ZDataMup.OddForm
