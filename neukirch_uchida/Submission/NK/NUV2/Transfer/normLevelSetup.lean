import Mathlib
import Submission.NK.NUV2.Transfer.verDefs
import Submission.NK.NUV2.Transfer.exists_tauStarAction
import Submission.NK.Reconstruct.generalBaseChange_galToGamma

/-!
# The level-wise data for the norm--transfer identity

This file sets up the objects used to prove `NK.NUV2.Transfer.transferNormIdentity`:

* `NK.NUV2.Transfer.normEndo` — the norm endomorphism
  `x ↦ ∏_{g ∈ Gal(L.L/M.L)} ρ(g)(x)` of `Γ_L`;
* `NK.NUV2.Transfer.AUX`, `NK.NUV2.Transfer.AUXL` — for a level `R` of `Γ_L` over `L.L`, the
  auxiliary level `A = normalClosure_{M.L}(R)` over `M.L` and the same field viewed over `L.L`;
* `NK.NUV2.Transfer.eps` — the level-wise transfer `Γ_{A,2} → Γ_{R,2}`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace NK.NUV2.Transfer

noncomputable section

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **`L.L` is normal over `ℚ`** for the canonical `ℚ`-algebra structure of a characteristic zero
field (the `IntermediateField` algebra structure is the canonical one up to `Subsingleton`). -/
instance instNormalFrobLevel (L : FrobLevel ℚ Ω) : Normal ℚ ↥L.L :=
  cast (congrArg (fun a => @Normal ℚ (↥L.L) _ _ a) (Subsingleton.elim _ _)) L.normal

variable (M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
  [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
  [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω] [FiniteDimensional ↥M.L ↥L.L]

/-- **The norm endomorphism** `x ↦ ∏_{g ∈ Gal(L.L/M.L)} ρ(g) x` of `Γ_L`. -/
noncomputable def normEndo (ρ : Gal(↥L.L/ℚ) →*
    (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2)) : Gamma ↥L.L Ω 2 →* Gamma ↥L.L Ω 2 where
  toFun x := ∏ g : Gal(↥L.L/↥M.L), ρ (AlgEquiv.restrictScalars ℚ g) x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [← Finset.prod_mul_distrib]

@[simp] theorem normEndo_apply (ρ : Gal(↥L.L/ℚ) →*
    (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2)) (x : Gamma ↥L.L Ω 2) :
    normEndo M L ρ x = ∏ g : Gal(↥L.L/↥M.L), ρ (AlgEquiv.restrictScalars ℚ g) x := rfl

/-- **The auxiliary level over `M.L`**: the normal closure of the level `R` of `Γ_L` over `M.L`. -/
noncomputable abbrev AUX (R : FrobLevel ↥L.L Ω) : FrobLevel ↥M.L Ω :=
  auxA M L hML R

/-- **The auxiliary level viewed over `L.L`** (the same field). -/
noncomputable abbrev AUXL (R : FrobLevel ↥L.L Ω) : FrobLevel ↥L.L Ω :=
  auxAL M L hML R

/-- **The level-wise transfer** `Γ_{A,2} → Γ_{R,2}` through the auxiliary level `A = AUX R`:
the transfer `ℓ-part(Gal(A/M.L)^{ab}) → ℓ-part(Gal(A/L.L)^{ab})` restricted to `R`. -/
noncomputable def eps (R : FrobLevel ↥L.L Ω) :
    LevelEllPart (AUX M L hML R).L 2 →* LevelEllPart R.L 2 :=
  transferEll M L hML R

theorem eps_apply (R : FrobLevel ↥L.L Ω) (z : LevelEllPart (AUX M L hML R).L 2) :
    eps M L hML R z = transferEll M L hML R z := rfl

end

end NK.NUV2.Transfer
