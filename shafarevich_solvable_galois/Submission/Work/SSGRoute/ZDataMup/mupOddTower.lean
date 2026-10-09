import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddChar
import Submission.Work.SSGRoute.ZDataMup.mupOddLevel
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level independence of the descended Kummer character of the local factor

`Work.SSGRoute.ZDataMup.OddForm.hChar` is the Kummer character of `β ∈ ↥Kˣ`, descended to a level
`M ⊇ ↥K(β^{1/p})`.  The pairing of `mupOddForm.lean` evaluates it at the local factor
`hLocalFactor A hA M (oddArtin M hcommM) ν` of the abelian Artin map of the level `M`.  This file
proves (`odd_hChar_tower`) that the value does **not** depend on the level: for
`↥K(β^{1/p}) ≤ L ≤ M` and Artin maps `oddArtin M`, `oddArtin L` of the two levels,

  `hChar β (θ^M_A(ν)) = hChar β (θ^L_A(ν))`.

The proof is the one recorded in the doc comment of `mupOddLevel.lean`:

* `Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq` (proved, `sorry`-free) says that
  the two Artin elements agree under the restriction `restrictMol L M hLM : Gal(M/↥K) → Gal(L/↥K)`;
* both `hChar` values are `ofAdd (kummerCharZMod β σ)` for a common lift
  `σ ∈ Gal(Ω/↥K)` of the level-`M` Artin element (`hChar_apply`), because the restriction of `σ` to
  `L` is the level-`L` Artin element by the previous point.

This is the `hChar` form of obligation (P4) of the gate plan
(`aux_hLocalFactor_restrictNormalHom_eq`); it is the only level-compatibility the odd-`p` route of
`NOTES_mupOdd_session11.md` consumes.
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

/-- **The level of the Artin factor does not matter** (as long as it contains the Kummer field of
the first argument): the descended Kummer character of the local factor is independent of the
level. -/
theorem odd_hChar_tower (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (β : (↥K)ˣ)
    {L M : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hLM : L ≤ M) (hKL : NK.LocalAnabelian.kummerField (K' := Ω) p β ≤ L)
    (hcommL : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a) (ν : (↥K)ˣ) :
    hChar (K := K) (p := p) ζ hζ β (le_trans hKL hLM)
        (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) ν) =
      hChar (K := K) (p := p) ζ hζ β hKL
        (hLocalFactor (K := K) A hA L (oddArtin (K := K) L hcommL) ν) := by
  classical
  haveI hNL : Normal ↥K ↥L := IsGalois.to_normal
  haveI hNM : Normal ↥K ↥M := IsGalois.to_normal
  haveI hNΩ : Normal ↥K Ω := inferInstance
  -- abbreviate the two local factors
  set z : NK.GlobalCFT.Idele ↥K :=
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA))
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) ν) with hz
  have hLMf : hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) ν =
      oddArtin (K := K) M hcommM z := rfl
  have hLLf : hLocalFactor (K := K) A hA L (oddArtin (K := K) L hcommL) ν =
      oddArtin (K := K) L hcommL z := rfl
  -- the two Artin elements agree under the restriction `Gal(M/↥K) → Gal(L/↥K)`
  have hcomp : restrictMol (K := ↥K) L M hLM (oddArtin (K := K) M hcommM z) =
      oddArtin (K := K) L hcommL z := by
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [Work.SSGRoute.ZConstruction.restrictMol_apply (K := ↥K) (L := L) (M := M) hLM (oddArtin (K := K) M hcommM z) x]
    exact Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq (p := p) k Ω K A hA L M
      hLM hcommM (oddArtin (K := K) M hcommM) (oddArtin_ker (K := K) M hcommM)
      (oddArtin_frob (K := K) M hcommM) (oddArtin (K := K) L hcommL)
      (oddArtin_ker (K := K) L hcommL) (oddArtin_frob (K := K) L hcommL) ν x
  -- a common lift of the level-`M` Artin element
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥M)
    (oddArtin (K := K) M hcommM z)
  have hσL : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L σ =
      oddArtin (K := K) L hcommL z := by
    rw [← hcomp, ← hσ]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [Work.SSGRoute.ZConstruction.restrictMol_apply (K := ↥K) (L := L) (M := M) hLM
      ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M) σ) x]
    rw [AlgEquiv.restrictNormalHom_apply (F := ↥K) (K₁ := Ω) L σ x,
      AlgEquiv.restrictNormalHom_apply (F := ↥K) (K₁ := Ω) M σ ⟨(x : Ω), hLM x.2⟩]
  have h1 : hChar (K := K) (p := p) ζ hζ β (le_trans hKL hLM)
      (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) ν) =
      Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ) := by
    rw [hLMf, ← hσ, hChar_apply]
  have h2 : hChar (K := K) (p := p) ζ hζ β hKL
      (hLocalFactor (K := K) A hA L (oddArtin (K := K) L hcommL) ν) =
      Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ) := by
    rw [hLLf, ← hσL, hChar_apply]
  rw [h1, h2]

end

end Work.SSGRoute.ZDataMup.OddForm
