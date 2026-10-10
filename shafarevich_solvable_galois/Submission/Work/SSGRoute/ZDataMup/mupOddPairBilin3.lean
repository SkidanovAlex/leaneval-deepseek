import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupOddPairBilin2
import Submission.Work.SSGRoute.ZDataMup.oddLevel_sup_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Additivity of the odd-`p` pairing

* `oPairGlob_add`: additivity in the first variable for *global* representatives (the tower makes
  the three levels involved comparable, and the character is multiplicative at the common level);
* `oPairGlob_eq_zero_of_localPowClass_eq_one`: a locally trivial first representative gives `0`;
* `oPair_congr`: the pairing depends on the representatives only through their local classes;
* `oPair_add_left`: additivity in the first variable.
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

/-- **Additivity of the pairing in the first variable**, for global representatives. -/
theorem oPairGlob_add (α₁ α₂ β : (↥K)ˣ) :
    oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (α₁ * α₂) β =
      oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₁ β +
        oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₂ β := by
  classical
  haveI hfd₁ : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α₁) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α₁
  haveI hgal₁ : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α₁) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α₁
  haveI hfd₂ : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α₂) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α₂
  haveI hgal₂ : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α₂) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α₂
  haveI hfd₁₂ : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (α₁ * α₂)) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (α₁ * α₂)
  haveI hgal₁₂ : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (α₁ * α₂)) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (α₁ * α₂)
  -- the common level `L₁ ⊔ L₂`
  let M : IntermediateField ↥K Ω :=
    hLevel (Ω := Ω) (K := K) (p := p) α₁ ⊔ hLevel (Ω := Ω) (K := K) (p := p) α₂
  have hMfd : FiniteDimensional ↥K ↥M := by
    rw [show M = _ from rfl]; infer_instance
  haveI : FiniteDimensional ↥K ↥M := hMfd
  haveI : IsGalois ↥K ↥M := by rw [show M = _ from rfl]; infer_instance
  haveI : NumberField ↥M := by
    rw [show M = _ from rfl]
    exact Commons.NumberTheory.NumberField.numberField_of_intermediateField
      (K := ↥K) (K' := Ω) M
  have hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a := by
    rw [show M = _ from rfl]
    exact oddLevel_sup_comm _ _ (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α₁)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α₂)
  have hle₁₂ : hLevel (Ω := Ω) (K := K) (p := p) (α₁ * α₂) ≤ M := by
    rw [show M = _ from rfl]
    exact hLevel_mul_le (Ω := Ω) (K := K) α₁ α₂
  have hle₁ : hLevel (Ω := Ω) (K := K) (p := p) α₁ ≤ M := by
    rw [show M = _ from rfl]; exact le_sup_left
  have hle₂ : hLevel (Ω := Ω) (K := K) (p := p) α₂ ≤ M := by
    rw [show M = _ from rfl]; exact le_sup_right
  have ht₁₂ := odd_hChar_tower (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA (α₁ * α₂)
    (L := hLevel (Ω := Ω) (K := K) (p := p) (α₁ * α₂)) (M := M) hle₁₂ (le_rfl)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ (α₁ * α₂)) hcommM β
  have ht₁ := odd_hChar_tower (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA α₁
    (L := hLevel (Ω := Ω) (K := K) (p := p) α₁) (M := M) hle₁ (le_rfl)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α₁) hcommM β
  have ht₂ := odd_hChar_tower (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA α₂
    (L := hLevel (Ω := Ω) (K := K) (p := p) α₂) (M := M) hle₂ (le_rfl)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α₂) hcommM β
  have hmul := hChar_mul (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α₁ α₂ (M := M) hle₁₂ hle₁ hle₂
    (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β)
  -- the level comparisons, in the form used below
  have ht₁₂' : hChar (K := K) (p := p) ζ hζ (α₁ * α₂) hle₁₂
        (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β) =
      hChar (K := K) (p := p) ζ hζ (α₁ * α₂) (le_refl _)
        (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (α₁ * α₂) β) := ht₁₂
  have ht₁' : hChar (K := K) (p := p) ζ hζ α₁ hle₁
        (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β) =
      hChar (K := K) (p := p) ζ hζ α₁ (le_refl _)
        (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₁ β) := ht₁
  have ht₂' : hChar (K := K) (p := p) ζ hζ α₂ hle₂
        (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β) =
      hChar (K := K) (p := p) ζ hζ α₂ (le_refl _)
        (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₂ β) := ht₂
  calc oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (α₁ * α₂) β
      = (hChar (K := K) (p := p) ζ hζ (α₁ * α₂) (le_refl _)
          (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (α₁ * α₂) β)).toAdd :=
        oPairGlob_def (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (α₁ * α₂) β
    _ = (hChar (K := K) (p := p) ζ hζ (α₁ * α₂) hle₁₂
          (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β)).toAdd := by
        rw [← ht₁₂']
    _ = (hChar (K := K) (p := p) ζ hζ α₁ hle₁
            (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β) *
          hChar (K := K) (p := p) ζ hζ α₂ hle₂
            (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β)).toAdd := by
        rw [hmul]
    _ = (hChar (K := K) (p := p) ζ hζ α₁ hle₁
            (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β)).toAdd +
          (hChar (K := K) (p := p) ζ hζ α₂ hle₂
            (hLocalFactor (K := K) A hA M (oddArtin (K := K) M hcommM) β)).toAdd := by
        rw [toAdd_mul]
    _ = oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₁ β +
          oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α₂ β := by
        rw [ht₁', ht₂', ← oPairGlob_def, ← oPairGlob_def]

/-- **A locally trivial first representative gives value `0`.** -/
theorem oPairGlob_eq_zero_of_localPowClass_eq_one (α β : (↥K)ˣ)
    (hα : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) α = 1) :
    oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β = 0 := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  rw [oPairGlob_def,
    oFactorGlob_eq_one_of_localPowClass_eq_one (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β
      hα, map_one, toAdd_one]

end

end Work.SSGRoute.ZDataMup.OddForm
