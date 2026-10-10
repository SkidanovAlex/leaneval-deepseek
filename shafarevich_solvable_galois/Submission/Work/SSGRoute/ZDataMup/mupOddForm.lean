import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.stabilizer_eq_implies_conj
import Submission.Work.SSGRoute.ZDataMup.mupOddAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd-`p` local Tate system: the pairing from the global abelian Artin map

This file builds the family `F` of bilinear forms on the level-`K` local `H¹`-groups whose local
contributions cancel in the reciprocity sum, i.e. the arithmetic content of
`Work.SSGRoute.ZDataMup.localTateSystem_productFormula_odd`, following the plan of
`NOTES_mupOdd_session11.md` (there is no use of the local factor membership `LFM`).

The pairing value of two local classes `x y ∈ V_A` at the finite place `A` is

  `oPair x y = χ_{x̃}(θ^{K(x̃^{1/p})}_A(ỹ))`,

where

* `hLift x ∈ Kˣ` is the coherent lift of `x` (`ZConstruction.exists_localKummerLift`),
* `χ_{x̃}` is the Kummer character of `x̃`, descended to the level `K(x̃^{1/p})`,
* `θ^L_A = Φ_L ∘ onePlace_𝔭 ∘ localImageAt_𝔭` is the local factor of the **global** abelian Artin
  map `Φ_L` of the level `L/↥K`.

Because the level depends only on the *first* variable, the reciprocity sum over a set `T'` of
places (one per `↥K`-orbit) is `χ_α(∏_{A ∈ T'} θ^{K(α^{1/p})}_A(β))` for a *single* level, and the
product is `1` by the product formula `oddArtin_product`.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-- The commutativity of the Galois group of the Kummer level `K(β^{1/p})`. -/
private theorem hLevel_comm (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β), a * b = b * a :=
  hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ β


variable (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (hA : SSGRoute.IsFinPlace k A)

/-- The Kummer level attached to a level-`K` local class `x`: the Kummer field of its coherent
lift.  **The level depends only on `x`** (and on the place). -/
abbrev oLevel (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) : IntermediateField ↥K Ω :=
  hLevel (Ω := Ω) (K := K) (p := p) (hLift ζ hζ A hA x)

/-- The Kummer character of the lift of `x`, descended to the level `oLevel x`. -/
noncomputable def oChar (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    (↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) ≃ₐ[↥K]
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)) →*
      Multiplicative (ZMod p) :=
  letI hfd : FiniteDimensional ↥K
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  letI hgal : IsGalois ↥K
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  hChar (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x) (le_refl _)

/-- The Galois group of `oLevel x` is commutative. -/
theorem oComm (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    ∀ a b : ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) ≃ₐ[↥K]
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x), a * b = b * a :=
  hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ (hLift ζ hζ A hA x)

/-- The local factor at `A` of the global Artin map of the level of `x`, applied to `γ`. -/
noncomputable def oFactor (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) (γ : (↥K)ˣ) :
    ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) ≃ₐ[↥K]
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
  letI hfd : FiniteDimensional ↥K
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  letI hgal : IsGalois ↥K
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  letI hnf : NumberField
      ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  hLocalFactor (K := K) A hA (oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
    (oddArtin (K := K) (oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
      (oComm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)) γ

/-- **The odd-`p` local pairing**: the Kummer character of the lift of `x`, evaluated at the local
factor of the global Artin map of the level of `x`, applied to the lift of `y`. -/
noncomputable def oPair (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) : ZMod p :=
  (oChar (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
    (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (hLift ζ hζ A hA y))).toAdd

/-- **The local factor kills a global element whose local Kummer class is trivial** (a local
`p`-th power): the local image is a `p`-th power, and the Artin factor of a level of exponent `p`
kills `p`-th powers. -/
theorem oddLocalFactor_eq_one_of_localPowClass_eq_one
    (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) (γ : (↥K)ˣ)
    (hγ : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ = 1) :
    oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x γ = 1 := by
  unfold oFactor
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (hLocalImageAt_mem_powRange_of_localPowClass_eq_one (K := K) (p := p) (A := A) hA γ hγ)
  simp only [powMonoidHom_apply] at hz
  rw [hLocalFactor, ← hz]
  have h1 : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA))
      (z ^ p) =
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) z) ^ p := by
    rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply, map_pow,
      NK.CFTLib.IdeleHasse.onePlaceHom_apply]
  rw [h1, map_pow]
  exact hLevel_aut_pow_eq_one (Ω := Ω) (K := K) ζ hζ (hLift ζ hζ A hA x) _

/-- **Additivity of the local factor in the argument.** -/
theorem oddLocalFactor_mul (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) (γ γ' : (↥K)ˣ) :
    oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (γ * γ') =
      oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x γ *
        oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x γ' := by
  haveI hfd : FiniteDimensional ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  haveI hgal : IsGalois ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  haveI hnf : NumberField ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  unfold oFactor
  exact hLocalFactor_mul (K := K) hA (oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
    (oddArtin (K := K) (oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
      (oComm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)) γ γ'

/-- **Additivity of the pairing in the second variable.** -/
theorem oPair_add_right (x y y' : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (y + y') =
      oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y +
        oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y' := by
  set δ : (↥K)ˣ := hLift ζ hζ A hA (y + y') *
    (hLift ζ hζ A hA y * hLift ζ hζ A hA y')⁻¹ with hδdef
  have hδ : ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA δ = 1 :=
    hLift_coherent (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA y y'
  have hβδ : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) δ = 1 :=
    (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) δ).mp hδ
  have h1 : δ * (hLift ζ hζ A hA y * hLift ζ hζ A hA y') = hLift ζ hζ A hA (y + y') := by
    rw [hδdef, mul_assoc, inv_mul_cancel, mul_one]
  have hfac' : hLift ζ hζ A hA y * hLift ζ hζ A hA y' * δ =
      hLift ζ hζ A hA (y + y') := by
    rw [mul_comm (hLift ζ hζ A hA y * hLift ζ hζ A hA y') δ]
    exact h1
  rw [oPair, oPair, oPair, ← hfac',
    oddLocalFactor_mul (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      (hLift ζ hζ A hA y * hLift ζ hζ A hA y') δ,
    oddLocalFactor_eq_one_of_localPowClass_eq_one (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
      x δ hβδ, mul_one,
    oddLocalFactor_mul (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      (hLift ζ hζ A hA y) (hLift ζ hζ A hA y'),
    map_mul, toAdd_mul]




/-- **The coherent lift realises every local `p`-th power class.** -/
theorem hLift_localPowClass_surjective
    (u : (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ ⧸
      (powMonoidHom p : (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ →*
        (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ).range) :
    ∃ y : hV (K := K) (p := p) (k := k) (Ω := Ω) A,
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA y) = u := by
  let eModel : hV (K := K) (p := p) (k := k) (Ω := Ω) A ≃
      ↥(lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Equiv.ofBijective _ (ZConstruction.localModelIso_bijective (p := p) (k := k) (Ω := Ω)
      (K := K) (A := A) hA)
  refine ⟨eModel.symm (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA (oddFinPlace (K := K) (A := A) hA) u), ?_⟩
  have h1 : ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA
      (hLift ζ hζ A hA (eModel.symm (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k)
        (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA (oddFinPlace (K := K) (A := A) hA)
        u))) =
      Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA (oddFinPlace (K := K) (A := A) hA) u := by
    rw [hLift_realises]
    exact Equiv.apply_symm_apply eModel _
  refine (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K)
    (ζ := ζ) (hζ := hζ) (A := A) hA (oddFinPlace (K := K) (A := A) hA)).injective ?_
  rw [Work.SSGRoute.ZDataMup.mupKummerEquiv_apply_localPowClass]
  exact h1

/-- The pairing value, as the Kummer character evaluated at the local factor (with the instances of
the level as hypotheses, so that they need not be synthesised). -/
theorem oPair_eq_hChar (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A)
    [FiniteDimensional ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)]
    [IsGalois ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)] :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y =
      (hChar (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x) (le_refl _)
        (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (hLift ζ hζ A hA y))).toAdd :=
  rfl

/-- **Left non-degeneracy of the pairing.** -/
theorem oPair_left_nondegenerate (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A)
    (hx : ∀ y, oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y = 0) : x = 0 := by
  classical
  haveI hfd : FiniteDimensional ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  haveI hgal : IsGalois ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  let eModel : hV (K := K) (p := p) (k := k) (Ω := Ω) A ≃
      ↥(lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Equiv.ofBijective _ (ZConstruction.localModelIso_bijective (p := p) (k := k) (Ω := Ω)
      (K := K) (A := A) hA)
  -- the local `p`-th power class of the lift of `x` is trivial
  have hkey : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
      (hLift ζ hζ A hA x) = 1 := by
    by_cases hβ : hLift ζ hζ A hA x ∈ NK.LocalAnabelian.powSubgroup p ↥K
    · obtain ⟨c, hc⟩ := hβ
      rw [← hc]
      refine (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) (c ^ p)).mp ?_
      exact Subtype.ext_iff.mpr (ZConstruction.kummerCharHom_pow (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) c)
    · -- the level is a non-trivial Kummer level
      have hcard : Nat.card (↥(hLevel (Ω := Ω) (K := K) (p := p) (hLift ζ hζ A hA x)) ≃ₐ[↥K]
          ↥(hLevel (Ω := Ω) (K := K) (p := p) (hLift ζ hζ A hA x))) = p := by
        have hgal' := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω)
          (k := ↥K) p Fact.out hζ (hLift ζ hζ A hA x) hβ
        rw [IsGalois.card_aut_eq_finrank, hgal'.2]
      have hinj := odd_hChar_injective (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ
        (hLift ζ hζ A hA x) hβ
      -- the local factor of every lift of a local class is trivial
      have hfac : ∀ y : hV (K := K) (p := p) (k := k) (Ω := Ω) A,
          oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (hLift ζ hζ A hA y) = 1 := by
        intro y
        have h1 : (hChar (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x) (le_refl _)
            (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
              (hLift ζ hζ A hA y))).toAdd = 0 := by
          rw [← oPair_eq_hChar (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y]
          exact hx y
        have h2 : (hChar (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x) (le_refl _)
            (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
              (hLift ζ hζ A hA y))) = 1 := by
          have h3 := ofAdd_toAdd (hChar (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x) (le_refl _)
            (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x (hLift ζ hζ A hA y)))
          rw [← h3, h1, ofAdd_zero]
        exact hinj (by rw [h2, map_one])
      -- the local image of every lift of a local class is a local norm
      have hloc : ∀ y : hV (K := K) (p := p) (k := k) (Ω := Ω) A,
          NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) (hLift ζ hζ A hA y) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
            (L := ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x))
            (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) := by
        intro y
        have hh := hfac y
        unfold oFactor at hh
        rw [hLocalFactor] at hh
        exact (oddArtin_onePlace (K := K) (oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
          (oComm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)
          (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) _).mp hh
      -- hence the local norm subgroup is everything
      have hnorm : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
          (L := ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x))
          (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) = ⊤ := by
        refine le_antisymm le_top ?_
        intro v _
        obtain ⟨y, hy⟩ := hLift_localPowClass_surjective (K := K) (p := p) (k := k) (Ω := Ω)
          ζ hζ hA (QuotientGroup.mk'
            (powMonoidHom p : (mupCompletion (K := K) A
              (oddFinPlace (K := K) (A := A) hA))ˣ →*
              (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ).range v)
        have h1 : QuotientGroup.mk'
            (powMonoidHom p : (mupCompletion (K := K) A
              (oddFinPlace (K := K) (A := A) hA))ˣ →*
              (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ).range
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) (hLift ζ hζ A hA y) *
              v⁻¹) = 1 := by
          rw [map_mul, map_inv]
          have h2 : QuotientGroup.mk'
              (powMonoidHom p : (mupCompletion (K := K) A
                (oddFinPlace (K := K) (A := A) hA))ˣ →*
                (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ).range
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA))
                (hLift ζ hζ A hA y)) = QuotientGroup.mk'
              (powMonoidHom p : (mupCompletion (K := K) A
                (oddFinPlace (K := K) (A := A) hA))ˣ →*
                (mupCompletion (K := K) A (oddFinPlace (K := K) (A := A) hA))ˣ).range v := by
            rw [← hy]
            rfl
          rw [h2, mul_inv_cancel]
        obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp h1
        have hv : v = (z ^ p)⁻¹ * NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) (hLift ζ hζ A hA y) := by
          rw [powMonoidHom_apply] at hz
          rw [hz]
          group
        rw [hv]
        have hN : (z ^ p)⁻¹ ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
            (L := ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x))
            (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) :=
          Subgroup.inv_mem _
            (mem_localNormSubgroup_of_mem_powRange (K := ↥K)
              (L := ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x)) hcard
              (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) _ ⟨z, rfl⟩)
        exact mul_mem hN (hloc y)
      have hsplit : SSGRoute.IsSplitIn ↥K (hLevel (Ω := Ω) (K := K) (p := p)
          (hLift ζ hζ A hA x)) A :=
        oddSplitIn_of_localNormSubgroup_eq_top (K := K) (p := p) (k := k) (Ω := Ω) A hA _
          hcard hnorm
      exact (odd_localPowClass_eq_one_iff_isSplitIn (K := K) (p := p) ζ hζ A hA
        (hLift ζ hζ A hA x)).mpr hsplit
  have h1 : ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA (hLift ζ hζ A hA x) = 1 :=
    (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) _).mpr hkey
  have h2 : eModel x = 1 := by
    show ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x = 1
    rw [← hLift_realises (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x]
    exact h1
  have h3 : eModel 0 = 1 :=
    ZConstruction.localModelIso_zero (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA
  exact eModel.injective (by rw [h2, h3])

end

end Work.SSGRoute.ZDataMup.OddForm
