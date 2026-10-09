import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_mul_le
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.galois_sup_structure
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor_tower
import Submission.Work.SSGRoute.ZConstruction.auxPairingGate_odd_aux
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.exists_abelianArtin_localFactors
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The θ-based local pairing of `μ_p` at the Kummer levels, and its assembly

This file is the assembly lane of `Work.SSGRoute.ZDataMup.localTate_reciprocityFamily` (see
`NOTES_LTRecFam_session6.md` for the design).  It builds the family `F` of the target from

* the **coherent lift** `hLift` of the local Kummer classes (`HonestPairing.lean`),
* the **abelian Artin map** `hPhi` of the Kummer level of the lift at a finite place,
* the **local factor** `hLocalFactor` and the **Kummer character** `kummerCharZMod`,

so that the pairing value at a place `A` and classes `x, y ∈ V_A` is

  `hPairAt A hA x y = χ_{β_A x}(θ^{L(x)}_A(β_A y))`,  `L(x) = hLevel (β_A x)`,

computed from the *global* abelian Artin map, hence admitting the reciprocity computation of
`NOTES_LTRecFam_session6.md` §4; the level-independence needed for bi-additivity is
`hLocalFactor_tower` (= obligation (P4), proved in the sibling module).
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open _root_.SSGRoute
open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-! ## Level bookkeeping for the Kummer levels -/

/-- **The Kummer level of an inverse is contained in the Kummer level.** -/
theorem hLevel_inv_le (β : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) β⁻¹ ≤ hLevel (Ω := Ω) (K := K) (p := p) β := by
  rw [NK.LocalAnabelian.kummerField_le_iff]
  intro α hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hα
    exact (map_ne_zero (algebraMap ↥K Ω)).mpr (Units.ne_zero (β⁻¹)) hα.symm
  have hβ : (α⁻¹) ^ p = algebraMap ↥K Ω ((β : ↥K)) := by
    rw [inv_pow, hα]
    simp [Units.val_inv_eq_inv_val]
  have hmem : α⁻¹ ∈ hLevel (Ω := Ω) (K := K) (p := p) β :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq hβ
  simpa using inv_mem hmem

/-- **The Kummer level of a quotient is contained in the compositum of the Kummer levels.** -/
theorem hLevel_div_le (β β' : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) (β * β'⁻¹) ≤
      hLevel (Ω := Ω) (K := K) (p := p) β ⊔ hLevel (Ω := Ω) (K := K) (p := p) β' :=
  le_trans (hLevel_mul_le (Ω := Ω) (K := K) (p := p) β β'⁻¹)
    (sup_le_sup_left (hLevel_inv_le (Ω := Ω) (K := K) (p := p) β') _)

/-! ## The chosen abelian Artin map of a Kummer level -/

/-- **An abelian idèlic Artin map of the Kummer level of `β`**, with all its clauses (this is
`Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors` with the instances of the Kummer
level supplied). -/
theorem exists_hPhi (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)] :
    ∃ Φ : NK.GlobalCFT.Idele ↥K →* (↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β)),
      Φ.ker = NK.GlobalCFT.Idele.normImage ↥K
          ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ⊔
          NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ y : NK.GlobalCFT.Idele ↥(hLevel (Ω := Ω) (K := K) (p := p) β),
        Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K
          ↥(hLevel (Ω := Ω) (K := K) (p := p) β) y) = 1) ∧
      (∀ a : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K a) = 1) ∧
      (∀ (v : NK.GlobalCFT.Place ↥K)
        (a : (NK.GlobalCFT.Place.localField ↥K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
            (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) v) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) =
          NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) Q) ∧
      (∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
        (∀ v, v ∉ s →
          Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) →
        NK.CFTLib.IdeleHasse.cprod (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ β) s
          (fun v => Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1) :=
  Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K)
    (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β))
    (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ β)

/-- **The chosen abelian Artin map of the Kummer level of `β`.** -/
noncomputable def hPhi (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    NK.GlobalCFT.Idele ↥K →* (↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) := by
  haveI := hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
  haveI := hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ β
  haveI := hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ β
  exact Classical.choose (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)

/-- The kernel of the chosen Artin map. -/
theorem hPhi_ker (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)] :
    (hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β).ker = NK.GlobalCFT.Idele.normImage ↥K
        ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ⊔
        NK.GlobalCFT.Idele.principalSubgroup ↥K :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).1

/-- The chosen Artin map kills the idèlic norms. -/
theorem hPhi_norm (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (y : NK.GlobalCFT.Idele ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) :
    hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β
      (NK.GlobalCFT.Idele.normIdeleHom ↥K
        ↥(hLevel (Ω := Ω) (K := K) (p := p) β) y) = 1 :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).2.1 y

/-- The chosen Artin map kills the principal idèles. -/
theorem hPhi_principal (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)] (a : (↥K)ˣ) :
    hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β
      (NK.GlobalCFT.Idele.principalIdele ↥K a) = 1 :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).2.2.1 a

/-- One-place faithfulness of the chosen Artin map. -/
theorem hPhi_onePlace_iff (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (v : NK.GlobalCFT.Place ↥K) (a : (NK.GlobalCFT.Place.localField ↥K v)ˣ) :
    hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β (NK.HassePrinciple.onePlace v a) = 1 ↔
      a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) v :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).2.2.2.1 v a

/-- Frobenius normalisation of the chosen Artin map. -/
theorem hPhi_frob (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hQ : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) Q) :
    hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β (NK.HeckeL.ideleOfPrime ↥K Q) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) Q :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).2.2.2.2.1 Q hQ

/-- The product formula for the local factors of the chosen Artin map. -/
theorem hPhi_cprod (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K))
    (hs : ∀ v, v ∉ s →
      hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β
        (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    NK.CFTLib.IdeleHasse.cprod (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ β) s
      (fun v => hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β
        (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1 :=
  (Classical.choose_spec (exists_hPhi (Ω := Ω) (K := K) (p := p) ζ hζ β)).2.2.2.2.2 x s hs

/-! ## The pairing value

For a finite place `A`, classes `x, y ∈ V_A` and the coherent lift `β_A := hLift ζ hζ A hA`, the
pairing value is

  `hPairAt ζ hζ A hA x y := χ_{β_A x}(σ_y)`,  `σ_y` any lift to `Gal(Ω/↥K)` of the local factor
  `θ^{L(x)}_A(β_A y) = Φ_{L(x)}(onePlace_𝔭 (localImageAt_𝔭 (β_A y)))`,  `L(x) = hLevel (β_A x)`.

Well-definedness in `σ_y` is `kummerCharZMod_eq_of_restrictNormalHom_eq` (`LocalFactor.lean`),
because `L(x)` contains `hLevel (β_A x)` by definition. -/

/-- The coherent lift at a place, as a function of the class. -/
abbrev hBeta (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) : (↥K)ˣ :=
  hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x

/-- The Kummer level of the lift of a class. -/
abbrev hLev (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    IntermediateField ↥K Ω :=
  hLevel (Ω := Ω) (K := K) (p := p) (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)

/-- **The pairing value at a finite place.** -/
noncomputable def hPairAt (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) : ZMod p := by
  haveI := hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
  haveI := hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
  haveI := hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)) :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω)
      (K₁ := ↥(hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
  exact Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
    (Classical.choose (hsurj (hLocalFactor (K := K) A hA
      (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
      (hPhi (Ω := Ω) (K := K) (p := p) ζ hζ
        (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
      (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA y))))

/-- **The computation rule of the pairing value**: any lift `σ` of the local factor computes
`hPairAt`.  This is the well-definedness of `hPairAt` in the choice of lift, and the form in which
the pairing is evaluated at any convenient level. -/
theorem hPairAt_eq_of_restrictNormalHom_eq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) (σ : Ω ≃ₐ[↥K] Ω)
    [FiniteDimensional ↥K ↥(hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)]
    [IsGalois ↥K ↥(hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)]
    (hσ : σ.restrictNormal (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x) =
      hLocalFactor (K := K) A hA (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
        (hPhi (Ω := Ω) (K := K) (p := p) ζ hζ
          (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
        (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA y)) :
    hPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x y =
      Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ
        (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x) σ := by
  haveI := hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)) :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω)
      (K₁ := ↥(hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
  refine kummerCharZMod_eq_of_restrictNormalHom_eq (Ω := Ω) (K := K) (p := p) ζ hζ
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x) le_rfl ?_
  have h1 : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
      (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)) σ =
      hLocalFactor (K := K) A hA (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
        (hPhi (Ω := Ω) (K := K) (p := p) ζ hζ
          (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
        (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA y) := hσ
  rw [h1]
  exact Classical.choose_spec (hsurj (hLocalFactor (K := K) A hA
    (hLev (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x)
    (hPhi (Ω := Ω) (K := K) (p := p) ζ hζ
      (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x))
    (hBeta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA y)))

/-- **The value formula**: a global cocycle `a` on `K.fixingSubgroup` which is the Kummer character
of `α ∈ Kˣ` has, at the place `A`, the same local character as `α`.  This is the bridge between the
global cocycles of clause (2) and the global units of `Kˣ`. -/
theorem localModelIso_toClass_eq_kummerCharMonoidHom (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (α : (↥K)ˣ)
    (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)) :
    Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
      Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA α := by
  classical
  have h4 := (Classical.choose_spec (Work.SSGRoute.ZDataMup.mupH1locLcHoms (p := p) (k := k)
    (Ω := Ω) (K := K) A hA)).2.2.2 a ha
  refine Subtype.ext (MonoidHom.ext fun d => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective d
  have hL : (Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K)
      (A := A) hA (Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)).1
        (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) :=
    congrArg Multiplicative.ofAdd (h4 g)
  have hR : (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA α).1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((Work.SSGRoute.decompEquiv_fok k Ω K A g : Ω ≃ₐ[↥K] Ω))) := rfl
  rw [hL, hR]
  exact congrArg Multiplicative.ofAdd (hα (g : Ω ≃ₐ[k] Ω) g.2.2)

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest

