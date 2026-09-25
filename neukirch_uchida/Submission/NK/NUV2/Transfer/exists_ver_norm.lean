import Mathlib
import Submission.NK.NUV2.Transfer.verDefs
import Submission.NK.NUV2.Transfer.normLevelSetup
import Submission.NK.NUV2.Transfer.transferEll_natural
import Submission.NK.Reconstruct.generalBaseChange_galToGamma
import Submission.NK.NUV2.Transfer.norm_level_factor_b

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-!
# `NK.NUV2.Transfer.exists_ver_norm`

The transfer (Verlagerung) `ver : Γ_M → Γ_L` of the inclusion `Gal(Ω/L.L) ≤ Gal(Ω/M.L)`
satisfies the norm formula `ver (res x) = ∑_{g ∈ Gal(L.L/M.L)} ρ g x`, where `ρ` is the outer
action of `Gal(L.L/ℚ)` on `Γ_L` induced by ring automorphisms of `Ω`.

## Strategy

`ver` is constructed levelwise: for every finite Galois level `R` of `Ω/L.L`, the auxiliary level
`A = AUX R = normalClosure_{M.L}(R)` is a finite Galois level of `Ω/M.L` containing `L.L`; the
levelwise transfer `eps R : Γ_{A,2} → Γ_{R,2}` is the classical transfer of the pair
`Gal(A/M.L) ⊇ Gal(A/L.L)` (`finiteVer`) followed by the restriction to `R`.  The normal closure is
monotone in `R` (`auxA_mono`), so the family `R ↦ eps R (proj (AUX R) y)` is compatible
(`transferEll_natural`) and defines an element of `Γ_L`.  The norm formula follows from the
levelwise norm identity `norm_level_factor`.
-/

namespace NK.NUV2.Transfer

noncomputable section

open NK.Reconstruct

/-- `Additive.ofMul` turns a product into a sum. -/
theorem ofMul_prod {ι M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M) :
    Additive.ofMul (s.prod f) = s.sum (fun i => Additive.ofMul (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ofMul_mul, ih]

theorem exists_ver_norm (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (M : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    [NumberField ↥M.L] [NumberField ↥L.L] [FiniteDimensional ℚ ↥M.L] [FiniteDimensional ℚ ↥L.L]
    [Normal ℚ ↥L.L] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
    [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]
    (ρ : Gal(↥L.L/ℚ) →* (NK.Reconstruct.Gamma ↥L.L Ω 2 ≃* NK.Reconstruct.Gamma ↥L.L Ω 2))
    (hρ : ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
        (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
        ρ τ = NK.Reconstruct.tauStar L.L 2 θ hθ) :
    ∃ ver : NK.Reconstruct.Gamma ↥M.L Ω 2 →* NK.Reconstruct.Gamma ↥L.L Ω 2, Continuous ⇑ver ∧
      ∀ x : NK.Reconstruct.Gamma ↥L.L Ω 2,
        (∑ g : Gal(↥L.L/↥M.L), Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) x))
          = Additive.ofMul
              (ver (NK.Reconstruct.generalBaseChange M (NK.Reconstruct.NumFieldIn.ofFrobLevel L)
                hML 2 x)) := by
  classical
  haveI hfin : FiniteDimensional ↥M.L ↥L.L := inferInstance
  -- the levelwise norm identity (the mathematical input)
  have hnorm : ∀ (R : NK.Reconstruct.FrobLevel ↥L.L Ω) (x : NK.Reconstruct.Gamma ↥L.L Ω 2),
      NK.Reconstruct.Gamma.proj R (normEndo M L ρ x)
        = eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R)
            (NK.Reconstruct.generalBaseChange M (NK.Reconstruct.NumFieldIn.ofFrobLevel L)
              hML 2 x)) :=
    fun R x => NormLevelB.norm_level_factor_b M L hML ρ hρ R x
  -- the compatible family of level components
  let comp : NK.Reconstruct.Gamma ↥M.L Ω 2 → (∀ R : NK.Reconstruct.FrobLevel ↥L.L Ω,
      NK.Reconstruct.LevelEllPart R.L 2) :=
    fun y R => eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R) y)
  have hcomp : ∀ y : NK.Reconstruct.Gamma ↥M.L Ω 2, NK.Reconstruct.Compatible 2 (comp y) := by
    intro y R₁ R₂ h
    show NK.Reconstruct.ellRestrict 2 R₁ R₂ h
        (eps M L hML R₂ (NK.Reconstruct.Gamma.proj (AUX M L hML R₂) y))
      = eps M L hML R₁ (NK.Reconstruct.Gamma.proj (AUX M L hML R₁) y)
    rw [show eps M L hML R₂ (NK.Reconstruct.Gamma.proj (AUX M L hML R₂) y)
        = transferEll M L hML R₂ (NK.Reconstruct.Gamma.proj (AUX M L hML R₂) y) from rfl,
      show eps M L hML R₁ (NK.Reconstruct.Gamma.proj (AUX M L hML R₁) y)
        = transferEll M L hML R₁ (NK.Reconstruct.Gamma.proj (AUX M L hML R₁) y) from rfl,
      transferEll_natural M L hML R₁ R₂ h]
    exact congrArg (transferEll M L hML R₁)
      (NK.Reconstruct.Gamma.proj_compatible (AUX M L hML R₁) (AUX M L hML R₂)
        (auxA_mono M L hML h) y)
  let ver : NK.Reconstruct.Gamma ↥M.L Ω 2 →* NK.Reconstruct.Gamma ↥L.L Ω 2 :=
    { toFun := fun y => NK.Reconstruct.Gamma.mk (comp y) (hcomp y)
      map_one' := by
        refine NK.Reconstruct.Gamma.ext (fun R => ?_)
        show eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R)
          (1 : NK.Reconstruct.Gamma ↥M.L Ω 2)) = 1
        rw [map_one, map_one]
      map_mul' := by
        intro y z
        refine NK.Reconstruct.Gamma.ext (fun R => ?_)
        show eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R) (y * z))
          = eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R) y)
            * eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R) z)
        rw [map_mul, map_mul] }
  have hver : ∀ (x : NK.Reconstruct.Gamma ↥L.L Ω 2),
      ver (NK.Reconstruct.generalBaseChange M (NK.Reconstruct.NumFieldIn.ofFrobLevel L) hML 2 x)
        = normEndo M L ρ x := by
    intro x
    refine NK.Reconstruct.Gamma.ext (fun R => ?_)
    show eps M L hML R (NK.Reconstruct.Gamma.proj (AUX M L hML R)
      (NK.Reconstruct.generalBaseChange M (NK.Reconstruct.NumFieldIn.ofFrobLevel L) hML 2 x))
        = NK.Reconstruct.Gamma.proj R (normEndo M L ρ x)
    rw [hnorm R x]
  refine ⟨ver, ?_, ?_⟩
  · show Continuous fun y : NK.Reconstruct.Gamma ↥M.L Ω 2 =>
      (NK.Reconstruct.Gamma.mk (comp y) (hcomp y) : NK.Reconstruct.Gamma ↥L.L Ω 2)
    refine Continuous.subtype_mk ?_ (fun y => hcomp y)
    rw [continuous_pi_iff]
    intro R
    exact (continuous_of_discreteTopology).comp (continuous_proj 2 (AUX M L hML R))
  · intro x
    rw [hver x, normEndo_apply]
    exact (ofMul_prod Finset.univ
      (fun g : Gal(↥L.L/↥M.L) => ρ (AlgEquiv.restrictScalars ℚ g) x)).symm

end

end NK.NUV2.Transfer
