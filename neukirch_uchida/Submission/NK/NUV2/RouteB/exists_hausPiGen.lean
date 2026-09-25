import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.Reconstruct.generalBaseChange_galToGamma

/-!
# The general base change descends to the Hausdorff torsion-free quotient

For number fields `K ⊆ M` inside a separable closure `Ω` of `ℚ` and a prime `ℓ`, Shimizu's base
change `π_{M/K} : Γ_M → Γ_K` (`NK.Reconstruct.generalBaseChange`) induces a `ℤ_ℓ`-linear map

  `Φ : Γ_M^{tf} = HausQuot M → Γ_K^{tf} = HausQuot K`

on the Hausdorff torsion-free quotients (`NK.Reconstruct.HausQuot`,
`NK.Reconstruct.hausMk`), characterised by the commutation with the projections:

  `Φ (hausMk x) = hausMk (generalBaseChange K M h ℓ x)`.

The two ingredients are:

* a character of `Γ_K` pulls back along `π_{M/K}` to a character of `Γ_M`
  (`NK.Reconstruct.dualMap`), so the kernel of `Γ_M ↠ Γ_M^{tf}` is mapped into the kernel of
  `Γ_K ↠ Γ_K^{tf}`: the descent is well defined (this is the content of
  `invisibleSubmodule_le_comap_generalBaseChange`);
* a *continuous* additive homomorphism between the pro-ℓ abelianisations `Γ` is automatically
  `ℤ_ℓ`-linear (`continuous_addHom_smul`): the scalar action of `ℤ_ℓ` is continuous and is the
  limit of the integer power maps, which any additive homomorphism respects.  This is what makes
  the descent a `LinearMap` rather than merely an additive map.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4,
Proposition 4f.5.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace NK.NUV2.RouteB

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## A continuous additive homomorphism of `Γ`'s is `ℤ_ℓ`-linear -/

/-- **A continuous additive homomorphism between the pro-ℓ abelianisations `Γ` is `ℤ_ℓ`-linear.**

The scalar action of `ℤ_ℓ` on `Γ` is continuous (`NK.Reconstruct.continuous_smul_gamma`), so both
`a ↦ φ (a • x)` and `a ↦ a • φ x` are continuous functions of `a ∈ ℤ_ℓ`; they agree on the natural
numbers (`φ (n • x) = n • φ x` for an additive `φ`), which are dense in `ℤ_ℓ`
(`PadicInt.denseRange_natCast`), hence agree everywhere.  This is the same argument as
`NK.Reconstruct.dual_apply_smul`. -/
theorem continuous_addHom_smul {K K' L L' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsGalois K K'] [Field L] [NumberField L] [Field L'] [Algebra L L']
    [IsGalois L L'] {ℓ : ℕ} [Fact ℓ.Prime]
    (φ : Additive (Gamma K K' ℓ) →+ Additive (Gamma L L' ℓ)) (hφ : Continuous ⇑φ)
    (a : PadicInt ℓ) (x : Additive (Gamma K K' ℓ)) : φ (a • x) = a • φ x := by
  have h1 : Continuous fun b : PadicInt ℓ => φ (b • x) := hφ.comp (continuous_smul_gamma x)
  have h2 : Continuous fun b : PadicInt ℓ => b • φ x := continuous_smul_gamma (φ x)
  have hagree : (fun b : PadicInt ℓ => φ (b • x)) ∘ (Nat.cast : ℕ → PadicInt ℓ)
      = (fun b : PadicInt ℓ => b • φ x) ∘ (Nat.cast : ℕ → PadicInt ℓ) := by
    funext n
    show φ ((n : PadicInt ℓ) • x) = (n : PadicInt ℓ) • φ x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  exact congrFun (DenseRange.equalizer PadicInt.denseRange_natCast h1 h2 hagree) a

/-! ## The general base change as a linear map -/

/-- Continuity of `π_{M/K} : Γ_M → Γ_K` in the additive form used by the module structure. -/
theorem continuous_toAdditive_generalBaseChange (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous ⇑(MonoidHom.toAdditive (generalBaseChange K M h ℓ)) := by
  show Continuous fun x : Additive (Gamma ↥M.L Ω ℓ) =>
    Additive.ofMul (generalBaseChange K M h ℓ (Additive.toMul x))
  exact ((generalBaseChange_continuous K M h ℓ).comp continuous_toMul).comp continuous_ofMul

/-- **The general base change `π_{M/K} : Γ_M → Γ_K` as a `ℤ_ℓ`-linear map.**

`NK.Reconstruct.generalBaseChange` is a continuous homomorphism of pro-ℓ abelian groups, hence
`ℤ_ℓ`-linear by `continuous_addHom_smul`. -/
noncomputable def generalBaseChangeLinear (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Additive (Gamma ↥M.L Ω ℓ) →ₗ[PadicInt ℓ] Additive (Gamma ↥K.L Ω ℓ) where
  toFun := MonoidHom.toAdditive (generalBaseChange K M h ℓ)
  map_add' := fun x y => map_add _ x y
  map_smul' := fun a x =>
    continuous_addHom_smul (MonoidHom.toAdditive (generalBaseChange K M h ℓ))
      (continuous_toAdditive_generalBaseChange K M h ℓ) a x

@[simp] theorem generalBaseChangeLinear_apply (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L)
    (ℓ : ℕ) [Fact ℓ.Prime] (x : Additive (Gamma ↥M.L Ω ℓ)) :
    generalBaseChangeLinear K M h ℓ x
      = Additive.ofMul (generalBaseChange K M h ℓ (Additive.toMul x)) := rfl

/-! ## The descent to `Γ^{tf}` -/

/-- **The general base change maps the invisible subgroup into the invisible subgroup.**

A continuous character `g : Γ_K → ℤ_ℓ` pulls back along `π_{M/K}` to a continuous character
`dualMap g : Γ_M → ℤ_ℓ`, so an element of `Γ_M` invisible to every character of `Γ_M` is killed by
every character of `Γ_K` after base change, i.e. lies in the invisible subgroup of `Γ_K`. -/
theorem invisibleSubmodule_le_comap_generalBaseChange (K M : NumFieldIn ℚ Ω) (h : K.L ≤ M.L)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    invisibleSubmodule (K := ↥M.L) (K' := Ω) (ℓ := ℓ)
      ≤ Submodule.comap (generalBaseChangeLinear K M h ℓ)
          (invisibleSubmodule (K := ↥K.L) (K' := Ω) (ℓ := ℓ)) := by
  intro x hx
  rw [Submodule.mem_comap, mem_invisibleSubmodule_iff]
  intro g
  have hx' := (mem_invisibleSubmodule_iff (K := ↥M.L) (K' := Ω) (ℓ := ℓ) x).mp hx
    (dualMap ℓ (generalBaseChange K M h ℓ) (generalBaseChange_continuous K M h ℓ) g)
  rw [dualMap_apply] at hx'
  simpa [generalBaseChangeLinear_apply] using hx'

/-- **The general base change descends to the Hausdorff quotient, `ℤ_ℓ`-linearly.**

For number fields `K ⊆ M` of `Ω/ℚ` and a prime `ℓ`, the base change
`π_{M/K} : Γ_M → Γ_K` (`NK.Reconstruct.generalBaseChange`) maps the invisible subgroup of `Γ_M`
into that of `Γ_K` (`invisibleSubmodule_le_comap_generalBaseChange`), hence descends to a
`ℤ_ℓ`-linear map `HausQuot M →ₗ HausQuot K`. -/
theorem exists_hausPiGen (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K M : NK.Reconstruct.NumFieldIn ℚ Ω) (h : K.L ≤ M.L) (ℓ : ℕ) [Fact ℓ.Prime]
    [NumberField ↥K.L] [NumberField ↥M.L] :
    ∃ Φ : NK.Reconstruct.HausQuot ↥M.L Ω ℓ →ₗ[PadicInt ℓ] NK.Reconstruct.HausQuot ↥K.L Ω ℓ,
      ∀ x : Additive (NK.Reconstruct.Gamma ↥M.L Ω ℓ),
        Φ (NK.Reconstruct.hausMk (K := ↥M.L) (K' := Ω) (ℓ := ℓ) x)
          = NK.Reconstruct.hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
              (Additive.ofMul (NK.Reconstruct.generalBaseChange K M h ℓ (Additive.toMul x))) := by
  refine ⟨Submodule.mapQ _ _ (generalBaseChangeLinear K M h ℓ)
    (invisibleSubmodule_le_comap_generalBaseChange K M h ℓ), ?_⟩
  intro x
  rw [hausMk_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hausMk_apply,
    Submodule.mkQ_apply, generalBaseChangeLinear_apply]

end NK.NUV2.RouteB
