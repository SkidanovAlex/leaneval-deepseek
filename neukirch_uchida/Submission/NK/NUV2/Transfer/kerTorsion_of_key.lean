import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.Reconstruct.hausPi
import Submission.NK.Reconstruct.generalBaseChange_galToGamma
import Submission.NK.RankTheoryDeep.hausPi_tauStar_invariant
import Submission.NK.ShimizuRank.hausQuot_torsionFree
import Submission.NK.NUV2.Transfer.exists_tauStarAction
import Submission.NK.NUV2.Transfer.exists_ver_norm
import Submission.NK.NUV2.gal_generation

/-!
# The torsion form of Shimizu's rank step, from the transfer/norm input

In Shimizu's situation (`M = K₁ ⊓ K₂`, `L ⊇ K₁K₂` a finite Galois level of `Ω/ℚ`,
`K₁^{(∞,2)}L = LK₂^{(∞,2)}`), every element of `ker (hausPi M L hM' 2)` is carried into
`ker (hausPi K₁ L h₁ 2)` by a power of `2`.

The single arithmetic input is the *transfer/norm* statement `hkey` (proved in the sibling module
`NK.NUV2.Transfer.exists_ver_norm`): the norm `N(x) = Σ_{g ∈ Gal(L/M)} g^* x` of an element whose
base change to `M` is invisible is itself invisible over `L`.

The remainder is group theory: the set of `τ ∈ Gal(L/ℚ)` under which `π_{L/K₁}` is invariant is a
*subgroup* containing `Gal(L/K₁)` and `Gal(L/K₂)`, hence (by `NK.NUV2.gal_generation`) contains
`Gal(L/M)`; consequently `π_{L/K₁}(N x) = [L : M] · π_{L/K₁}(x)`, and the left side vanishes because
`N x` is invisible.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace NK.NUV2

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **`ambientPi` agrees with `generalBaseChange`** for a finite Galois level over a number field. -/
theorem ambientPi_eq_generalBaseChange (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K.L Ω] (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    ambientPi K L h ℓ = generalBaseChange K (NumFieldIn.ofFrobLevel L) h ℓ := by
  refine MonoidHom.ext (fun x => ?_)
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥L.L) (K' := Ω) ℓ x
  rw [ambientPi_galToGamma K L h ℓ σ,
    generalBaseChange_galToGamma K (NumFieldIn.ofFrobLevel L) h ℓ σ]

/-- **The transfer image of an invisible element is invisible**: continuous homomorphisms of
profinite groups map invisible elements to invisible elements, since continuous characters pull
back. -/
theorem mem_invisible_of_mem_invisible (M L : NumFieldIn ℚ Ω)
    [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω]
    (ver : Gamma ↥M.L Ω 2 →* Gamma ↥L.L Ω 2) (hver : Continuous ⇑ver)
    {y : Additive (Gamma ↥M.L Ω 2)}
    (hy : y ∈ invisibleSubmodule (K := ↥M.L) (K' := Ω) (ℓ := 2)) :
    Additive.ofMul (ver (Additive.toMul y)) ∈ invisibleSubmodule (K := ↥L.L) (K' := Ω) (ℓ := 2) := by
  rw [mem_invisibleSubmodule_iff] at hy ⊢
  intro f
  set φ : Dual (Gamma ↥M.L Ω 2) 2 :=
    ⟨(f : Additive (Gamma ↥L.L Ω 2) →+ PadicInt 2).comp (MonoidHom.toAdditive ver), by
      show Continuous ((f : Additive (Gamma ↥L.L Ω 2) →+ PadicInt 2) ∘
        ⇑(MonoidHom.toAdditive ver))
      exact f.2.comp hver⟩ with hφ
  have h0 : (φ : Additive (Gamma ↥M.L Ω 2) →+ PadicInt 2) y = 0 := hy φ
  simpa [hφ, MonoidHom.toAdditive_apply_apply] using h0

/-- **The transfer/norm input** (proved in the sibling module `NK.NUV2.Transfer.exists_ver_norm`):
the norm of an element whose base change to `M` is invisible is invisible over `L`. -/
theorem norm_mem_invisible (M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
    [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]
    (ρ : Gal(↥L.L/ℚ) →* (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2))
    (hρ : ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
        (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
        ρ τ = tauStar L.L 2 θ hθ) :
    ∀ X : Gamma ↥L.L Ω 2,
      Additive.ofMul (generalBaseChange M (NumFieldIn.ofFrobLevel L) hML 2 X)
        ∈ invisibleSubmodule (K := ↥M.L) (K' := Ω) (ℓ := 2) →
      (∑ g : Gal(↥L.L/↥M.L), Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) X))
        ∈ invisibleSubmodule (K := ↥L.L) (K' := Ω) (ℓ := 2) := by
  have hsubA : Subsingleton (Algebra ℚ ↥L.L) := inferInstance
  have heqA : L.L.algebra' = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI hNormL : Normal ℚ ↥L.L :=
    cast (congrArg (fun a => @Normal ℚ (↥L.L) _ _ a) heqA) L.normal
  obtain ⟨ver, hver, hnorm⟩ :=
    NK.NUV2.Transfer.exists_ver_norm Ω M L hML ρ hρ
  intro X hX
  rw [hnorm X]
  exact mem_invisible_of_mem_invisible M (NumFieldIn.ofFrobLevel L) ver hver hX

/-! ## The main theorem -/

/-- **The torsion form of Shimizu's rank step.** -/
theorem kerTorsion_of_key (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω]
    (hM : M.L = K₁.L ⊓ K₂.L) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hM' : M.L ≤ L.L)
    (hsup : (levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = L.L ⊔ levelInfinityOf K₂ 2)
    [Algebra ↥M.L ↥L.L] [Algebra ↥K₁.L ↥L.L] [Algebra ↥K₂.L ↥L.L]
    [IsScalarTower ↥M.L ↥L.L Ω] [IsScalarTower ↥K₁.L ↥L.L Ω] [IsScalarTower ↥K₂.L ↥L.L Ω]
    (ρ : Gal(↥L.L/ℚ) →* (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2))
    (hρ : ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
        (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
        ρ τ = tauStar L.L 2 θ hθ) :
    ∀ x ∈ LinearMap.ker (hausPi M L hM' 2),
      ∃ n : ℕ, (2 : ℤ_[2]) ^ n • x ∈ LinearMap.ker (hausPi K₁ L h₁ 2) := by
  have hsubA : Subsingleton (Algebra ℚ ↥L.L) := inferInstance
  have heqA : L.L.algebra' = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI hNormL : Normal ℚ ↥L.L :=
    cast (congrArg (fun a => @Normal ℚ (↥L.L) _ _ a) heqA) L.normal
  let Φ : Additive (Gamma ↥L.L Ω 2) →ₗ[PadicInt 2] HausQuot ↥K₁.L Ω 2 :=
    (hausPi K₁ L h₁ 2).comp (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2))
  have hΦapp : ∀ Y : Additive (Gamma ↥L.L Ω 2), Φ Y = hausPi K₁ L h₁ 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) Y) :=
    fun Y => rfl
  -- invariance under `Gal(L/K₁)`
  have hinv₁ : ∀ (g₁ : Gal(↥L.L/↥K₁.L)) (Y : Gamma ↥L.L Ω 2),
      Φ (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₁) Y)) = Φ (Additive.ofMul Y) := by
    intro g₁ Y
    obtain ⟨θ, hθ, hθτ⟩ :=
      NK.NUV2.Transfer.exists_ringEquiv_extends_of_isSepClosure Ω L.L
        (AlgEquiv.restrictScalars ℚ g₁)
    have hρθ : ρ (AlgEquiv.restrictScalars ℚ g₁) = tauStar L.L 2 θ hθ := hρ _ θ hθ hθτ
    have hθK : ∀ x : Ω, x ∈ K₁.L → θ x = x := by
      intro x hx
      have hxL : x ∈ L.L := h₁ hx
      have key : ((algebraMap ↥K₁.L ↥L.L (⟨x, hx⟩ : ↥K₁.L) : ↥L.L) : Ω) = x := by
        rw [← IntermediateField.algebraMap_apply (L.L)
              (algebraMap ↥K₁.L ↥L.L (⟨x, hx⟩ : ↥K₁.L)),
            ← IsScalarTower.algebraMap_apply ↥K₁.L ↥L.L Ω,
            IntermediateField.algebraMap_apply (K₁.L) (⟨x, hx⟩ : ↥K₁.L)]
      have hmem : (⟨x, hxL⟩ : ↥L.L) = algebraMap ↥K₁.L ↥L.L (⟨x, hx⟩ : ↥K₁.L) := by
        apply Subtype.ext
        show ((⟨x, hxL⟩ : ↥L.L) : Ω) = ((algebraMap ↥K₁.L ↥L.L (⟨x, hx⟩ : ↥K₁.L) : ↥L.L) : Ω)
        rw [key]
      have hcomm : (AlgEquiv.restrictScalars ℚ g₁) (⟨x, hxL⟩ : ↥L.L) = ⟨x, hxL⟩ := by
        rw [hmem]
        exact g₁.commutes (⟨x, hx⟩ : ↥K₁.L)
      calc θ x = θ ((⟨x, hxL⟩ : ↥L.L) : Ω) := rfl
        _ = (((AlgEquiv.restrictScalars ℚ g₁) ⟨x, hxL⟩ : ↥L.L) : Ω) := hθτ ⟨x, hxL⟩
        _ = ((⟨x, hxL⟩ : ↥L.L) : Ω) := by rw [hcomm]
        _ = x := rfl
    rw [hΦapp, hΦapp, hρθ]
    exact NK.RankTheoryDeep.hausPi_tauStar_invariant K₁ L h₁ 2 θ hθ hθK Y
  -- invariance under `Gal(L/K₂)`, transported along the equality of the kernels
  have hinv₂ : ∀ (g₂ : Gal(↥L.L/↥K₂.L)) (Y : Gamma ↥L.L Ω 2),
      Φ (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y)) = Φ (Additive.ofMul Y) := by
    intro g₂ Y
    obtain ⟨θ, hθ, hθτ⟩ :=
      NK.NUV2.Transfer.exists_ringEquiv_extends_of_isSepClosure Ω L.L
        (AlgEquiv.restrictScalars ℚ g₂)
    have hρθ : ρ (AlgEquiv.restrictScalars ℚ g₂) = tauStar L.L 2 θ hθ := hρ _ θ hθ hθτ
    have hθK : ∀ x : Ω, x ∈ K₂.L → θ x = x := by
      intro x hx
      have hxL : x ∈ L.L := h₂ hx
      have key : ((algebraMap ↥K₂.L ↥L.L (⟨x, hx⟩ : ↥K₂.L) : ↥L.L) : Ω) = x := by
        rw [← IntermediateField.algebraMap_apply (L.L)
              (algebraMap ↥K₂.L ↥L.L (⟨x, hx⟩ : ↥K₂.L)),
            ← IsScalarTower.algebraMap_apply ↥K₂.L ↥L.L Ω,
            IntermediateField.algebraMap_apply (K₂.L) (⟨x, hx⟩ : ↥K₂.L)]
      have hmem : (⟨x, hxL⟩ : ↥L.L) = algebraMap ↥K₂.L ↥L.L (⟨x, hx⟩ : ↥K₂.L) := by
        apply Subtype.ext
        show ((⟨x, hxL⟩ : ↥L.L) : Ω) = ((algebraMap ↥K₂.L ↥L.L (⟨x, hx⟩ : ↥K₂.L) : ↥L.L) : Ω)
        rw [key]
      have hcomm : (AlgEquiv.restrictScalars ℚ g₂) (⟨x, hxL⟩ : ↥L.L) = ⟨x, hxL⟩ := by
        rw [hmem]
        exact g₂.commutes (⟨x, hx⟩ : ↥K₂.L)
      calc θ x = θ ((⟨x, hxL⟩ : ↥L.L) : Ω) := rfl
        _ = (((AlgEquiv.restrictScalars ℚ g₂) ⟨x, hxL⟩ : ↥L.L) : Ω) := hθτ ⟨x, hxL⟩
        _ = ((⟨x, hxL⟩ : ↥L.L) : Ω) := by rw [hcomm]
        _ = x := rfl
    have h₂inv : hausPi K₂ L h₂ 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y)))
        = hausPi K₂ L h₂ 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul Y)) := by
      rw [hρθ]
      exact NK.RankTheoryDeep.hausPi_tauStar_invariant K₂ L h₂ 2 θ hθ hθK Y
    have hker := ker_hausPi_eq_of_levelInfinity_eq K₁ K₂ L h₁ h₂ 2 hsup
    have hzero : hausPi K₂ L h₂ 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y)
        - Additive.ofMul Y)) = 0 := by
      rw [map_sub, map_sub, h₂inv, sub_self]
    have hzero₁ : hausPi K₁ L h₁ 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y)
        - Additive.ofMul Y)) = 0 := by
      have hmem : hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y) - Additive.ofMul Y)
          ∈ LinearMap.ker (hausPi K₂ L h₂ 2) := LinearMap.mem_ker.mpr hzero
      rw [← hker] at hmem
      exact LinearMap.mem_ker.mp hmem
    have hfin : Φ (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g₂) Y)) - Φ (Additive.ofMul Y)
        = 0 := by
      rw [← map_sub, hΦapp]
      exact hzero₁
    exact sub_eq_zero.mp hfin
  -- the subgroup of `Gal(L/ℚ)` under which `π_{L/K₁}` is invariant
  have hS : ∀ g : Gal(↥L.L/↥M.L), ∀ Y : Gamma ↥L.L Ω 2,
      Φ (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) Y)) = Φ (Additive.ofMul Y) := by
    let S : Subgroup (↥L.L ≃ₐ[ℚ] ↥L.L) :=
      { carrier := {τ | ∀ Y : Gamma ↥L.L Ω 2,
          Φ (Additive.ofMul (ρ τ Y)) = Φ (Additive.ofMul Y)}
        mul_mem' := by
          intro a b ha hb Y
          rw [map_mul, MulAut.mul_apply]
          exact (ha (ρ b Y)).trans (hb Y)
        one_mem' := by
          intro Y
          rw [map_one, MulAut.one_apply]
        inv_mem' := by
          intro a ha Y
          have hτY : Φ (Additive.ofMul (ρ a (ρ a⁻¹ Y))) = Φ (Additive.ofMul (ρ a⁻¹ Y)) := ha _
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at hτY
          exact hτY.symm }
    have hgen : ∀ g : Gal(↥L.L/↥M.L),
        (AlgEquiv.restrictScalars ℚ g : ↥L.L ≃ₐ[ℚ] ↥L.L) ∈ S :=
      gal_generation Ω K₁ K₂ M L hM h₁ h₂ S (fun g₁ => hinv₁ g₁) (fun g₂ => hinv₂ g₂)
    intro g Y
    exact hgen g Y
  -- the arithmetic input
  have hkey := norm_mem_invisible M L hM' ρ hρ
  intro x hx
  obtain ⟨Xa, hXa⟩ := hausMk_surjective (K := ↥L.L) (K' := Ω) (ℓ := 2) x
  set X : Gamma ↥L.L Ω 2 := Additive.toMul Xa with hXdef
  have hX : hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul X) = x := by
    rw [hXdef, ofMul_toMul]
    exact hXa
  have hbase : Additive.ofMul (generalBaseChange M (NumFieldIn.ofFrobLevel L) hM' 2 X)
      ∈ invisibleSubmodule (K := ↥M.L) (K' := Ω) (ℓ := 2) := by
    have h0 : hausPi M L hM' 2 (hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2) (Additive.ofMul X)) = 0 := by
      rw [hX]
      exact LinearMap.mem_ker.mp hx
    rw [hausPi_hausMk, baseChangeLinear_apply, ambientPi_eq_generalBaseChange M L hM' 2] at h0
    exact (hausMk_eq_zero_iff _).mp h0
  have hsum := hkey X hbase
  have hΦsum : Φ (∑ g : Gal(↥L.L/↥M.L),
      Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) X)) = 0 := by
    have h1 : hausMk (K := ↥L.L) (K' := Ω) (ℓ := 2)
        (∑ g : Gal(↥L.L/↥M.L), Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) X)) = 0 :=
      (hausMk_eq_zero_iff _).mpr hsum
    rw [hΦapp, h1]
    exact map_zero _
  have hsplit : Φ (∑ g : Gal(↥L.L/↥M.L),
      Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) X))
      = (Nat.card (Gal(↥L.L/↥M.L)) : ℤ_[2]) • Φ (Additive.ofMul X) := by
    rw [map_sum]
    rw [show (∑ g : Gal(↥L.L/↥M.L),
        Φ (Additive.ofMul (ρ (AlgEquiv.restrictScalars ℚ g) X)))
        = ∑ _g : Gal(↥L.L/↥M.L), Φ (Additive.ofMul X) from
      Finset.sum_congr rfl (fun g _ =>
        hS g X)]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
    congr 1
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hzero : (Nat.card (Gal(↥L.L/↥M.L)) : ℤ_[2]) • Φ (Additive.ofMul X) = 0 := by
    rw [← hsplit]
    exact hΦsum
  haveI hTF : Module.IsTorsionFree (PadicInt 2) (HausQuot ↥K₁.L Ω 2) :=
    NK.ShimizuRank.hausQuot_torsionFree (K := ↥K₁.L) (K' := Ω) (ℓ := 2)
  have hcard : (Nat.card (Gal(↥L.L/↥M.L)) : ℤ_[2]) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨Nonempty.intro (1 : Gal(↥L.L/↥M.L)), inferInstance⟩
  have hΦX : Φ (Additive.ofMul X) = 0 := (smul_eq_zero.mp hzero).resolve_left hcard
  refine ⟨0, ?_⟩
  rw [pow_zero, one_smul, ← hX]
  rw [LinearMap.mem_ker, ← hΦapp]
  exact hΦX

end NK.NUV2
