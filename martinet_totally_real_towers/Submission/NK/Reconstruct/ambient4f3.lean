import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.NumFieldIn
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.baseChange
import Submission.NK.Reconstruct.exists_tauStar
import Submission.NK.Reconstruct.exists_tauStar
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi

/-!
# The ambient setting of Shimizu's Proposition 4f.3

Proposition 4f.3 of Shimizu (arXiv:2009.10431) compares the base-change maps `π_{L/K₁}` and
`π_{L/τK₂}` for a finite Galois extension `L/ℚ` containing `K₁K₂`.  That needs `K₁` and `K₂` inside a
*common* separable closure `Ω`; this file sets up that setting using the vocabulary already built in
this area.

All fields are `FrobLevel ℚ Ω`: `K₁`, `K₂` (the two base fields, embedded in `Ω`) and `L` (a finite
Galois level over `ℚ` containing both).  Then

* `π_{L/K₁} = ambientPi K₁ L h₁ ℓ := gammaBaseChangeHom ℓ (levelExtend K₁ L h₁)` is the base change
  `Γ_L → Γ_{K₁}` (`levelExtend` is the level `L`, over `ℚ`, viewed over `↥K₁`), and similarly for
  `K₂`;
* `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` is `NK.Reconstruct.exists_gammaEquivOfPhi`;
* for a `ℚ`-algebra automorphism `θ` of `Ω` preserving the level `L`, `τ^* = τstar(θ)` is the outer
  action of `NK.Reconstruct.exists_tauStar`;
* `φ_τ := (σ̄ ∘ π_{L/K₁}) · (π_{L/K₂} ∘ τ^*)⁻¹` is the map whose non-vanishing is contradicted by
  the measure step (`NK.Reconstruct.exists_isFrobElementAt_notMem_iUnion_ker_of_infinite_range`,
  applied on the torsion-free quotient `Γ^TF` via `NK.Reconstruct.exists_gammaTF_lift` and
  `NK.Reconstruct.not_isOpen_ker_gammaTF_addHom`).

Everything in this file is a definition: the ambient setting and the maps `φ_τ`.  Proposition 4f.3
proper (that some `φ_τ` vanishes) and Lemmas 4f.4/4f.5 remain; see README §18.5.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The base change `π_{L/K} : Γ_L → Γ_K` in the ambient setting**: `L` is a finite Galois level
of `Ω/ℚ` containing `K`, viewed over `↥K` by `NK.Reconstruct.levelExtend`. -/
noncomputable def ambientPi (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) (ℓ : ℕ) :
    Gamma ↥L.L Ω ℓ →* Gamma ↥K.L Ω ℓ :=
  gammaBaseChangeHom (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h)

/-- **The map `φ_τ` of Shimizu's Proposition 4f.3**: for a `ℚ`-algebra automorphism `θ` of `Ω`
preserving the level `L`, the homomorphism
`Γ_L → Γ_{K₂}`, `γ ↦ (σ̄ ∘ π_{L/K₁})(γ) · (π_{L/K₂} ∘ τ^*)(γ)⁻¹`, where `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` is
the isomorphism induced by `ϕ` and `τ^*` is the outer action of `θ` on `Γ_L`. -/
noncomputable def phiTau (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L)
    (h₂ : K₂.L ≤ L.L)
    (ℓ : ℕ) (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (θ : Ω ≃+* Ω)
    (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) :
    Gamma ↥L.L Ω ℓ →* Gamma ↥K₂.L Ω ℓ :=
  ((σbar : Gamma ↥K₁.L Ω ℓ →* Gamma ↥K₂.L Ω ℓ).comp
      (ambientPi K₁ L h₁ ℓ)).comp
    (τstar.symm : Gamma ↥L.L Ω ℓ →* Gamma ↥L.L Ω ℓ)


/-! ## The Frobenius input (b) in the ambient `Γ` form -/

section Frob

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **`g` is the arithmetic Frobenius element at the place `A`** (at every finite level): for every
finite normal level `M/K` inside `K'`, the restriction of `g` to `M` is the Frobenius element at the
prime of `𝓞 M` cut out by `A`.  This is the place-wise form of
`NK.Reconstruct.IsFrobElementAt`. -/
def IsFrobElementAtPlace (A : FinitePlaceOf K K') (g : Gal(K'/K)) : Prop :=
  ∀ (M : FrobLevel K K'),
    NK.Chebotarev.IsFrobAt (primeOfLevel A.1 M.L (comap_level_ne_top A.2 M.L))
      (AlgEquiv.restrictNormalHom M.L g)

end Frob

/-- **Hypothesis (b) in the ambient `Γ` form** — Shimizu's Lemma 2.1.5: the isomorphism
`σ̄ : Γ_{K₁} ≅ Γ_{K₂}` matches the ℓ-adic Frobenius elements at corresponding places, i.e. for
corresponding places `A`, `σ̄ A` and Frobenius elements `g₁`, `g₂` there,
`σ̄(galToGamma g₁) = galToGamma g₂`.  In Shimizu's proof this is the identity
`σ̄(Frob_{𝔭₁}) = Frob_{σ_{*,K₁}(𝔭₁)}`. -/
def FrobeniusCorrespondenceGamma (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ)
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ)
    (placeMap : FinitePlaceOf ↥K₁.L Ω ≃ FinitePlaceOf ↥K₂.L Ω) : Prop :=
  ∀ (A : FinitePlaceOf ↥K₁.L Ω) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
    IsFrobElementAtPlace A g₁ → IsFrobElementAtPlace (placeMap A) g₂ →
      σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁)
        = galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂

end NK.Reconstruct
