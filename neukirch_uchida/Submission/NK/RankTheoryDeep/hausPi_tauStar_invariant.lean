import Mathlib
import Submission.NK.Reconstruct.hausPi
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.gammaSmul
import Submission.NK.Reconstruct.thetaGammaTransport_gen
import Submission.NK.RankTheoryDeep.tauStar_gamma_eq_one

/-!
# `π_{L/K}` is invariant under the outer action `τ^*`

Let `K ⊆ L` be a finite number-field level of a separable closure `Ω` of `ℚ` with `L/ℚ` finite
Galois, let `ℓ` be a prime and let `θ : Ω ≃+* Ω` be a ring automorphism which **preserves** `L`
(as a set) and **fixes `K` pointwise**.  Then the outer action `τ^* = tauStar L ℓ θ hθ` on
`Γ_L = Gamma ↥L.L Ω ℓ` (Shimizu, Prop. 4f.3) is invisible in `Γ_K^{tf}` after base change:

  `hausPi K L h ℓ (τ^* γ) = hausPi K L h ℓ γ`  for all `γ ∈ Γ_L`.

The reason is group-theoretic: `θ` is an element of `Gal(Ω/K)` (it fixes `K`), so conjugation by
`θ` is an *inner* automorphism of `Gal(Ω/K)` and hence acts trivially on the abelianisation, while
`π_{L/K}` is induced by the inclusion `Gal(Ω/L) ≤ Gal(Ω/K)`.  Everything descends to the
Hausdorff torsion-free quotient.

## Contents

* `NK.RankTheoryDeep.galToGamma_conj` — inner automorphisms are invisible in `Γ_K`;
* `NK.RankTheoryDeep.baseChangeLinear_ofMul` — the base change of a multiplicative element;
* `NK.RankTheoryDeep.ambientPi_tauStar_eq_self` — the identity `π_{L/K} ∘ τ^* = π_{L/K}` on `Γ`;
* `NK.RankTheoryDeep.hausPi_tauStar_invariant` — its descent to `Γ_K^{tf}`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u

namespace NK.RankTheoryDeep

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

/-- **Inner automorphisms are invisible in `Γ_K`.**  Conjugation in `Gal(K'/K)` becomes trivial in
the abelianisation, and `galToGamma` factors through the abelianisations of the finite levels. -/
theorem galToGamma_conj {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (a b : Gal(K'/K)) :
    galToGamma (K := K) (K' := K') ℓ (a * b * a⁻¹) = galToGamma (K := K) (K' := K') ℓ b := by
  refine Gamma.ext (fun M => ?_)
  rw [galToGamma_proj, galToGamma_proj]
  show ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.L
        (a * b * a⁻¹)))
      = ellComp ℓ (Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.L b))
  rw [show Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.L (a * b * a⁻¹))
        = Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') M.L b) from by
    simp only [map_mul, map_inv]
    exact abelianization_of_conj _ _]

/-- The base change of a multiplicative element, in additive notation. -/
theorem baseChangeLinear_ofMul {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L)
    (ℓ : ℕ) [Fact ℓ.Prime] (y : Gamma ↥L.L Ω ℓ) :
    baseChangeLinear K L h ℓ (Additive.ofMul y)
      = Additive.ofMul (ambientPi K L h ℓ y) := by
  rw [baseChangeLinear_apply]
  rfl

/-- **The base change `π_{L/K}` is invariant under the outer action `τ^*`** of a ring automorphism
`θ` of `Ω` which preserves `L` and fixes `K` pointwise: at the level of `Γ`, `π_{L/K} ∘ τ^* =
π_{L/K}`. -/
theorem ambientPi_tauStar_eq_self {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (θ : Ω ≃+* Ω)
    (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) (hθK : ∀ x : Ω, x ∈ K.L → θ x = x)
    (x : Gamma ↥L.L Ω ℓ) :
    ambientPi K L h ℓ (tauStar (L.L : IntermediateField ℚ Ω) ℓ θ hθ x)
      = ambientPi K L h ℓ x := by
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  haveI hgalK : IsGalois ↥K.L Ω := inferInstance
  -- `θ` viewed as an element of `Gal(Ω/↥K.L)`
  let θK : Ω ≃ₐ[↥K.L] Ω := { toRingEquiv := θ, commutes' := fun c => hθK c.1 c.2 }
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥L.L) (K' := Ω) ℓ x
  rw [tauStar_galToGamma,
    ambientPi_galToGamma K L h ℓ (ringConjHom L.L (θ : Ω ≃+* Ω) hθ σ),
    ambientPi_galToGamma K L h ℓ σ]
  -- conjugation by `θ` on `Gal(Ω/↥K.L)`
  have hconj : galRestrict h (ringConjHom (L.L : IntermediateField ℚ Ω) (θ : Ω ≃+* Ω) hθ σ)
      = θK * galRestrict h σ * θK⁻¹ := by
    ext z
    simp only [galRestrict_apply, ringConjHom_apply, AlgEquiv.mul_apply, AlgEquiv.coe_inv]
    rfl
  rw [hconj, galToGamma_conj]

theorem hausPi_tauStar_invariant {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    [IsSepClosure ↥K.L Ω] (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] (θ : Ω ≃+* Ω)
    (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) (hθK : ∀ x : Ω, x ∈ K.L → θ x = x)
    (x : NK.Reconstruct.Gamma ↥L.L Ω ℓ) :
    NK.Reconstruct.hausPi K L h ℓ
        (NK.Reconstruct.hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ)
          (Additive.ofMul (NK.Reconstruct.tauStar (L.L : IntermediateField ℚ Ω) ℓ θ hθ x)))
      = NK.Reconstruct.hausPi K L h ℓ
          (NK.Reconstruct.hausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul x)) := by
  have hγ := ambientPi_tauStar_eq_self K L h ℓ θ hθ hθK x
  rw [hausPi_hausMk, hausPi_hausMk, baseChangeLinear_ofMul, baseChangeLinear_ofMul, hγ]

end NK.RankTheoryDeep
