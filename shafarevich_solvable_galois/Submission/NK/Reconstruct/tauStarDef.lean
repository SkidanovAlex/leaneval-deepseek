import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.exists_tauStar
import Submission.NK.Reconstruct.gammaHaus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The outer action `τ^*` of an automorphism preserving a level, as a function

`NK.Reconstruct.exists_tauStar` produces, for a ring automorphism `θ` of the big field `K'` which
preserves a finite level `L` as a set, an automorphism `τ^*` of `Γ_L` with
`τ^*(galToGamma g) = galToGamma (g ↦ θ g θ⁻¹)`.  This file fixes a *choice* of such an automorphism
(`NK.Reconstruct.tauStar`), so that `τ^*` can be used as a function of `θ` — in particular in the
statements of Shimizu's Proposition 4f.3, where the finitely many `τ` of `G(L/ℚ)` have to be
substituted into the maps `φ_τ`.

## Contents

* `NK.Reconstruct.tauStar` — the chosen `τ^*`;
* `NK.Reconstruct.tauStar_galToGamma` — its defining property;
* `NK.Reconstruct.tauStar_comp` — `τ^*` is a homomorphism in the automorphism (`θ` composed with
  an element of `Gal(K'/L)` acts trivially, so `τ^*` depends only on `θ|_L`).

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Prop. 4f.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']

/-- **A choice of the outer action `τ^*`** of an automorphism `θ` of `K'` preserving a level `L` as
a set: an automorphism of `Γ_L` with `τ^*(galToGamma g) = galToGamma (θ g θ⁻¹)`. -/
noncomputable def tauStar (L : IntermediateField K K') [NumberField ↥L] (ℓ : ℕ) [Fact ℓ.Prime]
    (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) : Gamma ↥L K' ℓ ≃* Gamma ↥L K' ℓ :=
  (exists_tauStar L ℓ θ hθ).choose

/-- **The defining property of `τ^*`.** -/
theorem tauStar_galToGamma (L : IntermediateField K K') [NumberField ↥L] (ℓ : ℕ) [Fact ℓ.Prime]
    (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (g : Gal(K'/↥L)) :
    tauStar L ℓ θ hθ (galToGamma (K := ↥L) (K' := K') ℓ g)
      = galToGamma (K := ↥L) (K' := K') ℓ (ringConjHom L θ hθ g) :=
  (exists_tauStar L ℓ θ hθ).choose_spec g

end NK.Reconstruct
