import Submission.NK.Reconstruct.levelInfinity
import Submission.NK.Reconstruct.torsionFreeGamma
import Submission.NK.Reconstruct.lemma4f4
import Submission.NK.Reconstruct.NumFieldIn

/-!
# Shimizu's Proposition 4f.5, as a named input

Shimizu (arXiv:2009.10431, §4, Proposition 4f.5): *for `i = 1, 2` let `K_i` be a number field, and
assume that (a) one of the `K_i` has a complex prime, and (b) there is a finite extension
`L/K₁K₂` with `L/ℚ` Galois and `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` for some prime `ℓ`.  Then
`K₁ = K₂`.*

This is the last ingredient of the Shimizu §4 assembly beyond Proposition 4f.3 (proved here) and
Lemma 4f.4 (proved here).  Its proof in Shimizu's paper goes:

* from the field equality, `ker(π_{L/K₁}) = ker(π_{L/K₂}) =: N` in `Γ_L`;
* `res_L^{K_i}` factors through `Hom_{cts}(Γ_L/N, ℤ_ℓ)` (⊆ `Hom_{cts}(Γ_L, ℤ_ℓ)`), whose
  `ℤ_ℓ`-rank is `r_ℓ(K_i)`;
* the two images intersect in `Hom_{cts}(Γ_L/N, ℤ_ℓ)` and have rank `r_ℓ(K₁) = r_ℓ(K₂)`;
* by **Lemma 4f.1** (`NK.Reconstruct.lemma4f1_of_transfer`, whose finite-cokernel half consumes
  the transfer input `NK.Reconstruct.TransferInput`),
  `im(res^{K₁}) ∩ im(res^{K₂}) ⊆ Hom_{cts}(Γ_L,ℤ_ℓ)^{G(L/K₁)} ∩ Hom_{cts}(Γ_L,ℤ_ℓ)^{G(L/K₂)}
    = Hom_{cts}(Γ_L,ℤ_ℓ)^{G(L/K₁∩K₂)}`,
  so `r_ℓ(K₁) = r_ℓ(K₂) = r_ℓ(K₁ ∩ K₂)`;
* **Lemma 4f.2** (`NK.Reconstruct.RankStrictMonoInput`) applied to `K₁ ∩ K₂ ⊆ K₁` and to
  `K₁ ∩ K₂ ⊆ K₂` (both nontrivial only if the inclusion is strict, and `K₁` has a complex prime)
  forces `K₁ = K₁ ∩ K₂` and `K₂ = K₁ ∩ K₂`.

The formalisation of the bookkeeping in the first three bullets — the `G(L/K)`-action on `Γ_L` and
on its continuous dual, the identification
`Hom(Γ_L,ℤ_ℓ)^{G(L/K)} ≅ Hom((Γ_L)_{G(L/K)}, ℤ_ℓ)`, and the base change `π_{L/K}` as the map
induced by `G_L ⊆ G_K` — is the remaining work recorded in README §11.5 and §20.5.  It is isolated
here as the named predicate `NK.Reconstruct.Fourf5Input`, so that the assembly of Shimizu's
Theorem 4.0 can be stated and proved modulo it. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped NumberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Proposition 4f.5** (arXiv:2009.10431, §4), as a named input.

For finite Galois levels `K₁, K₂ ⊆ L` of `Ω/ℚ`: if one of the `K_i` has a complex prime and
`K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`, then `K₁ = K₂`.

The named inputs which discharge it are recorded in the module docstring; see also README §20.5. -/
def Fourf5Input (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K₁ K₂ L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω],
    (levelInfinityOf (NumFieldIn.ofFrobLevel K₁) ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (L.L ⊔ levelInfinityOf (NumFieldIn.ofFrobLevel K₂) ℓ : IntermediateField ℚ Ω) →
    (∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v) →
    K₁.L = K₂.L

end NK.Reconstruct
