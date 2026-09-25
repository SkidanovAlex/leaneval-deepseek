import Submission.NK.Reconstruct.lemma4f4

/-!
# The pointwise criterion of Shimizu's Lemma 4f.4, for arbitrary base fields

Shimizu's Lemma 4f.4 (arXiv:2009.10431) says: if `K₁, K₂` are number fields, `L/K₁K₂` is a finite
extension, and `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` satisfies `σ̄ ∘ π_{L/K₁} = π_{L/K₂}`, then
`K₁^{(∞,ℓ)}K₂ = K₁K₂^{(∞,ℓ)}`.

The proof (see `NK.Reconstruct.lemma4f4` for the formalised version with all three fields finite
Galois over `ℚ`) has three steps:

1. at the auxiliary level `L`, the identity `σ̄ ∘ π_{L/K₁} = π_{L/K₂}` implies the pointwise
   criterion `gammaHausMk (galToGamma (h|_{K₁})) = 1 ↔ gammaHausMk (galToGamma (h|_{K₂})) = 1` for
   every automorphism `h` of `Ω` over `L`;
2. **descent**: the same criterion for automorphisms over the compositum `K₁L ⊔ K₂L`;
3. the criterion at the compositum is equivalent to the equality
   `K₁^{(∞,ℓ)}K₂ = K₁K₂^{(∞,ℓ)}` of the two composita, by the Galois correspondence (fixing
   subgroups).

Step 1 is proved here **for arbitrary number fields `K₁, K₂ ⊆ L` as base fields** — it uses only
`NK.Reconstruct.ambientPi_galToGamma` and `NK.Reconstruct.gammaHausMk_sbar_eq_one_iff`, both of
which are available for arbitrary base fields (§24.3 of the README).  Step 3 is likewise
independent of the base fields.  Step 2 is the place where the *general base change*
`π_{M/K}` for an arbitrary finite extension `M/K` is needed: for the level `N := K₁L ⊔ K₂L` (which
is in general *not* Galois over `ℚ`), one has to pass from the identity at `Γ_L` to the identity at
`Γ_N`, which the formalised proof does by writing the elements of `Γ_N` (up to a power, using the
finiteness of the cokernel of `Γ_L → Γ_N`) as images under `π_{L/N} = ambientPi N L` and applying
the transitivity `π_{L/K} = π_{N/K} ∘ π_{L/N}` — and `π_{N/K}` is what is missing.  See README §24.4
for the construction of `π_{M/K}` that is to be formalised.

## Contents

* `NK.Reconstruct.hausMk_galToGamma_iff_general` — step 1 for arbitrary base fields.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Lemma 4f.4.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open NK.Chebotarev
open scoped NumberField

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Step 1 of Shimizu's Lemma 4f.4, for arbitrary base fields.**  Let `K₁, K₂ ⊆ L` be number
fields with `L/ℚ` finite Galois (so that `ambientPi K_i L h_i ℓ = π_{L/K_i}` is available), and let
`σ̄ : Γ_{K₁} ≅ Γ_{K₂}` satisfy Shimizu's identity at the level `L`.  Then for every automorphism `h`
of `Ω` over `L`, the classes `galToGamma (h|_{K₁})` and `galToGamma (h|_{K₂})` are simultaneously
invisible in `Γ_{K₁}^{tf}`, resp. `Γ_{K₂}^{tf}`. -/
theorem hausMk_galToGamma_iff_general (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥(K₁.L) Ω] [IsSepClosure ↥(K₂.L) Ω] [IsSepClosure ↥L.L Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥(K₁.L) Ω ℓ ≃* Gamma ↥(K₂.L) Ω ℓ) (hσbar : Continuous ⇑σbar)
    (heq : ∀ (γ : Gamma ↥(L.L) Ω ℓ),
      gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ) (ambientPi K₂ L h₂ ℓ γ))
    (h : Ω ≃ₐ[↥L.L] Ω) :
    gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ (galRestrict (E := K₁.L) (F := L.L) h₁ h)) = 1
      ↔ gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ (galRestrict (E := K₂.L) (F := L.L) h₂ h)) = 1 := by
  -- Shimizu's identity, evaluated at `galToGamma h`, rewritten by `ambientPi_galToGamma`.
  have hhev := heq (galToGamma (K := ↥L.L) (K' := Ω) ℓ h)
  rw [ambientPi_galToGamma K₁ L h₁ ℓ h, ambientPi_galToGamma K₂ L h₂ ℓ h] at hhev
  constructor
  · intro h1
    have h2 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
        (σbar (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
          (galRestrict (E := K₁.L) (F := L.L) h₁ h))) = 1 :=
      (gammaHausMk_sbar_eq_one_iff K₁ K₂ ℓ σbar hσbar _).mpr h1
    rwa [hhev] at h2
  · intro h2
    have h1 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
        (σbar (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
          (galRestrict (E := K₁.L) (F := L.L) h₁ h))) = 1 := by
      rw [hhev]; exact h2
    exact (gammaHausMk_sbar_eq_one_iff K₁ K₂ ℓ σbar hσbar _).mp h1

end NK.Reconstruct
