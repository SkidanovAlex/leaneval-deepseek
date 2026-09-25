import Submission.NK.Reconstruct.generalDescent
import Submission.NK.Reconstruct.lemma4f4_of_criterion

/-!
# Shimizu's Lemma 4f.4 for arbitrary number fields as base fields

Shimizu (arXiv:2009.10431, §4, Lemma 4f.4): for number fields `K₁, K₂`, a finite extension
`L/K₁K₂` and a continuous isomorphism `σ̄ : Γ_{K₁} ≅ Γ_{K₂}` with `σ̄ ∘ π_{L/K₁} = π_{L/K₂}`
(modulo the invisible subgroup), one has

  `K₁^{(∞,ℓ)}K₂ = K₁K₂^{(∞,ℓ)}`.

This file assembles the general form of the Lemma from the three ingredients already proved:

* `NK.Reconstruct.hausMk_galToGamma_iff_general` — step 1 (the criterion at the auxiliary level
  `L`), available for arbitrary base fields;
* `NK.Reconstruct.hausMk_heq_of_le_general` — step 2 (the descent to the middle field
  `N = K₁.L ⊔ K₂.L`, which is not normal over `K₁.L`), via the general base change `π_{M/K}`;
* `NK.Reconstruct.lemma4f4_of_criterion` — step 3 (the Galois correspondence at `N`).

The middle field is packaged as a `NumFieldIn` via `NK.Reconstruct.NumFieldIn.supOf`, inside the
auxiliary Galois level `L` (which contains it).

## Contents

* **`NK.Reconstruct.lemma4f4_gen`** — Shimizu's Lemma 4f.4, base fields arbitrary.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Lemma 4f.4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Lemma 4f.4 for arbitrary number fields as base fields.** -/
theorem lemma4f4_gen (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (heq : ∀ (γ : Gamma ↥L.L Ω ℓ),
      gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (ambientPi K₂ L h₂ ℓ γ)) :
    (levelInfinityOf K₁ ℓ ⊔ K₂.L : IntermediateField ℚ Ω)
      = (K₁.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω) := by
  -- the middle field `N = K₁.L ⊔ K₂.L`, inside the auxiliary level `L`
  let N : NumFieldIn ℚ Ω := NumFieldIn.supOf K₁ K₂ L.L (sup_le h₁ h₂)
  have hN₁ : K₁.L ≤ N.L := NumFieldIn.le_supOf_left K₁ K₂ L.L _
  have hN₂ : K₂.L ≤ N.L := NumFieldIn.le_supOf_right K₁ K₂ L.L _
  have hNL : N.L ≤ L.L := NumFieldIn.supOf_le K₁ K₂ L.L _
  have hNsup : N.L ≤ (K₁.L ⊔ K₂.L : IntermediateField ℚ Ω) := le_of_eq (NumFieldIn.supOf_L K₁ K₂ L.L _)
  haveI : IsSepClosure ↥N.L Ω := isSepClosure_of_le N.L
  -- the pointwise criterion at the middle field
  have key : ∀ h : Ω ≃ₐ[↥N.L] Ω,
      gammaHausMk (K := ↥(K₁.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
            (galRestrict (E := K₁.L) (F := N.L) hN₁ h)) = 1
        ↔ gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
          (galToGamma (K := ↥(K₂.L)) (K' := Ω) ℓ
            (galRestrict (E := K₂.L) (F := N.L) hN₂ h)) = 1 := by
    intro h
    -- the Shimizu identity descends to `N`
    have hdes := hausMk_heq_of_le_general K₁ K₂ N L h₁ h₂ hN₁ hN₂ hNL ℓ σbar heq
      (galToGamma (K := ↥N.L) (K' := Ω) ℓ h)
    rw [generalBaseChange_galToGamma K₁ N hN₁ ℓ h,
      generalBaseChange_galToGamma K₂ N hN₂ ℓ h] at hdes
    constructor
    · intro hx
      have h1 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
          (σbar (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
            (galRestrict (E := K₁.L) (F := N.L) hN₁ h))) = 1 :=
        (gammaHausMk_sbar_eq_one_iff K₁ K₂ ℓ σbar hσbar _).mpr hx
      rw [hdes] at h1
      exact h1
    · intro hy
      have h1 : gammaHausMk (K := ↥(K₂.L)) (K' := Ω) (ℓ := ℓ)
          (σbar (galToGamma (K := ↥(K₁.L)) (K' := Ω) ℓ
            (galRestrict (E := K₁.L) (F := N.L) hN₁ h))) = 1 := by
        rw [hdes]; exact hy
      exact (gammaHausMk_sbar_eq_one_iff K₁ K₂ ℓ σbar hσbar _).mp h1
  exact lemma4f4_of_criterion K₁ K₂ L h₁ h₂ ℓ N.L hN₁ hN₂ hNL hNsup key

end NK.Reconstruct
