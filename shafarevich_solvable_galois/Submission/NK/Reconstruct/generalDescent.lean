import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.Padics.PadicIntegers
import Submission.NK.Reconstruct.NumFieldInSup
import Submission.NK.Reconstruct.generalBaseChange_galToGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's descent `σ̄ ∘ π_{L/K₁} = π_{L/K₂} ⟹ σ̄ ∘ π_{N/K₁} = π_{N/K₂}`

This is step 2 of the proof of Shimizu's Lemma 4f.4 (arXiv:2009.10431) in the form needed by the
reconstruction step: `NK.Reconstruct.ambientPi_hausMk_heq_of_le` does it for finite Galois levels
`K ⊆ N ⊆ L` of `Ω/ℚ`; here the middle level `N` is an *arbitrary* finite number field inside `Ω`
(the compositum `K₁.L ⊔ K₂.L` in the application), so that the base changes `π_{N/K_i}` are
`NK.Reconstruct.generalBaseChange`.

The argument is unchanged from `ambientPi_hausMk_heq_of_le`: the cokernel of `π_{L/N}` is finite, so
every `γ ∈ Γ_N` has a power `γ ^ m` in the image of `π_{L/N}`; the identity at the corresponding
`γ' ∈ Γ_L` gives the `m`-th powers of the two sides equal in the torsion-free group `Γ_{K₂}^{tf}`,
whence the sides themselves are equal.  Only the two functoriality statements of the general base
change (`generalBaseChange_galToGamma`, `generalBaseChange_comp_ambientPi`) enter.

## Contents

* **`NK.Reconstruct.hausMk_heq_of_le_general`** — the descent.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Lemma 4f.4.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The identity `σ̄ ∘ π_{L/K₁} = π_{L/K₂}` descends to an arbitrary subfield `N ⊆ L`**, after
passing to the Hausdorff torsion-free quotients `Γ^{tf}`. -/
theorem hausMk_heq_of_le_general (K₁ K₂ N : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥N.L Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (hN₁ : K₁.L ≤ N.L) (hN₂ : K₂.L ≤ N.L) (hNL : N.L ≤ L.L)
    (ℓ : ℕ) [Fact ℓ.Prime] (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ)
    (heq : ∀ (γ : Gamma ↥L.L Ω ℓ),
      gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (ambientPi K₂ L h₂ ℓ γ))
    (γ : Gamma ↥N.L Ω ℓ) :
    gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (σbar (generalBaseChange K₁ N hN₁ ℓ γ))
      = gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ) (generalBaseChange K₂ N hN₂ ℓ γ) := by
  -- The exponent killing the finite cokernel of `π_{L/N}`.
  let m : ℕ := Nat.card (LevelEllPart (K := ↥N.L) (K' := Ω) (levelExtendGen N L hNL).L ℓ)
  have hm : m ≠ 0 := (Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩).ne'
  -- `γ ^ m` lies in the range of `π_{L/N}`.
  have hmem : γ ^ m ∈ (ambientPi N L hNL ℓ).range := by
    have hker : γ ^ m ∈
        (Gamma.proj (K := ↥N.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen N L hNL)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      simpa [m] using
        pow_card_eq_one' (x := Gamma.proj (K := ↥N.L) (K' := Ω) (ℓ := ℓ) (levelExtendGen N L hNL) γ)
    rwa [ker_proj_eq_range_gammaBaseChangeHom ℓ (levelExtendGen N L hNL)] at hker
  obtain ⟨γ', hγ'⟩ := hmem
  -- Transitivity of the base change.
  have hcomp₁ := generalBaseChange_comp_ambientPi K₁ N L hN₁ hNL ℓ
  have hcomp₂ := generalBaseChange_comp_ambientPi K₂ N L hN₂ hNL ℓ
  have key₁ : (generalBaseChange K₁ N hN₁ ℓ γ) ^ m = ambientPi K₁ L h₁ ℓ γ' := by
    rw [← map_pow, ← hγ']
    exact DFunLike.congr_fun hcomp₁ γ'
  have key₂ : (generalBaseChange K₂ N hN₂ ℓ γ) ^ m = ambientPi K₂ L h₂ ℓ γ' := by
    rw [← map_pow, ← hγ']
    exact DFunLike.congr_fun hcomp₂ γ'
  -- The `m`-th powers of the two sides agree in `Γ_{K₂}^{tf}`.
  have hpow : (gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
      (σbar (generalBaseChange K₁ N hN₁ ℓ γ))) ^ m
      = (gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
        (generalBaseChange K₂ N hN₂ ℓ γ)) ^ m := by
    rw [← map_pow, ← map_pow (f := σbar), key₁, heq γ', ← key₂, map_pow]
  -- `Γ_{K₂}^{tf}` is torsion-free, so the discrepancy itself is trivial.
  have hratio : gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
      (σbar (generalBaseChange K₁ N hN₁ ℓ γ))
      * (gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
        (generalBaseChange K₂ N hN₂ ℓ γ))⁻¹ = 1 := by
    refine gammaHaus_pow_eq_one (y := gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
      (σbar (generalBaseChange K₁ N hN₁ ℓ γ))
      * (gammaHausMk (K := ↥K₂.L) (K' := Ω) (ℓ := ℓ)
        (generalBaseChange K₂ N hN₂ ℓ γ))⁻¹) hm ?_
    rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  exact mul_inv_eq_one.mp hratio

end NK.Reconstruct
