/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Frobenius normalisation on the Kummer layers (Tate twist)

`NK.TameStructureDeep.Tame.kummer_tateTwist`: on each Kummer layer `κ^{ur}(β)`, `β ^ ℓ = a`
with `a ∈ κ` and `ℓ` prime to the residue characteristic, the lifted Frobenius `F` acts on the
Kummer group `Gal(κ^{ur}(β)/κ^{ur}) ≅ μ_ℓ` by the `q`-th power map: for every `σ` fixing
`κ^{ur}` one has

  `(F σ F⁻¹) β / β = (σ β / β) ^ q`,

which is the Tate twist `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)` of NSW (12.1.8).

The proof is the classical one.  Write `γ = σ β / β ∈ μ_ℓ` for the Kummer character of `σ`
and `δ = F⁻¹β / β ∈ μ_ℓ`.  Since `δ` is a root of unity of order dividing `ℓ` it lies in
`κ^{ur} = κ(μ_{p'})`, hence is fixed by `σ`; and `σ` acts on the Kummer character independently
of the chosen `ℓ`-th root of `a`, so that `σ(F⁻¹β)/(F⁻¹β) = γ`.  Therefore

  `(F σ F⁻¹) β = F (σ F⁻¹β) = F (γ · F⁻¹β) = F γ · β`,

and `F γ = γ ^ q` because `F` acts on the prime-to-`p` roots of unity by the `q`-th power map.
-/
import Mathlib
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.LocalAnabelian.ResidueField.Recovery
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot

namespace NK.TameStructureDeep.Tame

theorem kummer_tateTwist {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] {p q ℓ : ℕ} (hℓ : ℓ.Prime) (hpℓ : ¬ p ∣ ℓ)
    {a : κ} (ha : a ≠ 0) {β : K'} (hβ : β ^ ℓ = algebraMap κ K' a)
    {F : Gal(K'/κ)} (hF : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q F)
    (σ : Gal(K'/κ))
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup) :
    (F * σ * F⁻¹) β / β = (σ β / β) ^ q := by
  -- `a` is nonzero, hence so is `β`
  have ha' : algebraMap κ K' a ≠ 0 :=
    fun h => ha (FaithfulSMul.algebraMap_injective κ K' (by simpa using h))
  have hβne : β ≠ 0 := by
    intro h
    rw [h, zero_pow hℓ.ne_zero] at hβ
    exact ha' hβ.symm
  -- `σ` fixes `κ^{ur}` pointwise
  have hσfix := hσ
  simp only [IntermediateField.mem_fixingSubgroup_iff] at hσfix
  -- the Kummer character of `σ` at `β`
  set γ : K' := σ β / β with hγdef
  have hγpow : γ ^ ℓ = 1 := by
    rw [hγdef, div_pow, ← map_pow σ β ℓ, hβ, AlgEquiv.commutes, div_self ha']
  -- the Frobenius maps `γ` to its `q`-th power
  have hγF : F γ = γ ^ q := by
    rcases eq_or_ne γ 1 with h1 | hne
    · rw [h1, map_one, one_pow]
    · exact hF.2 ℓ hpℓ γ (isPrimitiveRoot_of_mem_nthRootsFinset hℓ
        ((Polynomial.mem_nthRootsFinset hℓ.pos 1).mpr hγpow) hne)
  -- `δ = F⁻¹β / β` is a root of unity of order dividing `ℓ`, hence lies in `κ^{ur}`
  set δ : K' := F.symm β / β with hδdef
  have hβ₁pow : (F.symm β) ^ ℓ = algebraMap κ K' a := by
    rw [← map_pow, hβ, AlgEquiv.commutes]
  have hδpow : δ ^ ℓ = 1 := by
    rw [hδdef, div_pow, hβ₁pow, hβ, div_self ha']
  have hσδ : σ δ = δ := by
    rcases eq_or_ne δ 1 with h1 | hne
    · rw [h1, map_one]
    · have hδmem : δ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p :=
        mem_unramifiedClosure_of_isPrimitiveRoot hpℓ
          (isPrimitiveRoot_of_mem_nthRootsFinset hℓ
            ((Polynomial.mem_nthRootsFinset hℓ.pos 1).mpr hδpow) hne)
      exact hσfix δ hδmem
  -- the Kummer character is independent of the chosen `ℓ`-th root of `a`
  have hσβ : σ β = γ * β := by
    rw [hγdef]
    exact (div_mul_cancel₀ (σ β) hβne).symm
  have hσβ₁ : σ (F.symm β) = γ * (F.symm β) := by
    have hβ₁eq : F.symm β = δ * β := by
      rw [hδdef]
      exact (div_mul_cancel₀ (F.symm β) hβne).symm
    rw [hβ₁eq, map_mul, hσδ, hσβ]
    ring
  -- the main computation
  have hmain : (F * σ * F⁻¹) β = γ ^ q * β := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    show F (σ (F.symm β)) = γ ^ q * β
    rw [hσβ₁, map_mul, hγF, AlgEquiv.apply_symm_apply]
  rw [div_eq_iff hβne]
  exact hmain

end NK.TameStructureDeep.Tame
