/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bijectivity of the Kummer pairing

For `K` a field containing a primitive `n`-th root of unity `ζ` and `L/K` a finite Galois
extension, the Kummer pairing

`kummerPairing hζ : (Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* (Gal(L/K) →* μ_n)`,  `a ↦ (σ ↦ σ α / α)`

is bijective.

Injectivity (that the kernel of the pairing is the subgroup of `n`-th powers in `K`) is
`Work.Kummer.kummerPairing_injective`.  The point of this file is surjectivity: every
homomorphism `χ : Gal(L/K) →* μ_n` is `σ ↦ σ β / β` for some `β` with `β ^ n ∈ K`.

The proof of surjectivity is the classical Lagrange resolvent: let `x₀ : L` be an element
whose Galois conjugates form a normal basis (`exists_linearIndependent_algEquiv_apply`), and put

`β = ∑_{σ ∈ Gal(L/K)} χ(σ)⁻¹ · σ(x₀)`.

Since `χ(σ) ≠ 0` and the `σ(x₀)` are `K`-linearly independent, `β ≠ 0`; a reindexing of the sum
gives `σ β = χ(σ) * β`, so `σ β / β = χ(σ)`; and then `σ (β ^ n) = χ(σ) ^ n * β ^ n = β ^ n` for
all `σ`, so `β ^ n` lies in the fixed field `K` of `Gal(L/K)`.  Thus `β ^ n = a` with `a ∈ Kˣ`, and
`a ∈ Kˣ ∩ (Lˣ)^n` realizes the character `χ`.

In fact — and this is why the hypotheses `Monoid.exponent Gal(L/K) ∣ n` and `IsKummerExtension n K L`
in the statement of `kummerPairing_bijective_of_isKummerExtension` are not used below — the
argument needs neither of them: the pairing `(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* (Gal(L/K) →* μ_n)` is
bijective for every finite Galois extension `L/K`.  This is the standard exactness of the Kummer
sequence `1 → μ_n → Lˣ → Lˣⁿ → 1` in Galois cohomology, together with Hilbert 90.
-/
import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_eq_one_iff
import Submission.Work.Kummer.kummerCharacter_eq_of_kummerRatio_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

open IntermediateField

section Resolvent

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n]

/-- **The Lagrange resolvent.**  Given a homomorphism `χ : Gal(L/K) →* μ_n` and a finite Galois
extension `L/K`, there is a unit `β` of `L` whose ratios `σ β / β` realize `χ` and whose `n`-th
power is in `K`:

`∀ σ, σ β / β = χ(σ)` in `Lˣ`, and `β ^ n = Units.map (algebraMap K L) a` for some `a : Kˣ`.

The construction is `β = ∑_σ χ(σ)⁻¹ · σ(x₀)`, where `x₀` is an element whose Galois conjugates
form a normal basis of `L/K`; the existence of `β` with the prescribed ratios is Noether's
generalization of Hilbert's Theorem 90. -/
theorem exists_unit_kummerRatio_eq_of_isGalois [FiniteDimensional K L] [IsGalois K L]
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ β : Lˣ, (∀ σ : Gal(L/K),
        kummerRatio σ β = Units.map (algebraMap K L) ((χ σ : rootsOfUnity n K) : Kˣ)) ∧
      ∃ a : Kˣ, β ^ n = Units.map (algebraMap K L) a := by
  -- `f σ` is the element `χ(σ) ∈ Kˣ ⊆ Lˣ`, viewed in `Lˣ`: it satisfies Noether's cocycle
  -- condition because `Gal(L/K)` acts trivially on the units coming from `K`.
  set f : Gal(L/K) → Lˣ :=
    fun σ => Units.map (algebraMap K L) ((χ σ : rootsOfUnity n K) : Kˣ) with hfdef
  have hcocycle : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have h1 : ((g • f h : Lˣ) : L) =
        algebraMap K L (((χ h : rootsOfUnity n K) : Kˣ) : K) := by
      rw [AlgEquiv.smul_units_def, hfdef]
      simp [Units.coe_map, AlgEquiv.commutes]
    apply Units.ext
    show ((f (g * h) : Lˣ) : L) = ((g • f h * f g : Lˣ) : L)
    rw [Units.val_mul, h1, hfdef]
    simp only [Units.coe_map, map_mul, Subgroup.coe_mul, Units.val_mul]
    exact mul_comm _ _
  -- Noether's generalization of Hilbert's Theorem 90 turns the cocycle into a coboundary.
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcocycle
  have hratio : ∀ σ : Gal(L/K), kummerRatio σ β = f σ := by
    intro σ
    rw [kummerRatio]
    exact hβ σ
  -- `β ^ n` is fixed by `Gal(L/K)`, hence lies in `K`.
  have hfix : ∀ σ : Gal(L/K), (σ : L ≃ₐ[K] L) ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    have h : (σ : L ≃ₐ[K] L) (β : L) =
        algebraMap K L (((χ σ : rootsOfUnity n K) : Kˣ) : K) * (β : L) := by
      have hh := congrArg (fun u : Lˣ => (u : L)) (hβ σ)
      rw [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, hfdef,
        div_eq_iff (Units.ne_zero β)] at hh
      exact hh
    have hpow1 : ((((χ σ : rootsOfUnity n K) : Kˣ)) : K) ^ n = 1 := by
      have h2 := (mem_rootsOfUnity n ((χ σ : rootsOfUnity n K) : Kˣ)).mp (χ σ).2
      simpa using congrArg (fun u : Kˣ => (u : K)) h2
    rw [map_pow, h, mul_pow, ← map_pow, hpow1, map_one, one_mul]
  obtain ⟨a₀, ha₀⟩ :=
    Set.mem_range.mp ((IsGalois.mem_range_algebraMap_iff_fixed ((β : L) ^ n)).mpr hfix)
  have ha₀' : a₀ ≠ 0 := by
    intro h0
    have hβn : (β : L) ^ n = 0 := by rw [← ha₀, h0, map_zero]
    exact pow_ne_zero n (Units.ne_zero β) hβn
  refine ⟨β, fun σ => hratio σ, Units.mk0 a₀ ha₀', ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
  exact ha₀.symm

end Resolvent

/-- **Surjectivity of the Kummer character.**  For a finite Galois extension `L/K` and a
primitive `n`-th root of unity `ζ ∈ K`, every homomorphism `Gal(L/K) →* μ_n` is the Kummer
character of some `a ∈ Kˣ ∩ (Lˣ)^n`. -/
theorem kummerCharacter_surjective_of_isGalois {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    [FiniteDimensional K L] [IsGalois K L] (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ a : kummerSubgroup n K L, kummerCharacter hζ a = χ := by
  obtain ⟨β, hratio, a, hpow⟩ := exists_unit_kummerRatio_eq_of_isGalois (K := K) (L := L) χ
  exact ⟨⟨a, ⟨β, hpow⟩⟩, kummerCharacter_eq_of_kummerRatio_eq hζ χ β a hpow hratio⟩

/-- **The Kummer pairing is bijective.**  For `K` a field containing a primitive `n`-th root of
unity `ζ` and `L/K` a finite Galois extension whose Galois group has exponent dividing `n` and
which is generated by `n`-th roots of elements of `K`, the Kummer pairing
`(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* (Gal(L/K) →* μ_n)` is bijective.

Injectivity is `Work.Kummer.kummerPairing_injective`; surjectivity follows from the Lagrange
resolvent `Work.Kummer.exists_unit_kummerRatio_eq_of_isGalois`.  (Neither `hexp` nor `hL` is
needed for this statement; they are recorded here as the hypotheses of the classical form.) -/
theorem kummerPairing_bijective_of_isKummerExtension {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (hL : IsKummerExtension n K L) :
    Function.Bijective (kummerPairing (K := K) (L := L) hζ) := by
  refine ⟨kummerPairing_injective (K := K) (L := L) hζ, fun χ => ?_⟩
  obtain ⟨a, ha⟩ := kummerCharacter_surjective_of_isGalois (K := K) (L := L) hζ χ
  exact ⟨QuotientGroup.mk' _ a, by rw [kummerPairing_mk, ha]⟩

end Work.Kummer
