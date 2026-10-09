import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_apply_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

open IntermediateField

/-- **Surjectivity of the Kummer character.**  Let `L/K` be a finite Galois extension and let
`ζ ∈ K` be a primitive `n`-th root of unity.  Then every homomorphism `Gal(L/K) →* μ_n(K)` is the
Kummer character of some `a ∈ Kˣ ∩ (Lˣ)^n`.

The proof is the classical Lagrange resolvent argument, in the form of Noether's generalization of
Hilbert's theorem 90: the character `χ` is a `1`-cocycle of `Gal(L/K)` with values in the units of
`K` (viewed in `Lˣ`), hence a coboundary, so there is `β ∈ Lˣ` with `σ β / β = χ(σ)` for all `σ`.
Then `β ^ n` is fixed by `Gal(L/K)`, hence lies in `Kˣ`, and it is a `K`-rational `n`-th power in
`L`, so it lies in the Kummer subgroup `Kˣ ∩ (Lˣ)^n` and its Kummer character is `χ`. -/
theorem kummerCharacterHom_surjective {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    [FiniteDimensional K L] [IsGalois K L] (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ a : kummerSubgroup n K L, kummerCharacter hζ a = χ := by
  classical
  -- The character `χ`, viewed as a homomorphism into the units of `K`.
  let w : Gal(L/K) →* Kˣ := (rootsOfUnity n K).subtype.comp χ
  -- Its image in the units of `L`.
  let f : Gal(L/K) → Lˣ := fun σ => Units.map (algebraMap K L) (w σ)
  have hwval : ∀ σ : Gal(L/K), w σ = (((χ σ : rootsOfUnity n K)) : Kˣ) := by
    intro σ
    rfl
  -- `f` is a `1`-cocycle, because `Gal(L/K)` acts trivially on the units coming from `K`.
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    have hfix : σ • f τ = f τ := algEquivUnitsMap_unitsMap σ (w τ)
    rw [hfix]
    apply Units.ext
    simp only [f, Units.coe_map, Units.val_mul, map_mul]
    exact mul_comm _ _
  -- Noether's form of Hilbert's theorem 90: `f` is a coboundary.
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have hmul : ∀ σ : Gal(L/K), algEquivUnitsMap (σ : L ≃ₐ[K] L) β = f σ * β :=
    fun σ => div_eq_iff_eq_mul.mp (hβ σ)
  -- Hence `σ (β : L) = f σ * β` in `L`.
  have hβcoe : ∀ σ : Gal(L/K), (σ : L ≃ₐ[K] L) (β : L) = ((f σ : Lˣ) : L) * (β : L) := by
    intro σ
    have h := congrArg (fun x : Lˣ => (x : L)) (hmul σ)
    simpa using h
  -- The values of `f` have `n`-th power `1`, since they come from `n`-th roots of unity.
  have hfpow : ∀ σ : Gal(L/K), (((f σ : Lˣ) : L)) ^ n = 1 := by
    intro σ
    have h4 : (((w σ : Kˣ) : K)) ^ n = 1 := by
      have h := (mem_rootsOfUnity n (((χ σ : rootsOfUnity n K)) : Kˣ)).mp (χ σ).2
      have h2 : ((((χ σ : rootsOfUnity n K)) : Kˣ) : K) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
      simpa [hwval σ] using h2
    have h5 : (((f σ : Lˣ) : L)) = algebraMap K L (((w σ : Kˣ) : K)) := rfl
    rw [h5, ← map_pow, h4, map_one]
  -- Therefore `β ^ n` is fixed by `Gal(L/K)`.
  have hpow : ∀ σ : Gal(L/K), (σ : L ≃ₐ[K] L) ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    rw [map_pow, hβcoe σ, mul_pow, hfpow σ, one_mul]
  obtain ⟨a, ha⟩ := Set.mem_range.mp
    ((IsGalois.mem_range_algebraMap_iff_fixed ((β : L) ^ n)).mpr hpow)
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 : ((β : L)) ^ n = 0 := by rw [← ha, h0, map_zero]
    exact pow_ne_zero n (Units.ne_zero β) h1
  -- `β` is an `n`-th root of the element `a ∈ Kˣ`.
  have hα : ((β : L)) ^ n = algebraMap K L ((Units.mk0 a ha0 : Kˣ) : K) := by
    rw [Units.val_mk0]
    exact ha.symm
  have hmem : Units.mk0 a ha0 ∈ kummerSubgroup n K L := by
    refine ⟨β, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
    exact ha.symm
  refine ⟨⟨Units.mk0 a ha0, hmem⟩, ?_⟩
  refine MonoidHom.ext fun σ => Subtype.ext ?_
  apply Units.map_injective (algebraMap K L).injective
  -- The Kummer ratio of `β` is `χ(σ)`.
  have hratio : kummerRatio σ β = f σ := by
    rw [kummerRatio, hmul σ]
    exact div_eq_iff_eq_mul.mpr rfl
  exact (kummerCharacter_apply_of_pow_eq hζ hmem hα σ).trans (hratio.trans (by rfl))

end Work.Kummer
