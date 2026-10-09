import Mathlib
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Work.SSGRoute.exists_character_lift_of_fixingSubgroup_le_ker
import Submission.Work.SSGRoute.exists_unit_div_eq_of_character
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Realization of Kummer characters of the absolute Galois group

`Work.SSGRoute.kummer_character_realization_inf`: let `L` be a separable closure of a field `U` and
let `ω : Gal(L/U) →* μ_n(U)` be a character of the absolute Galois group with *open* kernel.  Then
there is `γ ∈ L` with `γ ^ n ∈ U` and `σ γ / γ = ω σ` for every `σ ∈ Gal(L/U)`.

The three inputs are proved in the sibling files of this directory:

* `exists_finiteDimensional_normal_fixingSubgroup_le` — openness of `ker ω` produces a
  finite-dimensional normal intermediate field `M` with `Gal(L/M) ≤ ker ω`;
* `exists_character_lift_of_fixingSubgroup_le_ker` — `ω` then descends to a character `φ` of
  `Gal(M/U)`, with `φ (σ|_M) = ω σ`;
* `exists_unit_div_eq_of_character` — Noether's form of Hilbert's theorem 90 in the finite
  extension `M/U` realizes `φ` by a unit `β` of `M` (the Kummer resolvent `σ ↦ σ β / β`).

The element `γ` is the image of `β` in `L`.  Since every `σ` acts on `M` through `σ|_M`, the ratio
`σ γ / γ = (σ|_M) β / β = ω σ` is the prescribed root of unity, and `γ ^ n` is fixed by all of
`Gal(L/U)` — because `(ω σ) ^ n = 1` — hence lies in `U`.
-/

namespace Work.SSGRoute

open scoped Classical

noncomputable section

theorem kummer_character_realization_inf
    {U L : Type*} [Field U] [Field L] [Algebra U L] [IsSepClosure U L]
    {n : ℕ} (hn : n ≠ 0)
    (ω : (L ≃ₐ[U] L) →* ↥(rootsOfUnity n U))
    (hω : IsOpen (ω.ker : Set (L ≃ₐ[U] L))) :
    ∃ γ : L, γ ^ n ∈ Set.range (algebraMap U L) ∧
      ∀ σ : (L ≃ₐ[U] L),
        σ γ / γ = algebraMap U L (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U) := by
  classical
  haveI hGal : IsGalois U L := inferInstance
  -- A finite normal subextension cut out by an open subgroup inside `ker ω`.
  obtain ⟨M, hMfin, hMnorm, hMle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := U) (L := L) ω.ker hω
  haveI hMfd : FiniteDimensional U ↥M := hMfin
  haveI hMnm : Normal U ↥M := hMnorm
  -- The descended character `φ` of `Gal(M/U)`, with `φ (σ|_M) = ω σ`.
  obtain ⟨φ, hφ⟩ := exists_character_lift_of_fixingSubgroup_le_ker (U := U) (L := L) M ω hMle
  let d : (↥M ≃ₐ[U] ↥M) →* Uˣ := (rootsOfUnity n U).subtype.comp φ
  -- Hilbert 90 in the finite extension `M/U`.
  obtain ⟨β, hβ⟩ := exists_unit_div_eq_of_character (U := U) (M := ↥M) d
  have hγ0 : algebraMap ↥M L (β : ↥M) ≠ 0 :=
    (algebraMap ↥M L).injective.ne (Units.ne_zero β)
  -- The Kummer ratio of `γ` is the prescribed character.
  have hdiv : ∀ σ : L ≃ₐ[U] L,
      σ (algebraMap ↥M L (β : ↥M)) / (algebraMap ↥M L (β : ↥M))
        = algebraMap U L (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U) := by
    intro σ
    set χ : ↥M ≃ₐ[U] ↥M := AlgEquiv.restrictNormalHom (F := U) (K₁ := L) ↥M σ with hχdef
    have hφχ : φ χ = ω σ := hφ σ
    have hdχ : (d χ : Uˣ) = ((ω σ : ↥(rootsOfUnity n U)) : Uˣ) := by
      simp only [d, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact congrArg (fun z : ↥(rootsOfUnity n U) => (z : Uˣ)) hφχ
    have hχβ : χ (β : ↥M)
        = algebraMap U ↥M (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U) * (β : ↥M) := by
      have h := hβ χ
      rw [div_eq_iff (Units.ne_zero β)] at h
      rw [h, hdχ]
    have hσγ : σ (algebraMap ↥M L (β : ↥M)) = algebraMap ↥M L (χ (β : ↥M)) := by
      rw [hχdef]
      exact (AlgEquiv.restrictNormalHom_apply (K₁ := L) M σ (β : ↥M)).symm
    rw [hσγ, hχβ, map_mul, ← IsScalarTower.algebraMap_apply U ↥M L]
    rw [mul_div_cancel_right₀ _ hγ0]
  refine ⟨algebraMap ↥M L (β : ↥M), ?_, hdiv⟩
  -- `γ ^ n` is fixed by all of `Gal(L/U)`, hence lies in `U`.
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  rw [map_pow]
  have hpow : (algebraMap U L (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U)) ^ n = 1 := by
    rw [← map_pow, (mem_rootsOfUnity' n ((ω σ : ↥(rootsOfUnity n U)) : Uˣ)).mp (ω σ).2,
      map_one]
  have hσγ : σ (algebraMap ↥M L (β : ↥M))
      = algebraMap U L (((ω σ : ↥(rootsOfUnity n U)) : Uˣ) : U)
          * algebraMap ↥M L (β : ↥M) := by
    have h := hdiv σ
    rw [div_eq_iff hγ0] at h
    exact h
  rw [hσγ, mul_pow, hpow, one_mul]

end

end Work.SSGRoute
