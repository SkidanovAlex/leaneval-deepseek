import Mathlib
import Submission.Work.SSGRoute.decompK_restrict_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **A Galois subextension whose Galois group contains all archimedean decomposition groups is
unramified at infinity.**  Let `L/K` be a finite Galois extension of number fields and let
`E` be an intermediate field with `E/K` Galois.  If the stabilizer in `Gal(L/K)` of every
archimedean place `u` of `L` is contained in `Gal(L/E) = E.fixingSubgroup`, then every
archimedean place of `E` is unramified over `K`, i.e. `IsUnramifiedAtInfinitePlaces K ↥E`.

Route: by `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot` (with `k := K`, `K := ↥E`)
it suffices to show that the stabilizer of any archimedean place `w` of `↥E` in `↥E ≃ₐ[K] ↥E` is
trivial.  If `σ ≠ 1` were in it, choose a place `u` of `L` above `w` and lift `σ` to
`τ ∈ Stab_{Gal(L/K)}(u)` — surjectivity of the restriction map on decomposition groups
(`decompK_restrict_surjective`, valid at archimedean places too, via
`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`).  Then `τ|_E = σ ≠ 1` gives
`τ ∉ E.fixingSubgroup`, contradicting the hypothesis. -/
theorem e9_caseB_unramified_arch
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (h : ∀ u : NumberField.InfinitePlace L,
        MulAction.stabilizer (L ≃ₐ[K] L) u ≤ E.fixingSubgroup) :
    IsUnramifiedAtInfinitePlaces K ↥E := by
  refine ⟨fun w => ?_⟩
  rw [NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot]
  rw [eq_bot_iff]
  intro σ hσ
  simp only [Subgroup.mem_bot]
  -- Choose an archimedean place `u` of `L` above `w`.
  obtain ⟨u, hu'⟩ := NumberField.InfinitePlace.comap_surjective (k := ↥E) (K := L) w
  have hu : u.comap (algebraMap ↥E L) = w := hu'
  -- Lift `σ` to `τ₀ ∈ Gal(L/K)`.
  obtain ⟨τ₀, hτ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) L σ
  have hσw : σ • w = w := MulAction.mem_stabilizer_iff.mp hσ
  have hτ₀E : ∀ x : ↥E, τ₀ ((x : L)) = ((σ x : ↥E) : L) := by
    intro x
    have h1 := AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := L) (L := E) τ₀ x
    rw [hτ₀] at h1
    exact h1.symm
  -- `τ₀ • u` still lies over `w`.
  have hcomap : (τ₀ • u).comap (algebraMap ↥E L) = w := by
    have hsymm : ∀ x : ↥E, τ₀.symm ((x : L)) = ((σ.symm x : ↥E) : L) := by
      intro x
      have h2 := hτ₀E (σ.symm x)
      rw [AlgEquiv.apply_symm_apply] at h2
      rw [← h2, AlgEquiv.symm_apply_apply]
    rw [NumberField.InfinitePlace.comap_smul]
    have hf : (τ₀.symm : L →+* L).comp (algebraMap ↥E L)
        = (algebraMap ↥E L).comp (σ.symm : ↥E →+* ↥E) := by
      ext x
      exact hsymm x
    rw [hf]
    rw [NumberField.InfinitePlace.comap_comp]
    rw [hu]
    rw [← NumberField.InfinitePlace.smul_eq_comap]
    exact hσw
  -- Transitivity of `Gal(L/↥E)` on the places over `w`: some `ρ` moves `τ₀ • u` to `u`.
  obtain ⟨ρ, hρ⟩ :=
    NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := ↥E) (K := L) (hcomap.trans hu.symm)
  -- `τ' = ρ τ₀` is a lift of `σ` lying in the decomposition group of `u`.
  let τ' : L ≃ₐ[K] L := (AlgEquiv.restrictScalars K ρ) * τ₀
  have hτ'u : τ' • u = u := by
    change ((AlgEquiv.restrictScalars K ρ) * τ₀) • u = u
    rw [mul_smul]
    have hr : (AlgEquiv.restrictScalars K ρ) • (τ₀ • u) = ρ • (τ₀ • u) := rfl
    rw [hr, hρ]
  have hfix : τ' ∈ E.fixingSubgroup := h u (MulAction.mem_stabilizer_iff.mpr hτ'u)
  -- `τ' ∈ E.fixingSubgroup` forces its restriction to `E` to be trivial ...
  have hnormalize : ∀ x : ↥E, (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) τ' x = x := by
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := L) (L := E)]
    exact (IntermediateField.mem_fixingSubgroup_iff E τ').mp hfix ((x : L)) x.2
  have h1 : (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) τ' = 1 := by
    apply AlgEquiv.ext
    exact hnormalize
  -- ... while `ρ` restricts trivially since it is `↥E`-linear.
  have hρ1 : (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) (AlgEquiv.restrictScalars K ρ) = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := L) (L := E)]
    exact ρ.commutes x
  have hprod : (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) τ'
      = (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) (AlgEquiv.restrictScalars K ρ)
        * (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) τ₀ := by
    change (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) ((AlgEquiv.restrictScalars K ρ) * τ₀) = _
    rw [map_mul]
  have h4 : (AlgEquiv.restrictNormalHom (K₁ := L) ↥E) τ' = σ := by
    rw [hprod, hρ1, one_mul, hτ₀]
  exact h4.symm.trans h1

end Work.SSGRoute
