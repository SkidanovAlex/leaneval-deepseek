import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **Lifting an element of a decomposition group along a Galois subextension.**

Let `k ⊆ E ⊆ L` be an extension of number fields with `L/k` and `E/k` finite Galois; let `v` be a
place of `L` and `w` a place of `E` below it (`hv : v.LiesOver w`).  Then every `σ : E ≃ₐ[k] E` which
fixes `w` (`σ ∈ MulAction.stabilizer Gal(E/k) w`) lifts to `τ : L ≃ₐ[k] L` which fixes `v` and whose
restriction to `E` is `σ`:
`∃ τ, τ ∈ MulAction.stabilizer Gal(L/k) v ∧ AlgEquiv.restrictNormalHom E τ = σ`.

Proof: lift `σ` to any `τ₀` with `AlgEquiv.restrictNormalHom E τ₀ = σ`
(`AlgEquiv.restrictNormalHom_surjective`, since `E/k` is normal).  Because `τ₀` fixes `w`, its action
on the places of `L` preserves the fibre of `w`, i.e. `τ₀ • v` still lies over `w` (this is
`NK.HassePrinciple.liesOver_smul_of_restrict`).  The group `Gal(L/E)` acts transitively on the places
of `L` lying over `w`: the extension `L/E` is Galois (`IsGalois.tower_top_of_isGalois`) and the
transitivity is the on-disk `NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`
(`∀ {w w' : Place L} {v : Place E}, w.LiesOver v → w'.LiesOver v → ∃ σ, σ • w = w'`).  So there is
`ρ : L ≃ₐ[E] L` with `ρ • (τ₀ • v) = v`, and `τ := ρ * τ₀` (viewed in `Gal(L/k)`, using
`IsScalarTower k E L`) works.

Note: `Submission/Work/SSGRoute/decompK_restrict_surjective.lean` already proves the surjectivity of
the restriction map on decomposition groups (`Function.Surjective` form) — derive the `∃`-form from
that rather than reproving it. -/
theorem exists_mem_stabilizer_restrictNormalHom_eq {k E L : Type} [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] [Field L] [NumberField L] [Algebra k L]
    [Algebra E L] [IsScalarTower k E L] [FiniteDimensional k L] [IsGalois k L] [IsGalois k E]
    (v : NK.GlobalCFT.Place L) (w : NK.GlobalCFT.Place E) (hv : NK.GlobalCFT.Place.LiesOver v w)
    (σ : E ≃ₐ[k] E) (hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) w) :
    ∃ τ : L ≃ₐ[k] L, τ ∈ MulAction.stabilizer (L ≃ₐ[k] L) v ∧
      AlgEquiv.restrictNormalHom E τ = σ := by
  -- Step 1: lift `σ` to any `τ₀ : Gal(L/k)` restricting to `σ`.
  obtain ⟨τ₀, hτ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) L σ
  have hσw : σ • w = w := MulAction.mem_stabilizer_iff.mp hσ
  -- Step 2: `τ₀ • v` still lies over `w`, because `τ₀` restricts to `σ` and `σ` fixes `w`.
  have hlies0 : NK.GlobalCFT.Place.LiesOver (τ₀ • v)
      (AlgEquiv.restrictNormalHom E τ₀ • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := E) (L := L) τ₀
      (AlgEquiv.restrictNormalHom E τ₀)
      (fun y => AlgEquiv.restrictNormal_commutes τ₀ E y) hv
  have hlies : NK.GlobalCFT.Place.LiesOver (τ₀ • v) w := by
    rw [hτ₀, hσw] at hlies0
    exact hlies0
  -- Step 3: `Gal(L/E)` acts transitively on the places of `L` over `w`.
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois k E L
  haveI : FiniteDimensional E L := FiniteDimensional.right k E L
  obtain ⟨ρ, hρ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := E) (L := L) hlies hv
  -- Step 4: `τ := ρ * τ₀` (with `ρ` viewed in `Gal(L/k)`).
  refine ⟨AlgEquiv.restrictScalars k ρ * τ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    have hsmul : ∀ x : NK.GlobalCFT.Place L,
        (AlgEquiv.restrictScalars k ρ) • x = ρ • x := fun x => rfl
    rw [hsmul (τ₀ • v), hρ]
  · have hres : AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalars k ρ) = 1 := by
      ext x
      simp only [AlgEquiv.one_apply]
      apply (algebraMap E L).injective
      have hχ : AlgEquiv.restrictNormalHom E (AlgEquiv.restrictScalars k ρ)
          = (AlgEquiv.restrictScalars k ρ).restrictNormal E := rfl
      rw [hχ, AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
      exact ρ.commutes x
    rw [map_mul, hres, one_mul]
    exact hτ₀

end Work.SSGRoute.Sha2Lib
