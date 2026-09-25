import Mathlib
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.transferDescentAux

/-!
# Surjectivity of the restriction map on decomposition groups

For a tower of number fields `K ⊆ M ⊆ E` with `M/K`, `E/K` and `E/M` Galois, a place `w` of `M`
and a place `ŵ` of `E` lying over `w`, the restriction of decomposition groups

`stabRestrict : D_ŵ →* D_w`,   `D_ŵ = Stab_{Gal(E/K)}(ŵ)`,  `D_w = Stab_{Gal(M/K)}(w)`,

sending `σ` to the restriction `σ|_M`, is **surjective**.

The argument is the standard one:

* the restriction map `Gal(E/K) → Gal(M/K)` is surjective (`restrictHom_surjective`), so pick a
  lift `τ₀` of `σ`;
* `Gal(E/M)` acts transitively on the places of `E` above the fixed place `w` of `M`
  (`globalCFT_exists_smul_eq_of_liesOver` applied to the Galois extension `E/M`), so some
  `ρ ∈ Gal(E/M)` carries `τ₀ • ŵ` back to `ŵ`;
* the composite `inclMK ρ * τ₀` then fixes `ŵ` and still restricts to `σ` on `M`, because any
  element of `Gal(E/M)` acts trivially on `M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NK.GlobalCFT IsDedekindDomain

namespace NK.CFTLib.IdeleHasse.Descent

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]

/-- The inclusion `Gal(E/M) → Gal(E/K)` acts on the places of `E` exactly as the element of
`Gal(E/M)` it comes from: the two automorphisms have the same underlying map, hence the same action
on both the archimedean and the nonarchimedean places. -/
lemma inclMK_smul_place (ρ : E ≃ₐ[M] E) (ŵ : Place E) :
    (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ) • ŵ = ρ • ŵ := by
  have hfun : ⇑(NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ) = ⇑ρ :=
    NK.NUV2.ARL.HR.inclMK_apply ρ
  have hsymm : ∀ x : E,
      (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ).symm x = ρ.symm x := by
    intro x
    have h := congrFun hfun ((NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ).symm x)
    rw [AlgEquiv.apply_symm_apply] at h
    have h2 := congrArg ρ.symm h
    rw [AlgEquiv.symm_apply_apply] at h2
    exact h2.symm
  rcases ŵ with w | q
  · rw [Place.smul_ofInfinite, Place.smul_ofInfinite, Sum.inl.injEq]
    ext x
    rw [NumberField.InfinitePlace.smul_apply, NumberField.InfinitePlace.smul_apply, hsymm x]
  · rw [Place.smul_ofFinite, Place.smul_ofFinite, Place.ofFinite_inj]
    apply HeightOneSpectrum.ext
    rw [Place.smulHeightOneSpectrum_asIdeal, Place.smulHeightOneSpectrum_asIdeal]
    refine congrArg (fun f => Ideal.map f q.asIdeal) ?_
    ext x
    exact congrFun hfun x

theorem stabRestrict_surjective {K M E : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    Function.Surjective (NK.NUV2.ARL.HR.stabRestrict (K := K) (M := M) (E := E) w ŵ hw) := by
  haveI hfdME : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  intro σ
  -- Lift `σ` to an automorphism `τ₀` of `E` over `K`.
  obtain ⟨τ₀, hτ₀⟩ := NK.NUV2.ARL.HR.restrictHom_surjective (K := K) (M := M) (E := E) σ.1
  -- `τ₀ • ŵ` still lies over `w`.
  have hlies : Place.LiesOver (τ₀ • ŵ) w := by
    have h := NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := M) (L := E) τ₀
      (NK.NUV2.ARL.HR.restrictHom (K := K) (L := M) (E := E) τ₀)
      (fun y => NK.NUV2.ARL.HR.restrictHom_apply_coe τ₀ y) hw
    rw [hτ₀, MulAction.mem_stabilizer_iff.mp σ.2] at h
    exact h
  -- Transitivity of `Gal(E/M)` on the places of `E` above `w` moves `τ₀ • ŵ` back to `ŵ`.
  obtain ⟨ρ, hρ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (v := w) hlies hw
  refine ⟨⟨NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ * τ₀, ?_⟩, ?_⟩
  · -- `inclMK ρ * τ₀` fixes `ŵ`.
    rw [MulAction.mem_stabilizer_iff]
    rw [mul_smul, inclMK_smul_place]
    exact hρ
  · -- and restricts to `σ` on `M`, since `inclMK ρ` acts trivially on `M`.
    apply Subtype.ext
    show NK.NUV2.ARL.HR.restrictHom (K := K) (L := M) (E := E)
      (NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ * τ₀) = σ.1
    have hker : NK.NUV2.ARL.HR.inclMK (K := K) (M := M) (E := E) ρ
        ∈ (NK.NUV2.ARL.HR.restrictHom (K := K) (L := M) (E := E)).ker := by
      rw [NK.NUV2.ARL.HR.mem_ker_restrictHom_iff]
      intro m
      rw [NK.NUV2.ARL.HR.inclMK_apply]
      exact ρ.commutes m
    rw [map_mul, hτ₀, MonoidHom.mem_ker.mp hker, one_mul]

end NK.CFTLib.IdeleHasse.Descent
