import Mathlib
import Submission.NK.NUV2.Wall

/-!
# The idèle/Γ bridge in `finrank` form, from ℓ-adic Artin reciprocity

The requested statement is

```
hausQuot_finrank_eq_dual_idele_of_artin (Ω) [..] (hb : ArtinDualBridge Ω 2) (K) [..] :
    finrank (ℤ_2) (HausQuot K Ω 2) = finrank (ℤ_2) (Dual (C_K) 2)
```

i.e. Shimizu's `r_2(K) = rank_{ℤ_2} Hom_cts(C_K, ℤ_2)` in `finrank` form, where
`HausQuot K Ω ℓ = Γ_K^{Ω} ⧸ invisible` is the Hausdorff (dual-faithful) quotient of Shimizu's
`ℓ`-adic abelianisation and `C_K = 𝕀_K ⧸ Kˣ` is the idèle class group.

## What is proved here

The **only** classical input is the hypothesis `hb : ArtinDualBridge Ω 2`, i.e. the equality of the
`ℤ_2`-*ranks* of the continuous duals

`rank (Dual (Γ_K^{Ω}) 2) = rank (Dual (C_K) 2)`.

The whole content of the lemma is then the *elementary* identification of the `finrank` of the
Hausdorff quotient with the `finrank` of the dual of `Γ_K`:

`finrank (HausQuot K Ω ℓ) = finrank (Dual (Γ_K^{Ω}) ℓ)`   (`finrank_hausQuot_eq_finrank_dualGamma`).

**This is not the missing `rank (Dual Γ_K) ≤ rank (HausQuot)` inequality.**  The point is that
`Module.finrank = Cardinal.toNat ∘ Module.rank` kills infinite ranks, so only the following two
*elementary* implications are needed:

* `rank (Dual Γ_K) < ℵ₀ ⟹ rank (HausQuot) ≤ rank (Dual Γ_K)` — the evaluation
  `HausQuot ↪ Module.Dual (ℤ_ℓ) (Dual Γ_K)` is injective by *definition* of `invisibleSubmodule`
  (`NK.RankTheoryDeep.rank_hausQuot_le_rank_dual`, on disk);
* `rank (HausQuot) < ℵ₀ ⟹ rank (Dual Γ_K) ≤ rank (HausQuot)` — here we use the *descent map*
  `Dual (Γ_K) →ₗ[ℤ_ℓ] Module.Dual (ℤ_ℓ) (HausQuot)` of this file: a continuous character of `Γ_K`
  vanishes on the invisible subgroup, hence factors through `HausQuot`, and the resulting map is
  injective and `ℤ_ℓ`-linear; combined with
  `NK.RankTheoryDeep.rank_dual_le_rank_of_rank_lt_aleph0` it bounds `rank (Dual Γ_K)` by
  `rank (HausQuot)` whenever the latter is finite.

Consequently, if either rank is finite then the two ranks are *equal*; and if either is infinite
then both `finrank`s are `0`.  Hence the two `finrank`s always agree, and `hb` (an equality of
ranks, hence of `toNat`s) finishes.

In particular this file needs **no** extra classical input beyond `ArtinDualBridge`; it is the
`finrank`-level "descent" of the bridge, and the unconditional `HausQuotBridge_two` of
`NUV2/RouteD` is recovered by composing it with `NUV2/artinDualBridge_two`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, (10.3.20);
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2

open NK.Reconstruct

/-! ## The descent `Dual (Γ_K) →ₗ Module.Dual (ℤ_ℓ) (HausQuot)` -/

/-- **The descent of a continuous character of `Γ_K` to the Hausdorff quotient.**

A continuous additive character `χ : Γ_K → ℤ_ℓ` vanishes on `invisibleSubmodule` (by definition of
the latter as the intersection of the kernels of all such characters,
`NK.Reconstruct.mem_invisibleSubmodule_iff`), hence factors through the quotient
`HausQuot K K' ℓ = Γ_K ⧸ invisibleSubmodule`; the factored map is `Submodule.liftQ (dualToLinear χ)`
and is `ℤ_ℓ`-linear because `χ` is (`NK.Reconstruct.dualToLinear`). -/
noncomputable def dualDescentFun (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ) :
    Module.Dual (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) :=
  Submodule.liftQ (NK.Reconstruct.invisibleSubmodule (K := K) (K' := Ω) (ℓ := ℓ))
    (NK.Reconstruct.dualToLinear χ)
    (by
      intro x hx
      rw [LinearMap.mem_ker, NK.Reconstruct.dualToLinear_apply]
      exact (NK.Reconstruct.mem_invisibleSubmodule_iff x).mp hx χ)

/-- The descent map evaluated on a class: it is the original character on representatives. -/
@[simp] theorem dualDescentFun_apply_mk (K : Type) [Field K] [NumberField K] (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
    (x : Additive (NK.Reconstruct.Gamma K Ω ℓ)) :
    dualDescentFun K Ω ℓ χ (Submodule.Quotient.mk x) = χ x := by
  simp only [dualDescentFun, Submodule.liftQ_apply, NK.Reconstruct.dualToLinear_apply]

/-- **The descent map is `ℤ_ℓ`-linear**, by the pointwise module structure on the dual and the
linearity of `Submodule.liftQ` in the map. -/
noncomputable def dualDescent (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ →ₗ[PadicInt ℓ]
      Module.Dual (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) where
  toFun := dualDescentFun K Ω ℓ
  map_add' χ ψ := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := NK.Reconstruct.hausMk_surjective y
    simp
  map_smul' a χ := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := NK.Reconstruct.hausMk_surjective y
    simp

/-- The descent map on representatives: it evaluates the character at a representative. -/
@[simp] theorem dualDescent_apply_mk (K : Type) [Field K] [NumberField K] (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
    (x : Additive (NK.Reconstruct.Gamma K Ω ℓ)) :
    dualDescent K Ω ℓ χ (Submodule.Quotient.mk x) = χ x := by
  show dualDescentFun K Ω ℓ χ (Submodule.Quotient.mk x) = χ x
  simp

/-- **The descent map is injective**: the quotient map `Γ_K ↠ HausQuot` is surjective, so a
character is determined by its descent. -/
theorem dualDescent_injective (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (dualDescent K Ω ℓ) := by
  intro χ ψ h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  have h1 : dualDescent K Ω ℓ χ (Submodule.Quotient.mk x)
      = dualDescent K Ω ℓ ψ (Submodule.Quotient.mk x) := by rw [h]
  simpa using h1

/-! ## The `finrank` of the Hausdorff quotient is that of the dual -/

/-- **`finrank (HausQuot K K' ℓ) = finrank (Dual (Γ_K) ℓ)`**, for every topological setting in
which `HausQuot` is *defined* as `Γ_K ⧸ ⋂_χ ker χ` — no arithmetic input.

`Module.finrank` is `Cardinal.toNat ∘ Module.rank`, so it is enough to control the two *finiteness*
statements:

* if `rank (Dual Γ_K) < ℵ₀` then `rank (HausQuot) ≤ rank (Dual Γ_K) < ℵ₀`
  (`NK.RankTheoryDeep.rank_hausQuot_le_rank_dual`), and conversely
  `rank (Dual Γ_K) ≤ rank (Module.Dual (HausQuot)) ≤ rank (HausQuot)` by the descent
  `dualDescent` (`dualDescent_injective`) and
  `NK.RankTheoryDeep.rank_dual_le_rank_of_rank_lt_aleph0`; the two ranks are therefore *equal*;
* if `rank (Dual Γ_K) ≥ ℵ₀` then `rank (HausQuot) ≥ ℵ₀` by the same computation (were
  `rank (HausQuot)` finite, so would `rank (Dual Γ_K)` be), so both `toNat`s are `0`. -/
theorem finrank_hausQuot_eq_finrank_dualGamma (K : Type) [Field K] [NumberField K] (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ)
      = Module.finrank (PadicInt ℓ)
          (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ) := by
  by_cases hfin : Module.rank (PadicInt ℓ)
      (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ) < Cardinal.aleph0
  · have hle := NK.RankTheoryDeep.rank_hausQuot_le_rank_dual (K := K) (K' := Ω) (ℓ := ℓ) hfin
    have hMfin : Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) < Cardinal.aleph0 :=
      lt_of_le_of_lt hle hfin
    have hge : Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
        ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) :=
      le_trans
        (LinearMap.rank_le_of_injective (dualDescent K Ω ℓ) (dualDescent_injective K Ω ℓ))
        (NK.RankTheoryDeep.rank_dual_le_rank_of_rank_lt_aleph0 ℓ
          (NK.Reconstruct.HausQuot K Ω ℓ) hMfin)
    exact congrArg Cardinal.toNat (le_antisymm hle hge)
  · have hMinf : Cardinal.aleph0 ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) := by
      by_contra h
      have hMfin : Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) < Cardinal.aleph0 :=
        not_le.mp h
      have hge : Module.rank (PadicInt ℓ)
          (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
          ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) :=
        le_trans
          (LinearMap.rank_le_of_injective (dualDescent K Ω ℓ) (dualDescent_injective K Ω ℓ))
          (NK.RankTheoryDeep.rank_dual_le_rank_of_rank_lt_aleph0 ℓ
            (NK.Reconstruct.HausQuot K Ω ℓ) hMfin)
      exact absurd (lt_of_le_of_lt hge hMfin) hfin
    show Cardinal.toNat (Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ))
      = Cardinal.toNat (Module.rank (PadicInt ℓ)
          (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ))
    rw [Cardinal.toNat_eq_zero.mpr (Or.inr hMinf),
      Cardinal.toNat_eq_zero.mpr (Or.inr (not_lt.mp hfin))]

/-! ## The requested lemma -/

/-- **The idèle/Γ bridge in `finrank` form, from `ArtinDualBridge`.**

Given ℓ-adic Artin reciprocity at the separable closure in the form of the equality of the
`ℤ_2`-ranks of the continuous duals of `Γ_K^{Ω}` and of the idèle class group `C_K`, the
`finrank` of the Hausdorff quotient of `Γ_K^{Ω}` and that of `Hom_cts(C_K, ℤ_2)` agree:

```
finrank (ℤ_2) (Γ_K^{Ω} ⧸ invisible) = finrank (ℤ_2) Hom_cts(C_K, ℤ_2).
```

The first step is `finrank_hausQuot_eq_finrank_dualGamma`, an elementary property of the definition
of the Hausdorff quotient; the second is `hb` (an equality of `Cardinal`s, hence of their `toNat`s). -/
theorem hausQuot_finrank_eq_dual_idele_of_artin (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] (hb : NK.RankTheoryDeep.ArtinDualBridge Ω 2)
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω] :
    Module.finrank (PadicInt 2) (NK.Reconstruct.HausQuot K Ω 2)
      = Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) 2) := by
  have hbK := hb K
  simp only [NK.RankTheoryDeep.dualRank] at hbK
  rw [finrank_hausQuot_eq_finrank_dualGamma K Ω 2]
  show Cardinal.toNat (Module.rank (PadicInt 2)
      (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω 2) 2))
    = Cardinal.toNat (Module.rank (PadicInt 2)
      (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) 2))
  exact congrArg Cardinal.toNat hbK

end NK.NUV2
