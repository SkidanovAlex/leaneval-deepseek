import Mathlib
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.Reconstruct.gammaSmul
import Submission.NK.Reconstruct.GammaModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The duality step of the corrected rank theory: `rank (HausQuot) ≤ rank (Dual)`

This file proves the lemma requested by the rank-theory chapter,

`NK.RankTheoryDeep.rank_hausQuot_le_rank_dual`,

together with the abstract statement about `ℤ_ℓ`-modules on which it rests:
**the linear dual of a `ℤ_ℓ`-module of finite `ℤ_ℓ`-rank has rank at most that of the module**
(`NK.RankTheoryDeep.rank_dual_le_rank_of_rank_lt_aleph0`).

## The abstract input

Let `R = ℤ_[ℓ]` be the ring of `ℓ`-adic integers, `K = ℚ_[ℓ]` its fraction field, and `M` an
`R`-module with `rank_R M < ℵ₀`.  Then `rank_R (Module.Dual R M) ≤ rank_R M`.  The proof is the
localization argument, *without any torsion-freeness hypothesis*:

* `IsBaseChange.toDual` for the base change `M → K ⊗[R] M` gives an `R`-linear map
  `Module.Dual R M → Module.Dual K (K ⊗[R] M)`, injective because `R → K` is injective;
* `IsBaseChange.rank_eq` gives `rank_K (K ⊗[R] M) = rank_R M = n < ℵ₀`, so `K ⊗[R] M` is
  finite-dimensional over the field `K`;
* for a finite-dimensional vector space the dual has the same dimension
  (`Subspace.dual_finrank_eq`), and `IsFractionRing.rank_right_eq` computes the rank of a
  `K`-vector space viewed as an `R`-module.

This is the step that the docstring of the main lemma warns about: it avoids
`Module.free_of_finite_type_torsion_free` (which would need `Module.Finite M`, unavailable under
the hypothesis `rank M < ℵ₀`) by passing to the base change.

## The main lemma

`NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ invisibleSubmodule` is the quotient of Shimizu's
`ℓ`-adic abelianisation by the subgroup invisible to every continuous character
(`NK.Reconstruct.invisibleSubmodule`).  Since `invisibleSubmodule` is *defined* as the kernel of
the evaluation map

`e : Additive Γ_K →ₗ[ℤ_ℓ] Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ)`,  `e x = (χ ↦ χ x)`,

`e` descends to an *injective* `ℤ_ℓ`-linear map on the Hausdorff quotient, and the two rank
inequalities combine to

`rank (HausQuot K K' ℓ) ≤ rank (Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ)) ≤ rank (Dual (Γ_K) ℓ)`.

The `ℤ_ℓ`-linearity of `e` uses `NK.Reconstruct.dual_apply_smul` (every continuous additive
character is `ℤ_ℓ`-linear) and the pointwise module structure on the dual
(`NK.Reconstruct.instModuleDual`); the identification of the kernel is
`NK.Reconstruct.mem_invisibleSubmodule_iff`.

See `Submission/Work/RankTheoryDeep/README.md` §4 and `IdeleRank.lean` for the use of this result
in replacing the falsified `NK.ShimizuRank.GammaTFRankFinite` by
`NK.RankTheoryDeep.HausQuotRankFinite`.
-/

set_option linter.style.haveILetI false

open scoped TensorProduct

namespace NK.RankTheoryDeep

universe u v

/-! ## The linear dual of a finite-rank module over `ℤ_ℓ` -/

/-- **The linear dual of a `ℤ_ℓ`-module of finite `ℤ_ℓ`-rank does not have larger rank.**

For an `ℤ_[ℓ]`-module `M` of rank `< ℵ₀`, the `ℤ_ℓ`-linear dual `M →ₗ[ℤ_ℓ] ℤ_ℓ` has
`ℤ_ℓ`-rank at most `rank_{ℤ_ℓ} M`.

The proof passes to the base change `K ⊗[ℤ_ℓ] M`, `K = ℚ_[ℓ]`: the dual embeds into
`Module.Dual K (K ⊗[ℤ_ℓ] M)` (`IsBaseChange.toDual`), the base change has the same rank as `M`
(`IsBaseChange.rank_eq`) hence is finite-dimensional over the field `K`, and a finite-dimensional
vector space has a dual of the same dimension. -/
theorem rank_dual_le_rank_of_rank_lt_aleph0 (p : ℕ) [Fact p.Prime] (M : Type v)
    [AddCommGroup M] [Module (PadicInt p) M]
    (h : Module.rank (PadicInt p) M < Cardinal.aleph0) :
    Module.rank (PadicInt p) (Module.Dual (PadicInt p) M) ≤ Module.rank (PadicInt p) M := by
  have hbc : IsBaseChange (Padic p) (TensorProduct.mk (PadicInt p) (Padic p) M 1) :=
    TensorProduct.isBaseChange _ _ _
  have hrank : Module.rank (Padic p) ((Padic p) ⊗[PadicInt p] M) = Module.rank (PadicInt p) M :=
    hbc.rank_eq
  have hW : Module.rank (Padic p) ((Padic p) ⊗[PadicInt p] M) < Cardinal.aleph0 := by
    rw [hrank]; exact h
  haveI : Module.Finite (Padic p) ((Padic p) ⊗[PadicInt p] M) :=
    Module.rank_lt_aleph0_iff.mp hW
  have hinj : Function.Injective (hbc.toDual : Module.Dual (PadicInt p) M →ₗ[PadicInt p]
      Module.Dual (Padic p) ((Padic p) ⊗[PadicInt p] M)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    ext m
    refine IsFractionRing.injective (PadicInt p) (Padic p) ?_
    have h1 := hbc.toDual_comp_apply f m
    rw [hf] at h1
    simp only [map_zero, LinearMap.zero_apply] at h1 ⊢
    exact h1.symm
  calc Module.rank (PadicInt p) (Module.Dual (PadicInt p) M)
      ≤ Module.rank (PadicInt p) (Module.Dual (Padic p) ((Padic p) ⊗[PadicInt p] M)) :=
        LinearMap.rank_le_of_injective _ hinj
    _ = Module.rank (Padic p) (Module.Dual (Padic p) ((Padic p) ⊗[PadicInt p] M)) :=
        (IsFractionRing.rank_right_eq (PadicInt p) (Padic p) _).symm
    _ = Module.rank (Padic p) ((Padic p) ⊗[PadicInt p] M) := by
        rw [← Module.finrank_eq_rank (Padic p)
              (Module.Dual (Padic p) ((Padic p) ⊗[PadicInt p] M)),
            ← Module.finrank_eq_rank (Padic p) ((Padic p) ⊗[PadicInt p] M),
            Subspace.dual_finrank_eq]
    _ = Module.rank (PadicInt p) M := hrank

/-! ## The evaluation map and the Hausdorff quotient -/

section Main

variable {K : Type u} [Field K] [NumberField K] {K' : Type u} [Field K']
  [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The evaluation map** `x ↦ (χ ↦ χ x)` from Shimizu's `ℓ`-adic abelianisation into the
`ℤ_ℓ`-linear dual of its continuous dual.

It is `ℤ_ℓ`-linear because every continuous character is `ℤ_ℓ`-linear
(`NK.Reconstruct.dual_apply_smul`) and the dual carries the pointwise module structure
(`NK.Reconstruct.instModuleDual`). -/
noncomputable def evalMap :
    Additive (NK.Reconstruct.Gamma K K' ℓ) →ₗ[PadicInt ℓ]
      Module.Dual (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ) where
  toFun x :=
    { toFun := fun g => (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
      map_add' := by
        intro g h
        change ((g + h : NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)
          : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
          = (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
            + (h : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
        rw [AddSubgroup.coe_add, AddMonoidHom.add_apply]
      map_smul' := by
        intro a g
        change ((a • g : NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)
          : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
          = a • (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
        rw [NK.Reconstruct.smul_dual_apply, smul_eq_mul] }
  map_add' := by
    intro x y
    ext g
    exact g.1.map_add x y
  map_smul' := by
    intro a x
    ext g
    change (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) (a • x)
      = a • (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x
    rw [NK.Reconstruct.dual_apply_smul
      (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) g.2 a x, smul_eq_mul]

/-- **The kernel of the evaluation map is the invisible subgroup** — by definition of
`NK.Reconstruct.invisibleSubmodule` as the intersection of the kernels of the continuous
characters, `NK.Reconstruct.mem_invisibleSubmodule_iff`. -/
theorem ker_evalMap : LinearMap.ker (evalMap (K := K) (K' := K') (ℓ := ℓ))
    = NK.Reconstruct.invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) := by
  ext x
  rw [LinearMap.mem_ker, NK.Reconstruct.mem_invisibleSubmodule_iff]
  constructor
  · intro hx g
    have h2 : (evalMap (K := K) (K' := K') (ℓ := ℓ) x) g = 0 := by rw [hx]; rfl
    change (g : Additive (NK.Reconstruct.Gamma K K' ℓ) →+ PadicInt ℓ) x = 0 at h2
    exact h2
  · intro hx
    ext g
    exact hx g

/-- **The evaluation map descends to the Hausdorff quotient** `Γ_K ⧸ invisibleSubmodule`,
giving a `ℤ_ℓ`-linear map `HausQuot K K' ℓ → Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ)`. -/
noncomputable def hausToDual :
    NK.Reconstruct.HausQuot K K' ℓ →ₗ[PadicInt ℓ]
      Module.Dual (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ) :=
  Submodule.liftQ (NK.Reconstruct.invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ))
    (R₂ := PadicInt ℓ)
    (M₂ := Module.Dual (PadicInt ℓ)
      (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ))
    (evalMap (K := K) (K' := K') (ℓ := ℓ))
    (le_of_eq (ker_evalMap (K := K) (K' := K') (ℓ := ℓ)).symm)

/-- The descended map is the evaluation map on representatives. -/
theorem hausToDual_hausMk (x : Additive (NK.Reconstruct.Gamma K K' ℓ)) :
    hausToDual (K := K) (K' := K') (ℓ := ℓ) (NK.Reconstruct.hausMk (K := K) (K' := K') (ℓ := ℓ) x)
      = evalMap (K := K) (K' := K') (ℓ := ℓ) x := by
  rw [NK.Reconstruct.hausMk_apply]
  exact Submodule.liftQ_apply _ (R₂ := PadicInt ℓ)
    (M₂ := Module.Dual (PadicInt ℓ)
      (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ))
    (evalMap (K := K) (K' := K') (ℓ := ℓ)) x

/-- **The descended map is injective**: its kernel is the invisible subgroup, which is exactly the
subgroup killed by the quotient map. -/
theorem hausToDual_injective : Function.Injective (hausToDual (K := K) (K' := K') (ℓ := ℓ)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  obtain ⟨x, rfl⟩ := NK.Reconstruct.hausMk_surjective (K := K) (K' := K') (ℓ := ℓ) y
  have hev : evalMap (K := K) (K' := K') (ℓ := ℓ) x = 0 := by
    rw [← hausToDual_hausMk (K := K) (K' := K') (ℓ := ℓ) x]
    exact hy
  rw [NK.Reconstruct.hausMk_eq_zero_iff, ← ker_evalMap, LinearMap.mem_ker]
  exact hev

/-- **The duality step of the corrected rank theory**: the Hausdorff quotient is no larger than
the continuous dual.

Let `Γ_K = NK.Reconstruct.Gamma K K' ℓ` be Shimizu's ℓ-adic abelianisation,
`HausQuot K K' ℓ = Γ_K ⧸ invisible` its Hausdorff (dual-faithful) quotient and
`Dual (Γ_K) ℓ = {f : Additive Γ_K →+ ℤ_ℓ // Continuous f}` its continuous dual.  If that dual has
**finite** `ℤ_ℓ`-rank, then

  `rank_{ℤ_ℓ} (HausQuot K K' ℓ) ≤ rank_{ℤ_ℓ} (Dual (Γ_K) ℓ)`.

Proof.  The evaluation map `e : Additive (Γ_K) →ₗ[ℤ_ℓ] Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ)`,
`e x = (χ ↦ χ x)`, is `ℤ_ℓ`-linear (`Dual` carries the pointwise module structure `instModuleDual`,
and `χ (a • x) = a * χ x` by `NK.Reconstruct.dual_apply_smul`), and its kernel is *exactly*
`invisibleSubmodule` by `NK.Reconstruct.mem_invisibleSubmodule_iff`.  Hence `e` descends to an
injective linear map on `HausQuot K K' ℓ`, giving
`rank (HausQuot) ≤ rank (Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ))` (`Submodule.rank_le`).
Finally `Dual (Γ_K) ℓ` is a submodule of `Hom(Γ_K, ℤ_ℓ)`, hence torsion-free over the domain `ℤ_ℓ`,
so `Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ) ↪ Hom_{ℤ_ℓ}(Dual (Γ_K) ℓ, ℚ_ℓ)` — a `ℚ_ℓ`-vector space of
dimension equal to `rank (Dual (Γ_K) ℓ)`, using the finiteness hypothesis to know that this
dimension is the honest rank.  *(Do not route this through freeness:
`Module.free_of_finite_type_torsion_free` needs `Module.Finite`, which `rank < ℵ₀` does not give.)*

This closes the gap between the two models of Shimizu's `r_ℓ(K)` that
`RankTheoryDeep/Refutation.lean` shows to be genuinely different: `r_ℓ(K)` is the rank of the
*continuous dual* (equivalently, by the idèle-class-group computation, of `Hom_cts(C_K, ℤ_ℓ)`),
which bounds the rank of `HausQuot` from *above* by the present result and from *below* by the
injection `Dual → (HausQuot ⊗ ℚ_ℓ)^*`; it is *not* the rank of `Γ_K ⧸ torsion`, which is `ℵ₀`.
Consequently `NK.ShimizuRank.GammaTFRankFinite` may be replaced, without loss, by the finite-rank
hypothesis on `Dual (Γ_K) ℓ` — see `NK.RankTheoryDeep.HausQuotRankFinite` and `README.md` §4.

Not vacuous: for the trivial level `K' = K` one has `Γ_K = 0` and both sides are `0`; for `K = ℚ`,
`ℓ = 2` both sides are `1` (the cyclotomic character generates the dual and the Hausdorff quotient
is `ℤ_2`).  The hypothesis is not automatic: for an arbitrary compact abelian pro-`ℓ` group the
bound can fail (`∏_I ℤ_ℓ` with `I` infinite has both sides `|I|`). -/
theorem rank_hausQuot_le_rank_dual {K : Type u} [Field K] [NumberField K] {K' : Type u} [Field K']
    [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)
      < Cardinal.aleph0) :
    Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K K' ℓ)
      ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ) := by
  calc Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K K' ℓ)
      ≤ Module.rank (PadicInt ℓ) (Module.Dual (PadicInt ℓ)
          (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)) :=
        LinearMap.rank_le_of_injective
          (hausToDual (K := K) (K' := K') (ℓ := ℓ))
          (hausToDual_injective (K := K) (K' := K') (ℓ := ℓ))
    _ ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ) :=
        rank_dual_le_rank_of_rank_lt_aleph0 ℓ _ h

end Main

end NK.RankTheoryDeep

