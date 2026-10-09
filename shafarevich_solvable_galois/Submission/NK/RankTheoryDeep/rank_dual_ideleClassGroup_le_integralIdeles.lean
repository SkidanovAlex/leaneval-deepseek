import Mathlib
import Submission.NK.RankTheoryDeep.IdeleRankDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle class group vs. the integral idèles: the rank inequality on the duals

This file proves the lemma requested by the idèle-side rank assembly,

`NK.RankTheoryDeep.rank_dual_ideleClassGroup_le_integralIdeles`, i.e.

`rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ) ≤ rank_{ℤ_ℓ} Hom_cts(𝕀_int K, ℤ_ℓ)`,

for every number field `K` and every prime `ℓ`.

## The mathematics

The target of the naive map is *not* surjective: `𝕀_int K = ∏_v 𝒪_vˣ` maps into `C_K` with image
of *infinite* index in the naive sense (the idèles with non-negative valuation at every finite
place are precisely the ones whose attached fractional ideal is integral, and among them the units
at every finite place are the ones with *trivial* divisor ideal).  What saves the inequality is
that the image `H = mk '' 𝕀_int K ≤ C_K` is the kernel of the **divisor class map**
`C_K →* Cl(K)`, and the class group is *finite*: consequently

* every element of `C_K ⧸ H ≅ Cl(K)` is torsion, so a `ℤ_ℓ`-valued character of `C_K` which
  vanishes on `H` vanishes on all of `C_K` (a torsion-free group has no nontrivial homomorphism
  from a finite group: `χ x ≠ 0` would give `0 = χ (x ^ N) = N · χ x` with `N = |Cl(K)| > 0`);
* hence `Dual (C_K) ℓ → Dual (𝕀_int K) ℓ` — the restriction of characters along `𝕀_int K → C_K` —
  is *injective*, and an injective `ℤ_ℓ`-linear map cannot decrease `Module.rank`
  (`LinearMap.rank_le_of_injective`).

The finiteness of the class group of a number field is Mathlib's
`NumberField.RingOfIntegers.instFintypeClassGroup` (`Mathlib.NumberTheory.NumberField.ClassNumber`);
the exact sequence `H = ker (C_K → Cl(K))` is the on-disk
`NK.GlobalCFT.IdeleClassGroup.local_global_exact_sequence`
(`Submission/Work/GlobalCFT/IdeleClassGroupExact.lean`), which realizes the kernel of the divisor
class map as the image of `𝕀_int K` exactly as needed here.  No arithmetic input beyond that is
used.

## Relation to the sibling lemma

Together with `NK.RankTheoryDeep.rank_dual_integralIdeles_le_pi`
(`rank Hom_cts(𝕀_int K, ℤ_ℓ) ≤ rank Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)`, the identification of `𝕀_int K` with
the product of the local unit groups) this gives the first two steps of the CoNF (10.3.20)
computation

`rank Hom_cts(C_K, ℤ_ℓ) ≤ rank Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)`,
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

open NK.GlobalCFT

/-- The componentwise inclusion of the integral idèles in the idèle class group,
`𝕀_int K = ∏_v 𝒪_vˣ →* C_K`, i.e. the restriction of the quotient map `𝕀 K →* C_K`. -/
noncomputable def integralIdelesToClassGroup (K : Type u) [Field K] [NumberField K] :
    ↥(Idele.integralIdeles K) →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (Idele.integralIdeles K).subtype

/-- The map `𝕀_int K →* C_K` is continuous: it is the composite of the continuous quotient map
`𝕀 K →* C_K` (the quotient topology of `C_K = 𝕀 K ⧸ Kˣ`) with the inclusion of the subtype
`𝕀_int K ⊆ 𝕀 K`. -/
theorem continuous_integralIdelesToClassGroup (K : Type u) [Field K] [NumberField K] :
    Continuous (integralIdelesToClassGroup K) :=
  have hmk : Continuous (IdeleClassGroup.mk K) := continuous_quotient_mk'
  hmk.comp continuous_subtype_val

/-- **The restriction map on continuous characters is injective.**

If a continuous character `h : Dual (C_K) ℓ` vanishes on the image of `𝕀_int K →* C_K`, then it is
zero.

Proof.  By the exact sequence `NK.GlobalCFT.IdeleClassGroup.local_global_exact_sequence` the
image `H = mk '' 𝕀_int K` is the kernel of the divisor class map `f : C_K →* Cl(K)`, and `f` is
surjective onto the **finite** group `Cl(K)`.  Hence for `x : C_K` and `N = |Cl(K)| > 0` one has
`x ^ N ∈ H`, so that `h x = 0` because

`0 = h (x ^ N) = h (N • x) = N · h x`

in the torsion-free domain `ℤ_ℓ`. -/
theorem dualMap_integralIdelesToClassGroup_eq_zero (K : Type u) [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (h : NK.Reconstruct.Dual (IdeleClassGroup K) ℓ)
    (hh : NK.Reconstruct.dualMap ℓ (integralIdelesToClassGroup K)
            (continuous_integralIdelesToClassGroup K) h = 0) : h = 0 := by
  obtain ⟨f, hker, _hsurj⟩ := IdeleClassGroup.local_global_exact_sequence K
  set N : ℕ := Nat.card (ClassGroup (𝓞 K)) with hN
  have hNpos : 0 < N := Nat.card_pos
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro y
  -- `x ^ N` lies in the image of the integral idèles: it is killed by the divisor class map.
  have hpow : f (Additive.toMul y ^ N) = 1 := by
    have h1 := pow_card_eq_one' (x := f (Additive.toMul y))
    simpa [hN] using h1
  have hmem : Additive.toMul y ^ N ∈ (Idele.integralIdeles K).map
      (IdeleClassGroup.mk K) := by
    rw [← hker, MonoidHom.mem_ker, hpow]
  obtain ⟨y0, hy0mem, hy0⟩ := Subgroup.mem_map.mp hmem
  -- `h` vanishes there, by hypothesis.
  have hz : (h : Additive (IdeleClassGroup K) →+ PadicInt ℓ)
      (Additive.ofMul (Additive.toMul y ^ N)) = 0 := by
    rw [← hy0]
    have h2 := congrArg (fun u : NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) ℓ =>
      u (Additive.ofMul (⟨y0, hy0mem⟩ : ↥(Idele.integralIdeles K)))) hh
    simpa [NK.Reconstruct.dualMap_apply, integralIdelesToClassGroup] using h2
  -- and `h (N • y) = N · h y`.
  have hval : (h : Additive (IdeleClassGroup K) →+ PadicInt ℓ)
      (Additive.ofMul (Additive.toMul y ^ N))
        = (N : PadicInt ℓ) * ((h : Additive (IdeleClassGroup K) →+ PadicInt ℓ) y) := by
    rw [ofMul_pow, ofMul_toMul, map_nsmul, nsmul_eq_mul]
  have hzero : (N : PadicInt ℓ) * ((h : Additive (IdeleClassGroup K) →+ PadicInt ℓ) y) = 0 := by
    rw [← hval, hz]
  rcases mul_eq_zero.mp hzero with h3 | h3
  · exact absurd h3 (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos))
  · exact h3

/-- **The idèle class group is no larger than the integral idèles for the continuous dual**: the
`ℤ_ℓ`-rank of `Hom_cts(C_K, ℤ_ℓ)` is at most the `ℤ_ℓ`-rank of `Hom_cts(𝕀_int K, ℤ_ℓ)`.

The restriction `Φ : Dual (C_K) ℓ →ₗ[ℤ_ℓ] Dual (𝕀_int K) ℓ` along the continuous homomorphism
`𝕀_int K →* C_K` (`integralIdelesToClassGroup`) is injective
(`dualMap_integralIdelesToClassGroup_eq_zero`), and an injective linear map does not decrease
`Module.rank`. -/
theorem rank_dual_ideleClassGroup_le_integralIdeles (K : Type u) [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) ℓ)
      ≤ Module.rank (PadicInt ℓ)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) ℓ) := by
  have hcont : Continuous (integralIdelesToClassGroup K) :=
    continuous_integralIdelesToClassGroup K
  let Φ : NK.Reconstruct.Dual (IdeleClassGroup K) ℓ →ₗ[PadicInt ℓ]
      NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) ℓ :=
    { toFun := NK.Reconstruct.dualMap ℓ (integralIdelesToClassGroup K) hcont
      map_add' := fun f g =>
        NK.Reconstruct.dualMap_add ℓ (integralIdelesToClassGroup K) hcont f g
      map_smul' := by
        intro a f
        apply Subtype.ext
        apply AddMonoidHom.ext
        intro x
        simp [NK.Reconstruct.dualMap_apply, smul_dual_apply] }
  refine LinearMap.rank_le_of_injective Φ ?_
  intro f g hfg
  have hzero : Φ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hsub : f - g = 0 :=
    dualMap_integralIdelesToClassGroup_eq_zero K (f - g) hzero
  exact sub_eq_zero.mp hsub

end NK.RankTheoryDeep
