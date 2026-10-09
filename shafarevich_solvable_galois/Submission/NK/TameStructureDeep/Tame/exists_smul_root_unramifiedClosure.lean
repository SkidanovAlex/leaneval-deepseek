/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer pairing over `κ^{ur}` is onto `μ_n`, for every `n` prime to the residue characteristic

Let `κ = K_𝔭` be the completion of a number field at a finite place, `π` a uniformiser of `κ`, and
`K'` a separable closure of `κ`.  Write `κ^{ur} = κ(μ_{p'})` for the maximal unramified extension
of `κ` inside `K'`, realised as `NK.LocalAnabelian.unramifiedClosure` of the residue
characteristic `p`.

The arithmetic input of the tamely ramified structure theorem
(`Tame/layerDegree.lean`, `Tame/UnramifiedNoPow.lean`) is that `π` has no `n`-th root in `κ^{ur}`
for `n ≥ 2` prime to `p`.  Consequently `κ^{ur}(β)` has degree exactly `n` over `κ^{ur}` for any
`β` with `β ^ n = π` (`NK.TameStructureDeep.Tame.finrank_adjoin_urCl`).  Hence `X ^ n - C π` *is*
the minimal polynomial of `β` over `κ^{ur}`: no irreducibility input (Capelli's theorem) is needed,
the degree statement is available.

From this the Kummer pairing `σ ↦ σ β / β : Gal(K'/κ^{ur}) → μ_n` is onto: every `n`-th root of
unity `ζ` is a conjugate of `β` (`ζ β` is another root of the minimal polynomial), and normality
of `K'/κ^{ur}` realises conjugate roots by automorphisms.

The main result is `exists_smul_root_unramifiedClosure`: for a *primitive* `n`-th root of unity `ζ`
there is `τ ∈ Gal(K'/κ^{ur})` with `τ β = ζ β` and `τ ζ = ζ`.  The second condition is automatic,
`ζ` lying in `κ^{ur}` because `(n, p) = 1`; it is recorded because the tamely ramified structure
theorem uses the twist of the Kummer pairing by the action of `τ` on roots of unity.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.layerDegree
import Submission.NK.LocalAnabelian.ResidueField.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

theorem exists_smul_root_unramifiedClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n (NK.TameStructureDeep.Tame.resCharAt 𝔭))
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) {β : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletionIntegers K))
    {ζ : K'} (hζ : IsPrimitiveRoot ζ n) :
    ∃ τ : Gal(K'/𝔭.adicCompletion K),
      τ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
              (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup ∧
        τ β = ζ * β ∧ τ ζ = ζ := by
  classical
  haveI hchark : CharZero (𝔭.adicCompletion K) :=
    Algebra.charZero_of_charZero K (𝔭.adicCompletion K)
  haveI hchar : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  haveI hsepcl : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  -- the maximal unramified extension `κ^{ur} = κ(μ_{p'})`
  set L : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) with hL
  -- a primitive `n`-th root of unity is already unramified, `(n, p) = 1`
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpnd : ¬ NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hcop)
  have hζL : ζ ∈ L :=
    NK.TameStructureDeep.mem_unramifiedClosure_of_isPrimitiveRoot hpnd hζ
  -- the uniformiser, viewed in `κ^{ur}`
  set a : ↥L := ⟨algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K),
    IntermediateField.algebraMap_mem L _⟩ with ha
  have hβa : β ^ n = algebraMap ↥L K' a := by
    rw [hβ, ha, IntermediateField.algebraMap_apply]
  -- `β` is integral over `κ^{ur}` and `[κ^{ur}(β) : κ^{ur}] = n`
  have hβint : IsIntegral ↥L β :=
    ⟨X ^ n - C a, monic_X_pow_sub_C a hn.ne', by simp [hβa]⟩
  have hfin : Module.finrank ↥L ↥(IntermediateField.adjoin ↥L ({β} : Set K')) = n :=
    finrank_adjoin_urCl 𝔭 hn hcop hπ hβ
  have hminp : (minpoly ↥L β).natDegree = n := by
    rw [← adjoin.finrank hβint]; exact hfin
  have hdvd : minpoly ↥L β ∣ X ^ n - C a := by
    refine minpoly.dvd ↥L β ?_
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero]; exact hβa
  -- hence `X ^ n - C π` *is* the minimal polynomial of `β`
  have hminpeq : X ^ n - C a = minpoly ↥L β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint)
      (monic_X_pow_sub_C a hn.ne') hdvd (by rw [natDegree_X_pow_sub_C, hminp])
  -- and so is the minimal polynomial of `ζ β`, for every `n`-th root of unity `ζ`
  have hrootζ : aeval (ζ * β) (X ^ n - C a : Polynomial ↥L) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero, mul_pow, hζ.pow_eq_one, one_mul]
    exact hβa
  have hminpζ : X ^ n - C a = minpoly ↥L (ζ * β) :=
    minpoly.eq_of_irreducible_of_monic (hminpeq ▸ minpoly.irreducible hβint) hrootζ
      (monic_X_pow_sub_C a hn.ne')
  have hconj : IsConjRoot ↥L β (ζ * β) := hminpeq.symm.trans hminpζ
  -- conjugate roots are related by an automorphism, `K'/κ^{ur}` being normal
  obtain ⟨f, hf⟩ := IsConjRoot.exists_algEquiv hconj
  have hfsymm : f.symm β = ζ * β := (f.symm_apply_eq).mpr hf.symm
  refine ⟨(L.fixingSubgroupEquiv.symm f.symm : L.fixingSubgroup),
    (L.fixingSubgroupEquiv.symm f.symm).2, hfsymm, ?_⟩
  -- `τζ = ζ`: the automorphism fixes `κ^{ur}`, and `ζ ∈ κ^{ur}`
  exact (IntermediateField.mem_fixingSubgroup_iff L _).mp
    (L.fixingSubgroupEquiv.symm f.symm).2 ζ hζL

end

end NK.TameStructureDeep.Tame
