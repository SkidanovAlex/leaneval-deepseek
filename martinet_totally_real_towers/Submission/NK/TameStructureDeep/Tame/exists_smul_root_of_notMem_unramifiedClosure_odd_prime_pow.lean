/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer pairing over `κ^{ur}`, `ℓ` an odd prime, exponent `ℓ ^ k`

This is the prime-power refinement of
`NK.TameStructureDeep.Tame.exists_smul_root_of_notMem_unramifiedClosure`: if `β ^ ℓ ^ k = a` and
`a` has no `ℓ`-th root in `κ^{ur}` (i.e. `β ^ ℓ ^ (k-1) ∉ κ^{ur}`), then for *every* `ℓ ^ k`-th root
of unity `ζ` the Kummer pairing `σ ↦ σ β / β` on `Gal(K'/κ^{ur})` attains `ζ`:

  `∃ σ ∈ (κ^{ur}).fixingSubgroup, σ β = ζ β`.

The argument is the classical one and needs no hypothesis on `κ^{ur}` other than the Kummer input:
`X ^ ℓ ^ k - a` is irreducible over `L = κ^{ur}` by Capelli's theorem in the odd case
(Mathlib's `X_pow_sub_C_irreducible_of_prime_pow`, which is where `ℓ ≠ 2` enters), hence
`minpoly L β = X ^ ℓ ^ k - a`; every `ℓ ^ k`-th root of unity times `β` is then a root of this
minimal polynomial, i.e. a conjugate root of `β` over `L`, and normal extensions realise conjugate
roots by automorphisms (`IsConjRoot.exists_algEquiv`).

Note that `ζ` ranges over *all* `ℓ ^ k`-th roots of unity in `K'`, without any hypothesis that they
lie in `κ^{ur}`: this is exactly why the statement only needs `β ^ ℓ ^ k = a` and not
`μ_{ℓ^k} ⊆ κ^{ur}`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.Kummer
import Submission.NK.TameStructureDeep.Tame.exists_smul_root_of_notMem_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure

open scoped Classical
open Polynomial IntermediateField

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

/-- **The Kummer pairing is surjective, in the `ℓ ^ k`-power form.**

Let `κ` be a field with separable closure `K'`, `ℓ` an odd prime, `a ∈ κ`, `β ∈ K'` with
`β ^ ℓ ^ k = a`.  If `a` has no `ℓ`-th root in the unramified closure `κ^{ur} = κ(μ_{p'})`
(equivalently `β ^ ℓ ^ (k-1) ∉ κ^{ur}`), then every `ℓ ^ k`-th root of unity `ζ ∈ K'` is
attained by the Kummer cocycle: there is `σ ∈ Gal(K'/κ^{ur})` with `σ β = ζ β`. -/
theorem exists_smul_root_of_notMem_unramifiedClosure_odd_prime_pow {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p ℓ k : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hpℓ : ℓ ≠ p)
    {a : κ} {β : K'} (hβ : β ^ ℓ ^ k = algebraMap κ K' a)
    (hnroot : ∀ x : K', x ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p →
      x ^ ℓ ≠ algebraMap κ K' a)
    {ζ : K'} (hζ : ζ ^ ℓ ^ k = 1) :
    ∃ σ : Gal(K'/κ),
      σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup ∧
        σ β = ζ * β := by
  classical
  -- the maximal unramified extension `κ^{ur} = κ(μ_{p'})`
  set L : IntermediateField κ K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p with hL
  -- `a`, viewed inside `L`
  set aL : L := ⟨algebraMap κ K' a, IntermediateField.algebraMap_mem L a⟩ with haL
  -- the Kummer input: `a` has no `ℓ`-th root in `L`
  have haL' : ∀ b : L, b ^ ℓ ≠ aL := by
    intro b hb
    refine hnroot (b : K') b.2 ?_
    have h := congrArg (fun x : L => (x : K')) hb
    simpa [aL] using h
  -- Capelli: `X ^ ℓ ^ k - a` is irreducible over `L`, as `ℓ` is odd
  have hIrr : Irreducible (X ^ (ℓ ^ k) - C aL) :=
    X_pow_sub_C_irreducible_of_prime_pow hℓ hodd k haL'
  have hmonic : (X ^ (ℓ ^ k) - C aL).Monic := monic_X_pow_sub_C aL (pow_ne_zero k hℓ.ne_zero)
  -- `β` is a root
  have hrootβ : aeval β (X ^ (ℓ ^ k) - C aL) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero]
    simpa [aL] using hβ
  -- so is `ζ * β`, for every `ℓ ^ k`-th root of unity `ζ`
  have hrootζ : aeval (ζ * β) (X ^ (ℓ ^ k) - C aL) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero, mul_pow, hζ, one_mul]
    simpa [aL] using hβ
  -- hence both have minimal polynomial `X ^ ℓ ^ k - a` over `L`
  have hβint : minpoly L β = X ^ (ℓ ^ k) - C aL :=
    (minpoly.eq_of_irreducible_of_monic hIrr hrootβ hmonic).symm
  have hζint : minpoly L (ζ * β) = X ^ (ℓ ^ k) - C aL :=
    (minpoly.eq_of_irreducible_of_monic hIrr hrootζ hmonic).symm
  -- i.e. `ζ * β` is a conjugate root of `β` over `L`
  have hconj : IsConjRoot L β (ζ * β) := hβint.trans hζint.symm
  -- `K'/L` is normal, so conjugate roots are related by an `L`-automorphism
  obtain ⟨f, hf⟩ := IsConjRoot.exists_algEquiv hconj
  -- read this automorphism as an element of `Gal(K'/κ)` fixing `κ^{ur}` pointwise
  refine ⟨(L.fixingSubgroupEquiv.symm f.symm : L.fixingSubgroup), ?_, ?_⟩
  · exact (L.fixingSubgroupEquiv.symm f.symm).2
  · have : f.symm β = ζ * β := (f.symm_apply_eq).mpr hf.symm
    exact this

end NK.TameStructureDeep.Tame
