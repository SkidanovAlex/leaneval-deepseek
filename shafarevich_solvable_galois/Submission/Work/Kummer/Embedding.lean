/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cyclic embedding problem in Kummer theory

Let `L/K` be a cyclic extension of degree `n` and let `ζ ∈ K` be a primitive `n`-th root of unity.
The *cyclic embedding problem* with kernel `ℤ/n` asks whether `L` is contained in a cyclic
extension `M/K` of degree `n²`, i.e. whether the group extension

`1 → ℤ/n → ℤ/n² → ℤ/n → 1`

is realised by a Galois extension of `K`.

The Kummer-theoretic answer is that this is possible if and only if `ζ` is a norm from `L`, i.e.
if and only if the class of `ζ` in `Kˣ/N_{L/K}(Lˣ)` is trivial. Equivalently (this is the classical
form of the criterion) the cyclic algebra `(L/K, σ, ζ)` is split. The two halves are

* `Work.Kummer.exists_norm_eq_primRoot_of_cyclic_sq_extension` : if such an `M` exists then
  `ζ` is a norm from `L`;
* `Work.Kummer.exists_cyclic_sq_extension_of_norm_eq_primRoot` : if `ζ` is a norm from `L` then
  such an `M` exists.

This file records the criterion in the vocabulary of `normSubgroup` (`N_{L/K}(Lˣ) ≤ Kˣ`) and
states it in the "relative" form with `M` an explicit variable.

Note on the classical form of the criterion: if `L = K(α)` with `α ^ n = a`
(so `a ∈ Kˣ` generates the Kummer radical of `L/K`), then `N_{L/K}(α) = ζ ^ (n * (n - 1) / 2) * a`
(`Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator`). For odd `n` this equals `a`, so for
odd `n` the Kummer generator `a` is *always* a norm
(`Work.Kummer.exists_norm_eq_of_odd`), while for even `n` it equals `-a`; the sharp obstruction is
the class of `ζ` (equivalently, `μ_n ⊆ N_{L/K}(Lˣ)`), not the class of `a`.
-/
import Mathlib.FieldTheory.KummerExtension
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.Norm
import Submission.Work.Kummer.exists_norm_eq_primRoot_of_cyclic_sq_extension
import Submission.Work.Kummer.exists_cyclic_sq_extension_of_norm_eq_primRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.Kummer

variable {K : Type u} {L : Type u} {M : Type u} [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **The cyclic embedding problem: necessity.** If `L/K` (cyclic of degree `n`, `ζ` a primitive
`n`-th root of unity in `K`) is contained in a cyclic extension `M/K` of degree `n²`, then the
primitive root `ζ` lies in the norm group `N_{L/K}(Lˣ) ≤ Kˣ`. -/
theorem primRootUnit_mem_normSubgroup_of_cyclic_sq_extension {n : ℕ} [NeZero n] {ζ : K}
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    [IsGalois K L] [IsCyclic Gal(L/K)] (hζ : IsPrimitiveRoot ζ n)
    (hn : Module.finrank K L = n) (hnM : Module.finrank K M = n ^ 2) :
    primRootUnit hζ ∈ normSubgroup K L := by
  obtain ⟨η, hη⟩ := exists_norm_eq_primRoot_of_cyclic_sq_extension (K := K) (L := L) (M := M)
    hζ hn hnM
  exact ⟨η, hη.trans (primRootUnit_coe hζ).symm⟩

/-- **The cyclic embedding problem: the obstruction.** The class of `ζ` in the quotient
`Kˣ/N_{L/K}(Lˣ)`, i.e. the vanishing of the obstruction, is equivalent to the solvability of the
embedding problem; this is the "relative" restatement of the two halves. -/
theorem obstruction_class_eq_one_iff_norm {n : ℕ} [NeZero n] {ζ : K}
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] (hζ : IsPrimitiveRoot ζ n) :
    (QuotientGroup.mk' (normSubgroup K L) (primRootUnit hζ) : Kˣ ⧸ normSubgroup K L) = 1 ↔
      ζ ∈ Set.range fun η : Lˣ => Algebra.norm K (η : L) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_normSubgroup]
  exact ⟨fun h => h.imp fun η hη => hη.trans (primRootUnit_coe hζ),
    fun h => h.imp fun η hη => hη.trans (primRootUnit_coe hζ).symm⟩

end Work.Kummer
