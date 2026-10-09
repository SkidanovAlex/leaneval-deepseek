import Mathlib
import Submission.Work.HilbertSymbolGeneral.Defs
import Submission.NK.CFTLib.IdeleHasse.badSet_not_singleton
import Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# "One place of local-norm failure is no failure at all", degree two

`Work.HilbertSymbolGeneral.localNorm_not_singleton`: for a quadratic Galois extension `L / K` of
number fields and `x ∈ Kˣ`, if `x` is a local norm at every place of `K` outside a single place
`v₀`, then it is a local norm at `v₀` as well.

This is the degree-two case of Hilbert reciprocity in the "no singleton bad set" form
(Milne, *CFT*, VII.8.1(a), equivalently VIII.2 Example 2.2(ii)), and it is the form in which the
local–global Hasse principle for norms consumes the product formula
(`NK.NUV2.LC.HilbertReciprocityTwo.eq_empty_of_subset_singleton`).

The proof assembles three already-present pieces:

* `NK.CFTLib.IdeleHasse.badSet_not_singleton` — Hasse's norm theorem with one place omitted for an
  arbitrary *cyclic* extension, in the idèle form
  `P(x) ∈ N_{L/K} 𝕀_L` (this is the workspace's proved Hilbert reciprocity);
* the degree hypothesis `Nat.card (L ≃ₐ[K] L) = 2` makes `L / K` cyclic
  (`isCyclic_of_prime_card`), which is the hypothesis the crux is stated under;
* the dictionaries `NK.CFTLib.Existence.isLocalNorm_iff_exists_idele` and
  `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm` transport between the local-norm condition
  `NK.NUV2.LC.IsLocalNorm K L x v` and the idèle-norm condition used by the crux.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.HilbertSymbolGeneral

/-- **A single place of local-norm failure is no failure at all** (degree-two case of Hilbert
reciprocity): if `L / K` is a quadratic Galois extension of number fields and `x ∈ Kˣ` is a local
norm at every place `v ≠ v₀`, then `x` is a local norm at `v₀`. -/
theorem localNorm_not_singleton
    (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2)
    (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → NK.NUV2.LC.IsLocalNorm K L x v) :
    NK.NUV2.LC.IsLocalNorm K L x v₀ := by
  classical
  -- a group of prime cardinality two is cyclic
  have hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card h2
  -- translate the local-norm hypothesis into the idèle form consumed by the crux
  have hloc : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      ∃ y : NK.GlobalCFT.Idele L,
        NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v :=
    fun v hv =>
      (NK.CFTLib.Existence.isLocalNorm_iff_exists_idele (K := K) (L := L) x v).mp (h v hv)
  -- Hilbert reciprocity with one place omitted: `P(x)` is a global idèle norm
  have hmem : NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L :=
    NK.CFTLib.IdeleHasse.badSet_not_singleton (K := K) (L := L) hcyc hloc
  -- the local–global principle extracts the local condition at `v₀`
  have hloc₀ : ∃ y : NK.GlobalCFT.Idele L,
      NK.GlobalCFT.Idele.principalIdele K x v₀ = NK.GlobalCFT.Idele.normIdeleFun K L y v₀ :=
    (NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L)
      (NK.GlobalCFT.Idele.principalIdele K x)).mp hmem v₀
  -- and the dictionary closes the circle
  exact (NK.CFTLib.Existence.isLocalNorm_iff_exists_idele (K := K) (L := L) x v₀).mpr hloc₀

end Work.HilbertSymbolGeneral
