import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic periodicity lemma, in explicit cocycle form

Route C (`Submission/Work/NUV2/RouteC/kernelCondition_serre.lean`) needs, at prime-degree cyclic
local levels `M/F`, the statement that the cup product with a generator of `H²(Gal(M/F),ℤ)` has
kernel exactly the norm group.  This file isolates the *entire* mathematical content of that
statement in the cyclic case, as a computation in the low-degree cochain model
(`groupCohomology.coboundaries₂`, `groupCohomology.d₁₂`).

## The two ingredients

Let `n > 0` and `A : Rep k (ZMod n)` (`k` a commutative ring), and write `N := A.norm.hom`
(additively, `N x = Σ_{i : ZMod n} ρ_A i x`).

* `stdC n` is the **standard 2-cocycle** `c₀ (i,j) = 1` if `i.val + j.val ≥ n`, `0` otherwise;
  its class generates `H²(ℤ/n, ℤ) ≅ ℤ/n` (it is `δ` of the generator of `Hom(ℤ/n, ℚ/ℤ)`).
* `stdPrim A x` is the **explicit primitive** `b i = Σ_{k < i.val} ρ_A k x`.

The main result is that the cocycle `a ↦ (p ↦ c₀ p • a)` is a coboundary **iff** `a` lies in the
range of the norm.

## Verification of both directions (by hand, on the cochain model)

Recall `d₁₂ b (i,j) = ρ_A i (b j) - b (i+j) + b i`.

* `⟸` (`a = N x`): with `b := stdPrim A x`, for `i.val + j.val < n` the identity telescopes to
  `0 = c₀(i,j)·N x`, while for `i.val + j.val ≥ n`, putting `m := i.val + j.val - n`,
  `d₁₂ b (i,j) = Σ_{k=i}^{i+j-1} ρ k x - Σ_{k<m} ρ k x + Σ_{k<i} ρ k x
                = (N x + Σ_{k<m} ρ k x) - Σ_{k<m} ρ k x = N x = c₀(i,j)·N x`.
* `⟹`: from `c₀ · a = d₁₂ b`, first `b 0 = 0` (case `i = 0`), then summing the identities at
  `(i,1)` over all `i : ZMod n` gives `N (b 1) - Σ_i b (i+1) + Σ_i b i = Σ_i c₀(i,1)·a = a`; as
  `i ↦ i+1` is a bijection the middle terms cancel, so `a = N (b 1) ∈ range N`.

Consumers: the functoriality/boundary API (`groupCohomology.H2π`, `H2π_eq_zero_iff`,
`H2π_comp_map`, `mapCocycles₂`) turns this into
`groupCohomology.map (MonoidHom.id G) φ 2 c = 0 ↔ φ.hom.toLinearMap 1 ∈ range A.norm.hom`
for every generator `c` of `H²(G,k)`; see `cyclic_cup_eq_zero_iff` (requested separately).
-/

open scoped BigOperators

namespace NK.NUV2.RouteC

/-- The standard `2`-cocycle on the cyclic group `Multiplicative (ZMod n)`: the class of `stdC n`
generates `H²(ℤ/n, ℤ) ≅ ℤ/n`.  (Values are read through `ZMod.val`, i.e. representatives in
`{0,…,n-1}`, so the "wrap-around" is explicit.) -/
def stdC (n : ℕ) (p : Multiplicative (ZMod n) × Multiplicative (ZMod n)) : ℕ :=
  if (Multiplicative.toAdd p.1).val + (Multiplicative.toAdd p.2).val < n then 0 else 1

/-- The explicit primitive of the cocycle `p ↦ stdC n p • N x`: the cochain
`b i = Σ_{k < i.val} ρ_A k x` on the cyclic group `Multiplicative (ZMod n)`. -/
noncomputable def stdPrim {n : ℕ} (A : Rep ℤ (Multiplicative (ZMod n))) (x : A) :
    Multiplicative (ZMod n) → A :=
  fun i => ∑ k ∈ Finset.range (Multiplicative.toAdd i).val,
    A.ρ (Multiplicative.ofAdd (k : ZMod n)) x

/-! ## The two target lemmas (delegation targets; not yet proved)

**(U) the explicit primitive / upward direction**

```
theorem d₁₂_stdPrim {n : ℕ} [NeZero n] (A : Rep ℤ (Multiplicative (ZMod n))) (x : A)
    (p : Multiplicative (ZMod n) × Multiplicative (ZMod n)) :
    (groupCohomology.d₁₂ A).hom (stdPrim A x) p = (stdC n p : ℤ) • (A.norm.hom x)
```

**(K) the cyclic periodicity lemma in cocycle form** (this is the one to delegate first; (U) is the
`⟸` half of it and can be proved as a helper inside the child's file):

```
theorem stdC_smul_mem_coboundaries_iff {k : Type} [CommRing k] {n : ℕ} [NeZero n]
    (A : Rep k (Multiplicative (ZMod n))) (a : A) :
    (fun p : Multiplicative (ZMod n) × Multiplicative (ZMod n) => (stdC n p : k) • a)
        ∈ groupCohomology.coboundaries₂ A ↔
      a ∈ LinearMap.range A.norm.hom.toLinearMap
```

Both are *elementary*: see the module docstring for the two hand computations (`b := stdPrim A x`
gives `⟸`; summing the identities at `(i,1)` and using `b 0 = 0` gives `⟹`).  The abstract
formulation `NK.NUV2.RouteC.cyclic_cup_eq_zero_iff` (path `NUV2/RouteC/cyclic_cup_eq_zero_iff`,
reviewed) then follows from (K) with Mathlib's `groupCohomology.H2π`/`H2π_comp_map`/`mapCocycles₂`
API, since `stdC` represents a generator of `H²(ℤ/n, ℤ) ≅ ℤ/n` and the class map is additive.
-/

end NK.NUV2.RouteC
