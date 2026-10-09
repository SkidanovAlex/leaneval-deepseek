/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The shrinking lemma at `τ = (1,1)`, with no hypothesis

The whole chapter is conditional on `Prop5Data` (Proposition 5 of Schmidt–Wingberg) — and, for
Proposition 7 (i), on the Hochschild–Serre data `SemidirectShrinkingData`.  For the first pair
`τ = (1,1)` of the induction, however, Proposition 5 is *trivially* true: the refined filtration
has `F(d)_{(1,1)}/F(d)_{(1,2)} = F(d)/F(d)^2`, so the map `θ_τ` may be taken to be the canonical
identification.  This is formalized here as `nonempty_prop5Data_one_one` (in the module of that
name), and it makes the shrinking lemmas *unconditional* for `τ = (1,1)`:

```lean
exists_shrinking_Hm1_one_one   -- Proposition 6, k = -1, τ = (1,1)
exists_shrinking_H1_one_one    -- Proposition 7 (ii), τ = (1,1)
```

This is the base case of the induction in the proof of Theorem 15 (where `τ = (1,1)` is
"nothing to show"), and it is also the check that the isolated hypothesis `Prop5Data` is not
vacuous and that the shrinking machinery does produce maps `F(m) ⇢ F(n)` out of it.

## Main results

* `Work.CohomologicalShrinking.exists_shrinking_Hm1_one_one`
* `Work.CohomologicalShrinking.exists_shrinking_H1_one_one`
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- **Proposition 6, `k = -1`, for `τ = (1,1)`** — with no unproved input.

For `G` finite, `p` prime, `N` a finitely generated `𝔽_p[G]`-module, `t ∈ ℕ` and `n ≥ 1` there
is `m₀ ≥ n` such that for all `m ≥ m₀` and all `x : Fin t → Ĥ⁻¹(G, E(m,(1,1)) ⊗ N)` there is a
surjective `G`-equivariant `Φ : F(m) → F(n)` killing all the `x`. -/
theorem exists_shrinking_Hm1_one_one (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Module.Finite (ZMod p) N]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → Work.Tate.Hm1 G (E p G m 1 1 ⊗[ZMod p] N),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, (Φ.hm1Map p G N) (x k) = 0 := by
  obtain ⟨D⟩ := nonempty_prop5Data_one_one (p := p) G
  exact exists_shrinking_Hm1 (p := p) G le_rfl D N t hn

/-- **Proposition 7 (ii) for `τ = (1,1)`** — with no unproved input.

For `G` finite, `p` prime, `T` a finitely generated `𝔽_p[G]`-module, `t ∈ ℕ` and `n ≥ 1` there
is `m₀ ≥ n` such that for all `m ≥ m₀` and all
`x : Fin t → Ĥ^{-2}(F(m)/ν, E(m,(1,1)) ⊗ T) = F(m)/F(m)^2 ⊗ E(m,(1,1)) ⊗ T` there is a surjective
`G`-equivariant `Φ : F(m) → F(n)` killing all the `x`. -/
theorem exists_shrinking_H1_one_one (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → squareQuotient p G m ⊗[ZMod p] (E p G m 1 1 ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, Φ.h1Map p G T (x k) = 0 := by
  obtain ⟨D⟩ := nonempty_prop5Data_one_one (p := p) G
  exact exists_shrinking_H1 (p := p) G le_rfl D T t hn

end Work.CohomologicalShrinking
