/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 7 (ii) without hypotheses: the `H₁`-variant of the shrinking lemma

`Work.CohomologicalShrinking.exists_shrinking_H1_of_sigma` (`Prop7.lean`) is Proposition 7 (ii) of
Schmidt–Wingberg, derived from the `k = -1` shrinking lemma plus two hypotheses: the existence of
the surjection

`σ(m) : (F(m)/F(m)²)^{⊗(j+1)} ⊗ T ↠ F(m)/F(m)² ⊗ (E(m,τ) ⊗ T)`

(universal coefficient formula + Proposition 5 + associativity of the tensor power) and its
naturality in the rank.

The module `Submission.Work.CohomologicalShrinking.prop7.exists_h1Sigma` *constructs* that `σ`
together with its naturality from `Prop5Data`, so the hypotheses can be discharged.  This file
does exactly that: it restates Proposition 7 (ii) with `Prop5Data` as the only unproved input.

## Main result

* `Work.CohomologicalShrinking.exists_shrinking_H1_of_mult` : Proposition 7 (ii) at the levels
  `r·n`, conditional only on `Prop5Data` (Proposition 5).  The form at every level `m ≥ m₀` is
  `Work.CohomologicalShrinking.exists_shrinking_H1` in `Levels.lean`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Prop7
import Submission.Work.CohomologicalShrinking.prop7.exists_h1Sigma
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

/-- **Proposition 7 (ii) of Schmidt–Wingberg**, in the model
`Ĥ^{-2}(F(m)/ν, E(m,τ) ⊗ T) = F(m)/F(m)^2 ⊗ E(m,τ) ⊗ T`.

Let `G` be a finite group, `p` a prime, `τ = (i,j)` with `j ≥ 1`, `T` a finitely generated
`𝔽_p[G]`-module, `t ∈ ℕ` and `n ≥ 1`.  Then there is `r₀` such that for all `r ≥ r₀` and all
`x₁, …, x_t` in `Ĥ^{-2}(F(r·n)/ν, E(r·n,τ) ⊗ T) = F(r·n)/F(r·n)^2 ⊗ E(r·n,τ) ⊗ T` there is a
surjective `G`-equivariant `Φ : F(r·n) → F(n)` whose induced map kills all the `x_i`.

This is `exists_shrinking_H1_of_sigma` of `Prop7.lean` with its two hypotheses `σ`, `hσnat`
discharged by `prop7.exists_h1Sigma`.  **The only unproved input is `Prop5Data` (Proposition 5).** -/
theorem exists_shrinking_H1_of_mult (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [Fintype G] {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ∀ x : Fin t → squareQuotient p G (r * n) ⊗[ZMod p] (E p G (r * n) i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G (r * n) n, ∀ k : Fin t, Φ.h1Map p G T (x k) = 0 := by
  obtain ⟨σ, hσ, hσnat⟩ := prop7.exists_h1Sigma (p := p) G D T
  exact exists_shrinking_H1_of_sigma p G hj D T σ hσ hσnat t hn

end Work.CohomologicalShrinking
