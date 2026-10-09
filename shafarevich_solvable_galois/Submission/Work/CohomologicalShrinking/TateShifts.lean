/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The shrinking lemmas over the cohomology objects of `Work.Tate` and `Work.GroupCohomology`

The paper's Proposition 6 is stated for `Ĥ^k(G, E(m,τ) ⊗ T)`.  The primary statements of this
chapter (`Levels.lean`, `Models.lean`) put the degrees `k = ±2` in the *models* of `Ĥ²` and
`Ĥ^{-2}` given by the dimension shift `Ĥ^k(G,X) ≅ Ĥ⁻¹(G, X ⊗ A_k)`, `A_k = I_G^{-(k+1)}`
(`A_{-2} = I_G = augIdeal`, `A_2 = I_G^{-3} = A2`), which is where the shrinking argument takes
place.  This file removes the last step for a consumer: it restates the same results over the
cohomology groups themselves,

* `Work.GroupCohomology.H2 G (E(m,τ) ⊗ T)` (the `k = 2` case, used in steps 1 and 3 of
  Theorem 15), and
* `Work.Tate.Hm2 G (E(m,τ) ⊗ T) = Ĥ⁻¹(G, coindUp G (E(m,τ) ⊗ T))` (the `k = -2` case, used in
  Proposition 7 and in step 4 of Theorem 15),

so that a caller can feed in classes of `Ĥ²`/`Ĥ^{-2}` directly and get a `G`-operator
homomorphism `F(m) ⇢ F(n)` whose *induced map on those groups* kills them.

Both restatements are unconditional apart from `Prop5Data` (Proposition 5): they use

* `coindUpAddEquivTensor` — the natural equivariant equivalence
  `coindUp G A ≃+ A ⊗ I_G` (the paper's `A^♯ ≅ A ⊗ I_G`),
* `coindShiftAddEquivTensor` — the natural equivariant equivalence
  `coindShift G A ≃+ A ⊗ I_G^{-1}` (the paper's `A^* ≅ A ⊗ I_G^{-1}`),
* `shiftH2Family` — the dimension shift `Ĥ²(G,X) ≅ Ĥ⁻¹(G, X ⊗ A_2)` as a natural family,
  assembled from `Work.Tate`'s connecting maps and the naturality lemmas
  `tate.dimensionShiftH2H1_natural`, `tate.dimensionShiftH1H0_natural`,
  `tate.dimensionShiftCoind_natural`.

## Main results

* `Work.CohomologicalShrinking.exists_shrinking_H2_tate` : Proposition 6, `k = 2`, for classes in
  `GroupCohomology.H2`.
* `Work.CohomologicalShrinking.exists_shrinking_Hm2_tate` : Proposition 6, `k = -2`, for classes
  in `Work.Tate.Hm2` (module `Submission.Work.CohomologicalShrinking.exists_shrinking_Hm2_tate`).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.CohomologicalShrinking.shiftH2Family
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

/-- **Proposition 6 of Schmidt–Wingberg, case `k = 2`, for classes in `GroupCohomology.H2`.**

Let `G` be a finite group, `p` a prime, `τ = (i,j)` with `j ≥ 1` and `T` a finitely generated
`𝔽_p[G]`-module.  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all
`x₁, …, x_t ∈ H²(G, E(m,τ) ⊗ T)` there is a surjective `G`-equivariant `Φ : F(m) → F(n)` whose
induced map `Φ.h2Map` on `H²` kills all the `x_i`.

This is the case used with `T = Ind_{G_p}^G 𝔽_p` in step 1 of the proof of Theorem 15 and with a
general `T` in step 3.  It is unconditional apart from `Prop5Data`. -/
theorem exists_shrinking_H2_tate (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, Φ.h2Map p G T (x k) = 0 := by
  obtain ⟨s, hs⟩ := shiftH2Family (p := p) G (i := i) (j := j) T
  haveI : Module.Finite (ZMod p) (A2 p G) := moduleFinite_A2 p G
  exact exists_shrinking_H2_of_shift (p := p) G hj D T (A2 p G) s
    (fun {m n : ℕ} (Φ : OperatorMap G m n) => (hs Φ).symm) t hn

end Work.CohomologicalShrinking
