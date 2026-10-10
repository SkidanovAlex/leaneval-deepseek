import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs
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
