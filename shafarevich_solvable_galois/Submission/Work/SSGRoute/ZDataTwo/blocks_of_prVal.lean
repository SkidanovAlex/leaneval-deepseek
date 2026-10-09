import Mathlib
import Submission.Work.SSGRoute.NodeS37.defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Item 3 of the `p = 2` §4 verification: the branch check of the paper's rule (condition (4))

With `ρ = 0` (`ZDataTwo/crossedValueTwoProof.lean`) and the θ-formalism of
`Submission/Work/SSGRoute/NodeS37/defs.lean` (in which the "symmetry" `val m (ginv τ) = val m τ` is
*definitional*, because `val m` is indexed by `theta m` and `theta (ginv τ) = theta τ`), the six
block equations of Schmidt–Wingberg's condition (b) for the shoebox triple `i < j < N` read:

| block | equation |
|---|---|
| `τ`-sibling of `P_i` | `val i τ + prVal val j i τ + prVal val N i τ = 0` |
| `ginv τ`-sibling of `P_i` | `val i τ + prVal val j i (ginv τ) + prVal val N i (ginv τ) = 0` |
| `τ`-sibling of `P_j` | `prVal val j i (ginv τ) + val j τ + prVal val N j τ = 0` |
| `ginv τ`-sibling of `P_j` | `prVal val j i τ + val j τ + prVal val N j (ginv τ) = 0` |
| `τ`-sibling of `P_N` | `prVal val N i (ginv τ) + prVal val N j (ginv τ) + val N τ = 0` |
| `ginv τ`-sibling of `P_N` | `prVal val N i τ + prVal val N j τ + val N τ = 0` |

where the "foreign" values (e.g. the value of the `i`-th class at a block of `P_j`) have been
replaced, via the crossed identity just proved, by the corresponding `prVal` of the *other* class at
the *other* sibling — e.g. `z_i` at the `θ(τ)`-sibling of `P_j` equals `z_j` at the `θ(ginv τ)`-sibling
of `P_i`, i.e. `prVal val j i (ginv τ)`.

The hypotheses are exactly what the shoebox and the minimality of `N` supply
(`ZDataTwo.pigeonhole_three_minimal`): the Ψ-equality `val j = val i`, `val N = val j`, and the
witness pattern `(W_{ji}, W_{Ni}, W_{Nj}) = (F, T, F)` — no `t` strictly between `i` and `j` with
`val t = val i`, `t := j` witnessing `(i,N)`, and no `t` strictly between `j` and `N` with
`val t = val j` — together with the θ-invariance of the Ψ-vector (`hθ`, definitional in the actual
construction).
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The branch check of the paper's condition (4) against the shoebox triple.** -/
theorem blocks_of_prVal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (val : ℕ → NodeS37.Gam K → ZMod 2) (i j N : ℕ) (τ : NodeS37.Gam K)
    (hiτ : ¬ NodeS37.IsInv τ)
    (hθ : ∀ m : ℕ, ∀ υ : NodeS37.Gam K, val m (NodeS37.ginv υ) = val m υ)
    (hshij : ∀ υ : NodeS37.Gam K, val j υ = val i υ)
    (hshjN : ∀ υ : NodeS37.Gam K, val N υ = val j υ)
    (hw1 : ¬ NodeS37.Witness val i j) (hw2 : NodeS37.Witness val i N)
    (hw3 : ¬ NodeS37.Witness val j N) :
    (val i τ + NodeS37.prVal val j i τ + NodeS37.prVal val N i τ = 0) ∧
    (val i τ + NodeS37.prVal val j i (NodeS37.ginv τ)
      + NodeS37.prVal val N i (NodeS37.ginv τ) = 0) ∧
    (NodeS37.prVal val j i (NodeS37.ginv τ) + val j τ + NodeS37.prVal val N j τ = 0) ∧
    (NodeS37.prVal val j i τ + val j τ + NodeS37.prVal val N j (NodeS37.ginv τ) = 0) ∧
    (NodeS37.prVal val N i (NodeS37.ginv τ) + NodeS37.prVal val N j (NodeS37.ginv τ)
      + val N τ = 0) ∧
    (NodeS37.prVal val N i τ + NodeS37.prVal val N j τ + val N τ = 0) := by
  classical
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have hgi : ¬ NodeS37.IsInv (NodeS37.ginv τ) := NodeS37.not_isInv_ginv hiτ
  rcases NodeS37.theta_eq_self_or_ginv τ with hself | hginv
  · -- the `τ`-block is a "self" block (θ τ = τ), the `ginv τ`-block a "ginv" block
    have hg : NodeS37.theta (NodeS37.ginv τ) = NodeS37.ginv (NodeS37.ginv τ) := by
      rw [NodeS37.theta_ginv, hself, NodeS37.ginv_ginv]
    simp only [NodeS37.prVal_of_self hiτ hself, NodeS37.prVal_of_ginv hgi hg,
      if_neg hw1, if_pos hw2, if_neg hw3, hθ, hshij, hshjN, htwo, add_zero, zero_add, true_and]
  · -- the `τ`-block is a "ginv" block (θ τ = ginv τ), the `ginv τ`-block a "self" block
    have hs : NodeS37.theta (NodeS37.ginv τ) = NodeS37.ginv τ := by
      rw [NodeS37.theta_ginv, hginv]
    simp only [NodeS37.prVal_of_ginv hiτ hginv, NodeS37.prVal_of_self hgi hs,
      if_neg hw1, if_pos hw2, if_neg hw3, hθ, hshij, hshjN, htwo, add_zero, zero_add, true_and]

end Work.SSGRoute.ZDataTwo
