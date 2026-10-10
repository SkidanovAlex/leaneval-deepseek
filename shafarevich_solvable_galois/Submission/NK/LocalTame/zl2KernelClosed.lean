import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.Nat.Prime.Defs
import Submission.NK.LocalTame.normalIndexPowOpen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of `G ↠ (Z/ℓ^n)²` is closed

Let `G` be a compact Hausdorff topological group, `ℓ` a prime, and suppose that every *normal*
subgroup of `G` of index `ℓ` is open.  Then for every surjection
`f : G →* (Multiplicative (ZMod (ℓ^n)) × Multiplicative (ZMod (ℓ^n)))` the kernel of `f` is
closed (indeed open, being of finite index `ℓ^{2n}`).

The mathematical content is reduced to the auxiliary lemma
`NK.LocalTame.normalIndexPowOpen`: under the hypothesis above, *every* normal subgroup of
`G` whose index is a power of `ℓ` is open.  Taking `N = ker f` (of index `ℓ^{2n}`) this gives
openness of `ker f`, and an open subgroup of finite index is closed, so that
`(ker f).topologicalClosure = ker f`.
-/

namespace NK.LocalTame

-- `hn` is part of the requested statement; the proof does not need it.
set_option linter.unusedVariables false

open Subgroup

/-- **The kernel of a surjection onto `(ZMod (ℓ^n))²` is closed.**  Hypothesis: every normal
subgroup of index a prime `ℓ` of the compact Hausdorff group `G` is open. -/
theorem zl2KernelClosed {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n)
    (hopen : ∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G))
    (f : G →* (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n))))
    (hf : Function.Surjective f) : f.ker.topologicalClosure = f.ker := by
  -- The target has cardinality `ℓ ^ (n + n)`.
  have hcard : Nat.card (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n)))
      = ℓ ^ (n + n) := by
    have h1 : Nat.card (Multiplicative (ZMod (ℓ ^ n))) = ℓ ^ n := by
      rw [(Nat.card_congr
        (Multiplicative.ofAdd : ZMod (ℓ ^ n) ≃ Multiplicative (ZMod (ℓ ^ n)))).symm,
        Nat.card_zmod]
    rw [Nat.card_prod, h1, ← pow_add]
  -- Hence `ker f` has index `ℓ ^ (2 * n)`.
  have hidx : f.ker.index = ℓ ^ (2 * n) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top, hcard]
    congr 1
    omega
  have hopenker : IsOpen (f.ker : Set G) :=
    normalIndexPowOpen hℓ hopen f.ker inferInstance (2 * n) hidx
  have hcl : IsClosed (f.ker : Set G) := Subgroup.isClosed_of_isOpen f.ker hopenker
  exact (Subgroup.topologicalClosure_minimal f.ker le_rfl hcl).antisymm
    (Subgroup.le_topologicalClosure f.ker)

end NK.LocalTame
