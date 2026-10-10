import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Submission.NK.LocalTame.zl2KernelClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `NK.LocalTame.zl2QuotientTransfer`

Descent of `ℤ_ℓ²`-quotients from a compact group `G` to its topological abelianisation
`G ⧸ closure([G,G])`.

Let `G` be a compact Hausdorff topological group, `ℓ` a prime, and suppose that every normal
subgroup of `G` of index `ℓ` is open.  If for every `n ≥ 1` the group `G` admits a surjection
onto `(ℤ/ℓ^n)²`, then so does `G ⧸ closure([G,G])`.

The mathematical content is the following.  A surjection `f : G →* (ℤ/ℓ^n)²` has abelian image,
so its kernel `K = ker f` contains the commutator subgroup `[G,G]`.  If `K` were not closed then
`K` would be a proper dense subgroup of `U := closure(K)`; every subgroup of `G` of index `ℓ`
containing `K` is normal (it contains `[G,G]`) and hence open and closed, so it contains `U`.
Since `K` has index `ℓ^{2n}`, the group `G ⧸ K ≅ (ℤ/ℓ^n)²` has more than one subgroup of
index `ℓ`, which produces too many index-`ℓ` subgroups of `G` containing `K` — a contradiction.
Hence `K` is closed, so `closure([G,G]) ≤ K` and `f` factors through `G ⧸ closure([G,G])`.

The single "hard" ingredient is isolated as `NK.LocalTame.zl2KernelClosed`.
-/

namespace NK.LocalTame

/-- **Descent of `ℤ_ℓ²`-quotients to the topological abelianisation.**  If every normal subgroup
of index a prime `ℓ` is open in the compact Hausdorff group `G`, and `G` has a quotient
`(ℤ/ℓ^n)²` for every `n ≥ 1`, then `G ⧸ closure([G,G])` does too. -/
theorem zl2QuotientTransfer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hopen : ∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G))
    (h : ∀ n : ℕ, 0 < n → ∃ f : G →* (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n))),
      Function.Surjective f) :
    ∀ n : ℕ, 0 < n → ∃ f : (G ⧸ (commutator G).topologicalClosure) →*
      (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n))), Function.Surjective f := by
  intro n hn
  obtain ⟨f, hf⟩ := h n hn
  -- The kernel of `f` is closed (a surjection onto `(ℤ/ℓ^n)²` has closed kernel).
  have hker_closed : IsClosed (f.ker : Set G) :=
    (zl2KernelClosed hℓ hn hopen f hf) ▸ Subgroup.isClosed_topologicalClosure f.ker
  -- The commutator subgroup is contained in `ker f`, since the target is commutative.
  have hcom : commutator G ≤ f.ker := by
    change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ f.ker
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (f g) (f h))
  -- Hence the same holds for the closure, and `f` descends to the quotient.
  have hle : (commutator G).topologicalClosure ≤ f.ker :=
    Subgroup.topologicalClosure_minimal _ hcom hker_closed
  refine ⟨QuotientGroup.lift _ f hle, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk']⟩

end NK.LocalTame
