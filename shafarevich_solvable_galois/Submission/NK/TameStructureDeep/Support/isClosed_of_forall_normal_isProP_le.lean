import Mathlib
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Support

/-!
# The maximal normal pro-`p` subgroup of a profinite group is closed

Let `G` be a compact, Hausdorff, totally disconnected topological group (a profinite group) and
let `V ≤ G` be a normal subgroup which is pro-`p` in the finite-quotient sense
`NK.LocalTame.IsProP p ↥V` and *maximal* with that property among the normal subgroups of `G`.
Then `V` is closed.

The mathematical content is one implication: **the topological closure of a pro-`p` subgroup is
again pro-`p`**.  Indeed if `H := V.topologicalClosure` and `U ≤ H` is an open normal subgroup,
then `V` (viewed inside `H`) is dense in `H`, so `V · U` is an open dense subgroup of `H`, hence
equal to `H`; consequently `H ⧸ U ≅ V ⧸ (V ∩ U)` and `[H : U] = [V : V ∩ U]` is a power of `p`.
Every open normal subgroup of the profinite group `H` therefore has `p`-power index, so `H` is
pro-`p` by `isProP_of_openNormal_index_prime`.  Maximality of `V` forces `H ≤ V`, i.e.
`V = V.topologicalClosure` is closed.

The two ingredients of the argument are recorded separately below
(`dense_subgroupOf_topologicalClosure`, `index_eq_prime_pow_of_openNormal_topologicalClosure`).
-/

/-- **The dense subgroup lemma.**  For a subgroup `V` of a topological group, `V` (viewed as the
subgroup `V.subgroupOf V.topologicalClosure` of `V.topologicalClosure`) is dense in
`V.topologicalClosure`. -/
lemma dense_subgroupOf_topologicalClosure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Subgroup G) :
    Dense ((V.subgroupOf V.topologicalClosure : Subgroup ↥(V.topologicalClosure)) :
      Set ↥(V.topologicalClosure)) := by
  have hd : DenseRange (Set.inclusion (Subgroup.le_topologicalClosure V)) :=
    (denseRange_inclusion_iff (Subgroup.le_topologicalClosure V)).mpr subset_rfl
  have hrange : Set.range (Set.inclusion (Subgroup.le_topologicalClosure V)) =
      (V.subgroupOf V.topologicalClosure : Set ↥(V.topologicalClosure)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  rwa [DenseRange, hrange] at hd

/-- **Every open normal subgroup of the closure of a pro-`p` subgroup has `p`-power index.**

Here `V ≤ G` is pro-`p` in the finite-quotient sense and `G` is a profinite group.  The proof
uses that `V` is dense in `H := V.topologicalClosure`: for an open normal `U ≤ H` the subgroup
`V · U = V ⊔ U` (with `V` viewed inside `H`) is open and dense in `H`, hence equal to `H`, so
that `[H : U] = [V : V ∩ U]`, which is a power of `p` because `V` is pro-`p`. -/
lemma index_eq_prime_pow_of_openNormal_topologicalClosure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {p : ℕ}
    {V : Subgroup G} (hVp : NK.LocalTame.IsProP p ↥V)
    (U : OpenNormalSubgroup ↥(V.topologicalClosure)) :
    ∃ k : ℕ, U.toSubgroup.index = p ^ k := by
  have hcomp : CompactSpace ↥(V.topologicalClosure) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure V).isCompact
  let S : Subgroup ↥(V.topologicalClosure) := V.subgroupOf V.topologicalClosure
  have hSpro : NK.LocalTame.IsProP p ↥S :=
    (NK.LocalTame.isProP_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_topologicalClosure V)) p).mpr hVp
  have hSdense : Dense (S : Set ↥(V.topologicalClosure)) :=
    dense_subgroupOf_topologicalClosure V
  let M : Subgroup ↥(V.topologicalClosure) := U.toSubgroup
  have hMopen : IsOpen (M : Set ↥(V.topologicalClosure)) := U.isOpen
  have hMn : M.Normal := U.isNormal'
  have hKopen :
      IsOpen ((S ⊔ M : Subgroup ↥(V.topologicalClosure)) : Set ↥(V.topologicalClosure)) :=
    Subgroup.isOpen_mono le_sup_right hMopen
  have hKdense :
      Dense ((S ⊔ M : Subgroup ↥(V.topologicalClosure)) : Set ↥(V.topologicalClosure)) :=
    hSdense.mono (fun _ hx => Subgroup.mem_sup_left hx)
  -- `S ⊔ M` is an open dense subgroup, hence everything
  have hKtop : S ⊔ M = ⊤ := by
    have hcl : ((S ⊔ M : Subgroup ↥(V.topologicalClosure)) : Set ↥(V.topologicalClosure)) =
        Set.univ := by
      rw [← (Subgroup.isClosed_of_isOpen (S ⊔ M) hKopen).closure_eq]
      exact hKdense.closure_eq
    refine le_antisymm le_top ?_
    intro x _
    exact SetLike.mem_coe.mp (by rw [hcl]; trivial)
  -- hence `[H : M] = [V : V ∩ M]`
  have hIdx : M.index = (M.subgroupOf S).index := by
    have h1 : M.relIndex (S ⊔ M) = M.relIndex S := Subgroup.relIndex_sup_right S M
    rw [hKtop, Subgroup.relIndex_top_right] at h1
    exact h1
  haveI hMfinite : Finite (↥(V.topologicalClosure) ⧸ M) :=
    Subgroup.quotient_finite_of_isOpen M hMopen
  haveI hMFI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI hNfin : (M.subgroupOf S).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [← hIdx]; exact Subgroup.FiniteIndex.index_ne_zero)
  obtain ⟨k, hk⟩ := hSpro (M.subgroupOf S) hNfin
  exact ⟨k, hIdx.trans hk⟩

theorem isClosed_of_forall_normal_isProP_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {p : ℕ}
    (hp : p.Prime) {V : Subgroup G} [V.Normal] (hVp : NK.LocalTame.IsProP p ↥V)
    (hVmax : ∀ N : Subgroup G, N.Normal → NK.LocalTame.IsProP p ↥N → N ≤ V) :
    IsClosed (V : Set G) := by
  haveI hcomp : CompactSpace ↥(V.topologicalClosure) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure V).isCompact
  -- the closure of `V` is pro-`p` (all its open normal subgroups have `p`-power index)
  have hHpro : NK.LocalTame.IsProP p ↥(V.topologicalClosure) :=
    isProP_of_openNormal_index_prime hp
      (fun U => index_eq_prime_pow_of_openNormal_topologicalClosure hVp U)
  -- maximality of `V` forces it to contain its own closure
  have hHle : V.topologicalClosure ≤ V :=
    hVmax (V.topologicalClosure) (Subgroup.is_normal_topologicalClosure V) hHpro
  have hEq : V.topologicalClosure = V :=
    le_antisymm hHle (Subgroup.le_topologicalClosure V)
  rw [← hEq]
  exact Subgroup.isClosed_topologicalClosure V

end NK.TameStructureDeep.Support
