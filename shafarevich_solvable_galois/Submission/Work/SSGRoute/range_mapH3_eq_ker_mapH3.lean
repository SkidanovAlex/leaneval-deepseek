import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.iotaInv_comp_mem_Z3
import Submission.Work.SSGRoute.range_deltaH3_eq_ker_mapH3
import Submission.Work.SSGRoute.sub_d2_liftCochain2_mem_Z3_and_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness at `H³(G,N)`: `range H³(ι) = ker H³(π)`

For a short exact sequence `0 → M →^{ι} N →^{π} P → 0` of discrete `G`-modules, the long exact
sequence in continuous cohomology

`… → H³(G,M) →^{ι_*} H³(G,N) →^{π_*} H³(G,P)`

is exact at `H³(G,N)`: the range of the coefficient functoriality `mapH3 S.iota` is the kernel of
`mapH3 S.pi`.

This is the degree-`3` analogue of `Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1` and of the
workspace's exactness at `H²(G,N)`, and mirrors the standard diagram chase for the middle term of a
long exact sequence: given a `3`-cocycle `c` of `N` with `π ∘ c = d² k` for a locally constant
`2`-cochain `k` of `P`, lift `k` to a `2`-cochain `k̃` of `N`.  Then `c - d² k̃` is again a
`3`-cocycle of `N` (because `d³ ∘ d² = 0`) whose values lie in `ker π = range ι`, so pulling it back
along `ι` gives a `3`-cocycle `c'` of `M` with `H³(ι) [c'] = [c]`.

The easy inclusion is the vanishing of the composite `H³(π) ∘ H³(ι)`; the substantive one is the
diagram chase just described.
-/

namespace Work.SSGRoute

open Work.AbsoluteKummer

/-! ## The two cochain-level inputs of the chase

Both are imported from their own files:

* `Work.SSGRoute.iotaInv_comp_mem_Z3` — the pull-back along `ι` of a `3`-cocycle with values in
  `ker π = range ι`;
* `Work.SSGRoute.sub_d2_liftCochain2_mem_Z3_and_ker` — `c - d² k̃` is again a `3`-cocycle, with
  values in `ker π`, whenever `π ∘ c = d² k` and `k̃` is a locally constant lift of `k`.-/

/-! ## The composite `H³(π) ∘ H³(ι)` vanishes -/

/-- **The composite `H³(π) ∘ H³(ι)` is zero**: on the class of a `3`-cocycle `c` of `M` it is the
class of `π ∘ ι ∘ c = 0`. -/
theorem mapH3_pi_comp_mapH3_iota_eq_zero {G : Type*} [TopologicalSpace G] [Group G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : ShortExactSeq G M N P) (x : H3 (M := M) G) :
    H3Map.mapH3 S.pi S.pi_equivariant (H3Map.mapH3 S.iota S.iota_equivariant x) = 0 := by
  refine H3_induction_on x (C := fun z => H3Map.mapH3 S.pi S.pi_equivariant
    (H3Map.mapH3 S.iota S.iota_equivariant z) = 0) ?_
  intro c
  rw [H3Map.mapH3_H3π, H3Map.mapH3_H3π, H3π_eq_zero_iff]
  have hzero : H3Map.mapZ3 S.pi S.pi_equivariant
      (H3Map.mapZ3 S.iota S.iota_equivariant c) = 0 := by
    ext p
    rw [H3Map.mapZ3_apply, H3Map.mapZ3_apply, S.pi_iota]
    rfl
  rw [hzero]
  exact (B3 (M := P) G).zero_mem

/-- **The range of `H³(ι)` lies in the kernel of `H³(π)`.** -/
theorem range_mapH3_iota_le_ker_mapH3_pi {G : Type*} [TopologicalSpace G] [Group G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : ShortExactSeq G M N P) :
    (H3Map.mapH3 S.iota S.iota_equivariant).range ≤ (H3Map.mapH3 S.pi S.pi_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (mapH3_pi_comp_mapH3_iota_eq_zero S x)

/-! ## The diagram chase: `ker H³(π) ≤ range H³(ι)` -/

/-- **Exactness at `H³(G,N)` (the substantive inclusion).**  If the class of a `3`-cocycle `c` of
`N` dies under `π_*`, say `π ∘ c = d² k` with `k` locally constant, then `c` is the class of
`ι ∘ c'` for the `3`-cocycle `c' := ι⁻¹ (c - d² k̃)` of `M`, where `k̃` is any lift of `k`. -/
theorem ker_mapH3_pi_le_range_mapH3_iota {G : Type*} [TopologicalSpace G] [Group G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [IsTopologicalGroup G] (S : ShortExactSeq G M N P) :
    (H3Map.mapH3 S.pi S.pi_equivariant).ker ≤ (H3Map.mapH3 S.iota S.iota_equivariant).range := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  revert hx
  refine H3_induction_on x (C := fun z => H3Map.mapH3 S.pi S.pi_equivariant z = 0 →
    z ∈ (H3Map.mapH3 S.iota S.iota_equivariant).range) ?_
  intro c hc
  -- `π ∘ c` is a `3`-coboundary of `P`: `π ∘ c = d² k` with `k` locally constant
  rw [H3Map.mapH3_H3π, H3π_eq_zero_iff, mem_B3_iff] at hc
  obtain ⟨k, hklc, hk⟩ := hc
  have hk' : (Work.GroupCohomology.d2 G P) k
      = fun p : G × G × G => S.pi ((c : G × G × G → N) p) := hk
  -- `c - d² k̃` is a `3`-cocycle of `N` with values in `ker π = range ι`
  obtain ⟨hc''Z3, hc''ker⟩ := sub_d2_liftCochain2_mem_Z3_and_ker S c.2 hklc hk'
  -- pull it back along `ι`
  have hc'Z3 : (fun p : G × G × G => S.iotaInv
      ((c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p))
      ∈ Z3 (M := M) G :=
    iotaInv_comp_mem_Z3 S hc''Z3 hc''ker
  refine ⟨H3π G ⟨fun p : G × G × G => S.iotaInv
    ((c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p),
    hc'Z3⟩, ?_⟩
  rw [H3Map.mapH3_H3π]
  have hmap : H3Map.mapZ3 S.iota S.iota_equivariant
      (⟨fun p : G × G × G => S.iotaInv
        ((c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p),
        hc'Z3⟩ : Z3 (M := M) G)
      = (⟨fun p : G × G × G =>
        (c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p,
        hc''Z3⟩ : Z3 (M := N) G) :=
    Subtype.ext (funext fun p => S.iota_iotaInv (S.mem_range_of_mem_ker (hc''ker p)))
  rw [hmap, H3π_eq_iff]
  have hd2B3 : (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) ∈ B3 (M := N) G :=
    (mem_B3_iff G (M := N)).mpr
      ⟨S.liftCochain2 k, S.isLocallyConstant_liftCochain2 hklc, rfl⟩
  have hcoe : (((⟨fun p : G × G × G =>
        (c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p,
        hc''Z3⟩ : Z3 (M := N) G) - c : Z3 (M := N) G) : G × G × G → N)
      = fun p : G × G × G => -((Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p) := by
    funext p
    show ((c : G × G × G → N) p - (Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p)
      - (c : G × G × G → N) p = -((Work.GroupCohomology.d2 G N) (S.liftCochain2 k) p)
    abel
  rw [hcoe]
  exact (B3 (M := N) G).neg_mem hd2B3

/-! ## Exactness at `H³(G,N)` -/

theorem range_mapH3_eq_ker_mapH3 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).range =
      (Work.SSGRoute.H3Map.mapH3 S.pi S.pi_equivariant).ker :=
  le_antisymm (range_mapH3_iota_le_ker_mapH3_pi S) (ker_mapH3_pi_le_range_mapH3_iota S)

end Work.SSGRoute
