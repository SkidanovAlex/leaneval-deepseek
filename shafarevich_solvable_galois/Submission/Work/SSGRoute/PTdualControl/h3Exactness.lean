import Mathlib
import Submission.Work.SSGRoute.PTdualControl.mapH3
import Submission.Work.AbsoluteKummer.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness at `H³` for a short exact sequence

* `Work.SSGRoute.H3_induction_on` — the quotient-induction gadget for `H³ = Z³_c/B³_c` (the
  degree-`3` analogue of `Work.AbsoluteKummer.SES.H2_induction_on`);
* `Work.SSGRoute.PTdualControl.H3π_eq_iff`, `d2_mem_Z3`;
* `Work.AbsoluteKummer.ShortExactSeq.iotaInv_comp_mem_Z3` — transport of a `3`-cocycle supported in
  `ker π` back through `ι⁻¹`;
* `Work.AbsoluteKummer.ShortExactSeq.range_mapH3_iota_le_ker_mapH3` — the *easy* inclusion of the
  exactness at `H³(G,N)` of `H³(G,M) → H³(G,N) → H³(G,P)`.

The *reverse* inclusion (`ker_mapH3_le_range_mapH3`) and the assembly
(`range_mapH3_eq_ker_mapH3`) are **not** proved here: the mirror of the `⊇` half of
`Work.SSGRoute.range_mapH2_eq_ker_mapH2` is *not* as mechanical as it looks — the subtype coercions
of `Z³_c` and the `let`-bound coboundary correction make the elaborator time out even at
`4e6` heartbeats (the degree-`2` file needs `set_option backward.isDefEq.respectTransparency false`
and 3.2e6 heartbeats for the same steps).  Everything it needs is on disk
(`Work.GroupCohomology.mapCochain3`, `mapCochain3_d2`, `S.liftCochain2`, `mem_C2c_iff`,
`isLocallyConstant_d2`, `H3_induction_on`, `H3π_eq_iff`, `d2_mem_Z3`, `iotaInv_comp_mem_Z3`).
-/

open scoped Classical

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

variable {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
  [AddCommGroup M] [DistribMulAction G M]

/-- **Quotient induction on `H³`**: to prove a property of a class it suffices to prove it on the
classes of `3`-cocycles. -/
theorem H3_induction_on {C : Work.SSGRoute.H3 (M := M) G → Prop}
    (x : Work.SSGRoute.H3 (M := M) G)
    (h : ∀ c : Work.SSGRoute.Z3 (M := M) G, C (Work.SSGRoute.H3π (M := M) G c)) : C x := by
  obtain ⟨c, rfl⟩ :=
    QuotientAddGroup.mk'_surjective
      ((Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype) x
  exact h c

end Work.SSGRoute

namespace Work.SSGRoute.PTdualControl

variable {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
  [AddCommGroup M] [DistribMulAction G M]

/-- The `H3π` class equality is the difference being a `3`-coboundary. -/
theorem H3π_eq_iff (c c' : Work.SSGRoute.Z3 (M := M) G) :
    Work.SSGRoute.H3π (M := M) G c = Work.SSGRoute.H3π (M := M) G c'
      ↔ ((c - c' : Work.SSGRoute.Z3 (M := M) G) : G × G × G → M)
        ∈ Work.SSGRoute.B3 (M := M) G := by
  rw [Work.SSGRoute.H3π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
  rfl

/-- `d²` of a locally constant `2`-cochain is a `3`-cocycle. -/
theorem d2_mem_Z3 [IsTopologicalGroup G] (h : Work.AbsoluteKummer.IsDiscreteModule G M)
    {c : G × G → M} (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.GroupCohomology.d2 G M c ∈ Work.SSGRoute.Z3 (M := M) G := by
  rw [Work.SSGRoute.mem_Z3_iff]
  exact ⟨Work.SSGRoute.d3_d2 (G := G) (A := M) c,
    Work.SSGRoute.isLocallyConstant_d2 (G := G) (M := M) h hc⟩

end Work.SSGRoute.PTdualControl

namespace Work.AbsoluteKummer.ShortExactSeq

open Work.AbsoluteKummer

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

/-- **Exactness at `H³(G,N)` (the easy inclusion)**: the image of `H³(ι)` lies in the kernel of
`H³(π)`. -/
theorem range_mapH3_iota_le_ker_mapH3 (S : ShortExactSeq G M N P) :
    (Work.SSGRoute.PTdualControl.mapH3 (G := G) S.iota S.iota_equivariant).range ≤
      (Work.SSGRoute.PTdualControl.mapH3 (G := G) S.pi S.pi_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker]
  refine Work.SSGRoute.H3_induction_on x (C := fun y =>
    Work.SSGRoute.PTdualControl.mapH3 (G := G) S.pi S.pi_equivariant
      (Work.SSGRoute.PTdualControl.mapH3 (G := G) S.iota S.iota_equivariant y) = 0) ?_
  intro c
  rw [Work.SSGRoute.PTdualControl.mapH3_H3π (G := G) S.iota S.iota_equivariant c,
    Work.SSGRoute.PTdualControl.mapH3_H3π (G := G) S.pi S.pi_equivariant
      (Work.SSGRoute.PTdualControl.mapZ3 (G := G) S.iota S.iota_equivariant c),
    Work.SSGRoute.H3π_eq_zero_iff (M := P) G, Work.SSGRoute.mem_B3_iff (G := G) (M := P)]
  refine ⟨0, Work.AbsoluteKummer.isLocallyConstant_const 0, ?_⟩
  funext p
  simp only [map_zero, Pi.zero_apply, Work.SSGRoute.PTdualControl.mapZ3_apply, S.pi_iota]

/-- **Transporting a `3`-cocycle supported in `ker π` back through `ι⁻¹`**: if `c` is a continuous
`3`-cocycle of `N` taking all its values in `ker π = range ι`, then `p ↦ ι⁻¹ (c p)` is a continuous
`3`-cocycle of `M`. -/
theorem iotaInv_comp_mem_Z3 (S : ShortExactSeq G M N P) {c : G × G × G → N}
    (hc : c ∈ Work.SSGRoute.Z3 (M := N) G) (hker : ∀ p : G × G × G, c p ∈ S.pi.ker) :
    (fun p : G × G × G => S.iotaInv (c p)) ∈ Work.SSGRoute.Z3 (M := M) G := by
  rw [Work.SSGRoute.mem_Z3_iff]
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨g, h, k, l⟩ := p
    have hfix : (fun q : G × G × G => S.iota (S.iotaInv (c q))) = c :=
      funext fun q => S.iota_iotaInv (S.mem_range_of_mem_ker (hker q))
    have hkey := congrFun (Work.SSGRoute.d3_comp (G := G) S.iota S.iota_equivariant
      (fun q => S.iotaInv (c q))) (g, h, k, l)
    have hc0 := congrFun ((Work.SSGRoute.mem_Z3_iff (G := G) (M := N)).mp hc).1 (g, h, k, l)
    have hle : S.iota (Work.SSGRoute.d3 (G := G) (A := M)
        (fun q => S.iotaInv (c q)) (g, h, k, l)) = 0 := by
      rw [← hkey, hfix]
      simpa using hc0
    have hre : S.iota ((0 : G × G × G × G → M) (g, h, k, l)) = 0 := by
      rw [show (0 : G × G × G × G → M) (g, h, k, l) = (0 : M) from rfl, map_zero]
    exact S.iota_injective (hle.trans hre.symm)
  · exact Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv
      ((Work.SSGRoute.mem_Z3_iff (G := G) (M := N)).mp hc).2

end Work.AbsoluteKummer.ShortExactSeq

namespace Work.SSGRoute.PTdualControl

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

end Work.SSGRoute.PTdualControl
