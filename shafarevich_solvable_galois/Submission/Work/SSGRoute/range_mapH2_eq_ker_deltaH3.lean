import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- A continuous `2`-cochain killed by `d²` is a continuous `2`-cocycle. -/
theorem mem_Z2_of_d2_eq_zero {G : Type*} [TopologicalSpace G] [Group G] {A : Type*}
    [AddCommGroup A] [DistribMulAction G A] {c : G × G → A}
    (hc : Work.GroupCohomology.d2 G A c = 0)
    (hlc : Work.AbsoluteKummer.IsLocallyConstant c) :
    c ∈ Work.AbsoluteKummer.Z2 G A := by
  rw [Work.AbsoluteKummer.Z2, AddSubgroup.mem_inf, Work.GroupCohomology.Z2_eq_ker_d2,
    AddMonoidHom.mem_ker, Work.AbsoluteKummer.mem_C2c_iff]
  exact ⟨hc, hlc⟩

/-- **The composite `δ³ ∘ H²(π)` vanishes.** -/
theorem range_mapH2_le_ker_deltaH3 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).range ≤ S.deltaH3.ker := by
  rintro y ⟨x, rfl⟩
  refine Work.AbsoluteKummer.SES.H2_induction_on x
    (C := fun z => S.deltaH3 ((Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) z) = 0) ?_
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π, S.deltaH3_H2π, Work.SSGRoute.H3π_eq_zero_iff]
  set c' : Work.AbsoluteKummer.Z2 G P := Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant c with hc'
  have hcval : ∀ p : G × G, (c' : G × G → P) p = S.pi ((c : G × G → N) p) := by
    intro p
    rw [hc', Work.AbsoluteKummer.mapZ2_apply]
  have hlcN : Work.AbsoluteKummer.IsLocallyConstant (c : G × G → N) := c.2.2
  have hlcP : Work.AbsoluteKummer.IsLocallyConstant (c' : G × G → P) := by
    rw [show (c' : G × G → P) = fun p : G × G => S.pi ((c : G × G → N) p) from funext hcval]
    exact Work.AbsoluteKummer.IsLocallyConstant.map S.pi hlcN
  have hlift : Work.AbsoluteKummer.IsLocallyConstant (S.liftCochain2 (c' : G × G → P)) :=
    S.isLocallyConstant_liftCochain2 hlcP
  have hpi : ∀ p : G × G,
      S.pi (S.liftCochain2 (c' : G × G → P) p) = S.pi ((c : G × G → N) p) := by
    intro p
    rw [S.pi_liftCochain2]
    exact hcval p
  have hcoc : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 (c' : G × G → P) p)) = 0 := by
    rw [show (fun p : G × G => S.pi (S.liftCochain2 (c' : G × G → P) p)) =
        (c' : G × G → P) from funext fun p => S.pi_liftCochain2 _ p]
    exact Work.SSGRoute.d2_eq_zero_of_mem_Z2 c'.2.1
  have hB := S.deltaCochain3_sub_mem_B3 hlift hlcN hpi hcoc
  have hzero : S.deltaCochain3 (c : G × G → N) = 0 := by
    funext p
    show S.iotaInv (Work.GroupCohomology.d2 G N (c : G × G → N) p) = 0
    rw [congrFun (Work.SSGRoute.d2_eq_zero_of_mem_Z2 c.2.1) p, Pi.zero_apply, S.iotaInv_zero]
  rw [hzero, sub_zero] at hB
  rwa [S.deltaZ3_eq_deltaCochain3 c']

/-- **Realising a class of `H²(G,P)` whose connecting class dies by a cocycle of `H²(G,N)`.**

If the connecting cocycle of `c : Z²(G,P)` is the `d²` of a continuous `2`-cochain `k` with values
in `M`, then `c` can be lifted to a continuous `2`-cocycle of `N`: the canonical lift `ñ` of `c`
is corrected by `ι ∘ k`, which kills `d²ñ`. -/
theorem exists_Z2_lift_of_deltaZ3_eq_d2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (c : Work.AbsoluteKummer.Z2 G P)
    (k : G × G → M) (hklc : Work.AbsoluteKummer.IsLocallyConstant k)
    (hk : Work.GroupCohomology.d2 G M k = (S.deltaZ3 c : G × G × G → M)) :
    ∃ c' : Work.AbsoluteKummer.Z2 G N,
      Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant c' = c := by
  have hcd2 : Work.GroupCohomology.d2 G P (c : G × G → P) = 0 :=
    Work.SSGRoute.d2_eq_zero_of_mem_Z2 c.2.1
  have hd2mem : ∀ p : G × G × G,
      Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p ∈ S.iota.range :=
    fun p => S.mem_range_of_mem_ker (by
      rw [AddMonoidHom.mem_ker]
      exact S.pi_d2_liftCochain2 hcd2 p)
  set ñ' : G × G → N := S.liftCochain2 (c : G × G → P) - fun p => S.iota (k p) with hñ'
  have h'lc : Work.AbsoluteKummer.IsLocallyConstant ñ' := by
    rw [hñ']
    exact (S.isLocallyConstant_liftCochain2 c.2.2).sub
      (Work.AbsoluteKummer.IsLocallyConstant.map S.iota hklc)
  have hd2' : Work.GroupCohomology.d2 G N ñ' = 0 := by
    funext p
    have h1 : Work.GroupCohomology.d2 G N ñ' p
        = Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p
          - Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) p := by
      simp only [hñ', Pi.sub_apply, map_sub]
    have hdel : (↑(S.deltaZ3 c) : G × G × G → M) p
        = S.iotaInv (Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p) := by
      rw [S.deltaZ3_eq_deltaCochain3 c]
      rfl
    rw [h1, congrFun (Work.SSGRoute.d2_comp S.iota S.iota_equivariant k) p, congrFun hk p,
      hdel, S.iota_iotaInv (hd2mem p)]
    simp
  have hZ : ñ' ∈ Work.AbsoluteKummer.Z2 G N := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    refine ⟨?_, h'lc⟩
    intro g h l
    have h0 : g • ñ' (h, l) - ñ' (g * h, l) + ñ' (g, h * l) - ñ' (g, h) = 0 := by
      simpa [Work.GroupCohomology.d2_apply] using congrFun hd2' (g, h, l)
    have h0' : g • ñ' (h, l) - ñ' (g * h, l) + ñ' (g, h * l) = ñ' (g, h) := sub_eq_zero.mp h0
    rw [← h0']
    abel
  refine ⟨⟨ñ', hZ⟩, ?_⟩
  apply Subtype.ext
  funext p
  rw [Work.AbsoluteKummer.mapZ2_apply]
  change S.pi (ñ' p) = (c : G × G → P) p
  rw [hñ']
  show S.pi (S.liftCochain2 (c : G × G → P) p - S.iota (k p)) = (c : G × G → P) p
  rw [map_sub, S.pi_iota, sub_zero, S.pi_liftCochain2]

/-- **Exactness at `H²(G,P)` for the `2 → 3` segment**: the kernel of the connecting map
`δ³ : H²(G,P) → H³(G,M)` is contained in the image of `H²(π)`. -/
theorem ker_deltaH3_le_range_mapH2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    S.deltaH3.ker ≤ (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).range := by
  intro x hx
  revert hx
  refine Work.AbsoluteKummer.SES.H2_induction_on x
    (C := fun z => z ∈ S.deltaH3.ker →
      z ∈ (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).range) ?_
  intro c hc
  rw [AddMonoidHom.mem_ker, S.deltaH3_H2π, Work.SSGRoute.H3π_eq_zero_iff] at hc
  rw [Work.SSGRoute.mem_B3_iff] at hc
  obtain ⟨k, hklc, hk⟩ := hc
  obtain ⟨c', hc'⟩ := Work.SSGRoute.exists_Z2_lift_of_deltaZ3_eq_d2 S c k hklc hk
  exact ⟨Work.AbsoluteKummer.H2π G N c',
    by rw [Work.AbsoluteKummer.mapH2_H2π, hc']⟩

theorem range_mapH2_eq_ker_deltaH3 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).range = S.deltaH3.ker :=
  le_antisymm (range_mapH2_le_ker_deltaH3 S) (ker_deltaH3_le_range_mapH2 S)

end Work.SSGRoute
