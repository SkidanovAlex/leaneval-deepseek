import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- **Exactness at `H¹(G,P)` (the easy inclusion)**: the image of `H¹(π)` lies in the kernel of
the connecting map `δ : H¹(G,P) → H²(G,M)`. -/
theorem range_mapH1_le_ker_deltaH2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant).range ≤ S.deltaH2.ker := by
  rintro y ⟨x, rfl⟩
  refine H1_induction_on x (C := fun y => S.deltaH2 (mapH1 S.pi S.pi_equivariant y) = 0) ?_
  intro b
  rw [mapH1_H1π, S.deltaH2_H1π, H2π_eq_zero_iff]
  set c : Z1 G P := mapZ1 S.pi S.pi_equivariant b with hc
  have hcval : ∀ g : G, (c : G → P) g = S.pi ((b : G → N) g) := by
    intro g
    rw [hc]
    exact mapZ1_apply S.pi S.pi_equivariant b g
  set n : G → N := S.liftCochainC (c : G → P) with hn
  have hnπ : ∀ g : G, S.pi (n g) = (c : G → P) g := by
    intro g; rw [hn]; exact S.pi_liftCochainC (c : G → P) g
  have hnl : IsLocallyConstant n := by
    rw [hn]; exact S.isLocallyConstant_liftCochainC (isLocallyConstant_of_mem_Z1 c.2)
  have hbl : IsLocallyConstant (b : G → N) := isLocallyConstant_of_mem_Z1 b.2
  have hker : ∀ g : G, n g - (b : G → N) g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, map_sub, hnπ g, hcval g, sub_self]
  set k : G → M := fun g => S.iotaInv (n g - (b : G → N) g) with hkdef
  have hkι : ∀ g : G, S.iota (k g) = n g - (b : G → N) g := by
    intro g; rw [hkdef]; exact S.iota_iotaInv (S.mem_range_of_mem_ker (hker g))
  have hklc : IsLocallyConstant k := by
    rw [hkdef]; exact IsLocallyConstant.map S.iotaInv (hnl.sub hbl)
  rw [mem_B2_iff]
  refine ⟨k, hklc, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have hd1 : Work.GroupCohomology.d1 G M k (g, h) =
      (S.deltaCocycleC c : G × G → M) (g, h) := by
    apply S.iota_injective
    have step1 : S.iota (Work.GroupCohomology.d1 G M k (g, h)) =
        Work.GroupCohomology.d1 G N (fun x => S.iota (k x)) (g, h) := by
      have hmap1 : Work.GroupCohomology.mapCochain1 G S.iota k = fun x => S.iota (k x) := by
        funext x; rw [Work.GroupCohomology.mapCochain1_apply]
      have hmap :=
        congrFun (Work.GroupCohomology.mapCochain2_d1 G S.iota S.iota_equivariant k) (g, h)
      rw [Work.GroupCohomology.mapCochain2_apply, hmap1] at hmap
      exact hmap
    have hnb : (fun x => S.iota (k x)) = n - (b : G → N) := by
      funext x; rw [hkι x]; rfl
    have step2 : Work.GroupCohomology.d1 G N (fun x => S.iota (k x)) (g, h) =
        Work.GroupCohomology.d1 G N n (g, h) -
          Work.GroupCohomology.d1 G N (b : G → N) (g, h) := by
      rw [hnb, map_sub, Pi.sub_apply]
    have hbz : Work.GroupCohomology.d1 G N (b : G → N) (g, h) = 0 := by
      rw [Work.GroupCohomology.d1_apply, isCrossedHom_of_mem_Z1 b.2 g h]
      abel
    have step3 : Work.GroupCohomology.d1 G N n (g, h) -
          Work.GroupCohomology.d1 G N (b : G → N) (g, h) =
        S.iota ((S.deltaCocycleC c : G × G → M) (g, h)) := by
      rw [hbz, sub_zero, hn, ← S.iota_deltaCocycleC c g h]
    calc S.iota (Work.GroupCohomology.d1 G M k (g, h))
        = Work.GroupCohomology.d1 G N (fun x => S.iota (k x)) (g, h) := step1
      _ = Work.GroupCohomology.d1 G N n (g, h) -
            Work.GroupCohomology.d1 G N (b : G → N) (g, h) := step2
      _ = S.iota ((S.deltaCocycleC c : G × G → M) (g, h)) := step3
  rw [hd1]

/-- **Exactness at `H²(G,M)` (the easy inclusion)**: the image of the connecting map
`δ : H¹(G,P) → H²(G,M)` lies in the kernel of `H²(ι)`. -/
theorem range_deltaH2_le_ker_mapH2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    S.deltaH2.range ≤ (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  refine H1_induction_on x
    (C := fun y => mapH2 S.iota S.iota_equivariant (S.deltaH2 y) = 0) ?_
  intro c
  rw [S.deltaH2_H1π, mapH2_H2π, H2π_eq_zero_iff, mem_B2_iff]
  refine ⟨S.liftCochainC (c : G → P),
    S.isLocallyConstant_liftCochainC (isLocallyConstant_of_mem_Z1 c.2), ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  rw [mapZ2_apply]
  exact (S.iota_deltaCocycleC c g h).symm

end Work.AbsoluteKummer.SES
