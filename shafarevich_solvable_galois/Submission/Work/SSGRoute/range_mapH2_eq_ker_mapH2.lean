import Mathlib
import Submission.Work.AbsoluteKummer.SES.deltaH2_forward
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
import Submission.Work.GroupCohomology.range_mapH2_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Exactness at `H²(G,N)` (the easy inclusion)**: the image of `H²(ι)` lies in the kernel of
`H²(π)`. -/
theorem range_mapH2_iota_le_ker_mapH2_pi {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).range ≤
      (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker]
  refine Work.AbsoluteKummer.SES.H2_induction_on x (C := fun y =>
    Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant
      (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant y) = 0) ?_
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π,
    Work.AbsoluteKummer.H2π_eq_zero_iff, Work.AbsoluteKummer.mem_B2_iff]
  refine ⟨0, (Work.AbsoluteKummer.mem_C1c_iff 0).mpr
    (Work.AbsoluteKummer.isLocallyConstant_const 0), ?_⟩
  funext p
  simp only [map_zero, Pi.zero_apply, Work.AbsoluteKummer.mapZ2_apply, S.pi_iota]

/-- **Transporting a `2`-cocycle supported in `ker π` back through `ι⁻¹`**: if `c` is a
continuous `2`-cocycle of `N` taking all its values in `ker π = range ι`, then
`p ↦ ι⁻¹ (c p)` is a continuous `2`-cocycle of `M`. -/
theorem iotaInv_comp_mem_Z2 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) {c : G × G → N}
    (hc : c ∈ Work.AbsoluteKummer.Z2 G N) (hker : ∀ p : G × G, c p ∈ S.pi.ker) :
    (fun p : G × G => S.iotaInv (c p)) ∈ Work.AbsoluteKummer.Z2 G M := by
  rw [Work.AbsoluteKummer.mem_Z2_iff]
  refine ⟨?_, ?_⟩
  · intro g h k
    apply S.iota_injective
    rw [map_add, map_add, S.iota_equivariant,
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g * h, k))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g, h))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (h, k))),
      S.iota_iotaInv (S.mem_range_of_mem_ker (hker (g, h * k)))]
    exact ((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).1 g h k
  · exact Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv
      ((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).2

theorem range_mapH2_eq_ker_mapH2 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).range =
      (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).ker := by
  apply le_antisymm
  · exact range_mapH2_iota_le_ker_mapH2_pi S
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    refine (Work.AbsoluteKummer.SES.H2_induction_on x (C := fun y =>
      Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant y = 0 →
      y ∈ (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).range) ?_) hx
    intro b hb
    rw [Work.AbsoluteKummer.mapH2_H2π] at hb
    have hmem : ((Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant b :
        Work.AbsoluteKummer.Z2 G P) : G × G → P) ∈ Work.AbsoluteKummer.B2 G P :=
      (Work.AbsoluteKummer.H2π_eq_zero_iff
        (Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant b)).mp hb
    rw [Work.AbsoluteKummer.mem_B2_iff] at hmem
    obtain ⟨f, hf, hfm⟩ := hmem
    have hflc : Work.AbsoluteKummer.IsLocallyConstant f :=
      (Work.AbsoluteKummer.mem_C1c_iff f).mp hf
    have hglc : Work.AbsoluteKummer.IsLocallyConstant (S.liftCochainC f) :=
      S.isLocallyConstant_liftCochainC hflc
    have hd1glc : Work.AbsoluteKummer.IsLocallyConstant
        (Work.GroupCohomology.d1 G N (S.liftCochainC f)) :=
      Work.AbsoluteKummer.isLocallyConstant_d1 S.isDiscreteN hglc
    have hd1Z2 : Work.GroupCohomology.d1 G N (S.liftCochainC f) ∈
        Work.AbsoluteKummer.Z2 G N := by
      rw [Work.AbsoluteKummer.mem_Z2_iff]
      exact ⟨Work.GroupCohomology.d1_mem_Z2 G N (S.liftCochainC f), hd1glc⟩
    have hbk_mem : (fun p : G × G =>
        (b : G × G → N) p - Work.GroupCohomology.d1 G N (S.liftCochainC f) p) ∈
        Work.AbsoluteKummer.Z2 G N :=
      sub_mem b.2 hd1Z2
    let bk : Work.AbsoluteKummer.Z2 G N :=
      ⟨fun p : G × G =>
        (b : G × G → N) p - Work.GroupCohomology.d1 G N (S.liftCochainC f) p, hbk_mem⟩
    have hbk_ker : ∀ p : G × G, (bk : G × G → N) p ∈ S.pi.ker := by
      intro p
      rw [AddMonoidHom.mem_ker]
      have hg : Work.GroupCohomology.mapCochain1 G S.pi (S.liftCochainC f) = f := by
        funext g
        rw [Work.GroupCohomology.mapCochain1_apply]
        exact S.pi_liftCochainC f g
      have hd1 : ∀ q : G × G, S.pi (Work.GroupCohomology.d1 G N (S.liftCochainC f) q) =
          S.pi ((b : G × G → N) q) := by
        intro q
        have h := congrFun (Work.GroupCohomology.mapCochain2_d1 G S.pi S.pi_equivariant
          (S.liftCochainC f)) q
        rw [Work.GroupCohomology.mapCochain2_apply, hg, hfm,
          Work.AbsoluteKummer.mapZ2_apply] at h
        exact h
      show S.pi ((b : G × G → N) p -
        Work.GroupCohomology.d1 G N (S.liftCochainC f) p) = 0
      rw [map_sub, hd1 p, sub_self]
    let aCoch : G × G → M := fun p => S.iotaInv ((bk : G × G → N) p)
    have haCoch : ∀ p : G × G, S.iota (aCoch p) = (bk : G × G → N) p :=
      fun p => S.iota_iotaInv (S.mem_range_of_mem_ker (hbk_ker p))
    have ha_mem : aCoch ∈ Work.AbsoluteKummer.Z2 G M :=
      iotaInv_comp_mem_Z2 S bk.2 hbk_ker
    refine ⟨Work.AbsoluteKummer.H2π G M ⟨aCoch, ha_mem⟩, ?_⟩
    rw [Work.AbsoluteKummer.mapH2_H2π]
    have hmapZ : Work.AbsoluteKummer.mapZ2 S.iota S.iota_equivariant
        (⟨aCoch, ha_mem⟩ : Work.AbsoluteKummer.Z2 G M) = bk := by
      ext p
      rw [Work.AbsoluteKummer.mapZ2_apply]
      exact haCoch p
    rw [hmapZ]
    rw [Work.AbsoluteKummer.H2π_eq_iff, Work.AbsoluteKummer.mem_B2_iff]
    refine ⟨fun g : G => -S.liftCochainC f g, (Work.AbsoluteKummer.mem_C1c_iff _).mpr
      hglc.neg, ?_⟩
    funext p
    obtain ⟨p1, p2⟩ := p
    have hcoe : ((bk - b : Work.AbsoluteKummer.Z2 G N) : G × G → N) (p1, p2) =
        -Work.GroupCohomology.d1 G N (S.liftCochainC f) (p1, p2) := by
      rw [AddSubgroup.coe_sub, Pi.sub_apply]
      show ((b : G × G → N) (p1, p2) -
          Work.GroupCohomology.d1 G N (S.liftCochainC f) (p1, p2)) -
          (b : G × G → N) (p1, p2) =
        -Work.GroupCohomology.d1 G N (S.liftCochainC f) (p1, p2)
      abel
    rw [hcoe]
    show Work.GroupCohomology.d1 G N (fun g : G => -S.liftCochainC f g) (p1, p2) =
      -Work.GroupCohomology.d1 G N (S.liftCochainC f) (p1, p2)
    rw [show (fun g : G => -S.liftCochainC f g) = -S.liftCochainC f from rfl, map_neg]
    simp

end Work.SSGRoute
