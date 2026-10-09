import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- Induction principle for `H¹` of the continuous (absolute) cohomology: it suffices to check a
predicate on the classes of continuous cocycles. -/
theorem H1_induction_on {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] {C : Work.AbsoluteKummer.H1 G M → Prop}
    (x : Work.AbsoluteKummer.H1 G M)
    (h : ∀ f : Work.AbsoluteKummer.Z1 G M, C (Work.AbsoluteKummer.H1π G M f)) : C x := by
  obtain ⟨f, rfl⟩ :=
    QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 G M).comap (Work.AbsoluteKummer.Z1 G M).subtype) x
  exact h f

theorem range_mapH1_eq_ker_mapH1 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).range = (Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant).ker := by
  apply le_antisymm
  · exact S.mapH1_iota_range_le_ker_pi
  · intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    rw [AddMonoidHom.mem_range]
    revert hy
    induction y using H1_induction_on with
    | h f =>
      intro hy
      rw [Work.AbsoluteKummer.mapH1_H1π] at hy
      rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hy
      obtain ⟨p, hp⟩ := hy
      have hpval : ∀ g : G, g • p - p = S.pi ((f : G → N) g) := by
        intro g
        have h := congrFun hp g
        rw [Work.GroupCohomology.d0_apply, Work.AbsoluteKummer.mapZ1_apply] at h
        exact h
      obtain ⟨b, hb⟩ := S.pi_surjective p
      let D : Work.AbsoluteKummer.Z1 G N :=
        ⟨Work.GroupCohomology.d0 G N b,
          Work.AbsoluteKummer.mem_Z1_of (Work.GroupCohomology.d0_mem_Z1 G N b)
            (Work.AbsoluteKummer.isLocallyConstant_d0 S.isDiscreteN b)⟩
      let zB : Work.AbsoluteKummer.Z1 G N := f - D
      have hzB_val : ∀ g : G, (zB : G → N) g = (f : G → N) g - (g • b - b) := by
        intro g
        show ((f - D : Work.AbsoluteKummer.Z1 G N) : G → N) g = (f : G → N) g - (g • b - b)
        rw [AddSubgroup.coe_sub]
        rfl
      have hzB_ker : ∀ g : G, (zB : G → N) g ∈ S.pi.ker := by
        intro g
        rw [AddMonoidHom.mem_ker]
        have h1 : S.pi ((zB : G → N) g) = S.pi ((f : G → N) g) - (g • p - p) := by
          rw [hzB_val g, map_sub, map_sub, S.pi_equivariant g b, hb]
        rw [h1, hpval g, sub_self]
      have hex : ∀ g : G, ∃ m : M, S.iota m = (zB : G → N) g := by
        intro g
        have hmem : (zB : G → N) g ∈ S.iota.range := by
          rw [S.range_iota_eq_ker_pi]
          exact hzB_ker g
        exact AddMonoidHom.mem_range.mp hmem
      let fA : G → M := fun g => Classical.choose (hex g)
      have hfA : ∀ g : G, S.iota (fA g) = (zB : G → N) g :=
        fun g => Classical.choose_spec (hex g)
      have hfA_local : Work.AbsoluteKummer.IsLocallyConstant fA := by
        intro g₀
        obtain ⟨U, hU, hgU, hconst⟩ :=
          Work.AbsoluteKummer.isLocallyConstant_of_mem_Z1 zB.2 g₀
        exact ⟨U, hU, hgU, fun g hg => S.iota_injective (by rw [hfA g, hfA g₀, hconst g hg])⟩
      have hfA_cross : Work.GroupCohomology.IsCrossedHom G M fA := by
        intro g h
        apply S.iota_injective
        rw [map_add, S.iota_equivariant, hfA (g * h), hfA h, hfA g]
        exact Work.AbsoluteKummer.isCrossedHom_of_mem_Z1 zB.2 g h
      let fAZ : Work.AbsoluteKummer.Z1 G M :=
        ⟨fA, Work.AbsoluteKummer.mem_Z1_of hfA_cross hfA_local⟩
      refine ⟨Work.AbsoluteKummer.H1π G M fAZ, ?_⟩
      rw [Work.AbsoluteKummer.mapH1_H1π]
      have hzm : Work.AbsoluteKummer.mapZ1 S.iota S.iota_equivariant fAZ = zB := by
        apply Subtype.ext
        funext g
        rw [Work.AbsoluteKummer.mapZ1_apply]
        exact hfA g
      rw [hzm]
      have hDmem : ((D : Work.AbsoluteKummer.Z1 G N) : G → N) ∈ Work.AbsoluteKummer.B1 G N :=
        ⟨b, rfl⟩
      have hDz : Work.AbsoluteKummer.H1π G N D = 0 :=
        (Work.AbsoluteKummer.H1π_eq_zero_iff D).mpr hDmem
      rw [show zB = f - D from rfl, map_sub, hDz, sub_zero]

end Work.AbsoluteKummer.SES
